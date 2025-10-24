import telebot
from telebot import types
from telebot_calendar import Calendar, CallbackData, RUSSIAN_LANGUAGE
from telebot.apihelper import ApiTelegramException
import datetime
import gspread
from oauth2client.service_account import ServiceAccountCredentials
import re
import os
from dotenv import load_dotenv
import json
import time
import sys
import traceback
import pytz
from threading import Thread, Lock
import logging
import uuid
import schedule
from logging.handlers import RotatingFileHandler
import requests
# from requests.exceptions import ReadTimeout
import random
from collections import defaultdict
import backoff
import hashlib
from http.client import RemoteDisconnected

# Настройка логирования
logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)
logger.propagate = False  # Это предотвратит дублирование

console_handler = logging.StreamHandler()
console_handler.setLevel(logging.INFO)
console_formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
console_handler.setFormatter(console_formatter)

file_handler = RotatingFileHandler('bot.log', maxBytes=5 * 1024 * 1024, backupCount=3)
file_handler.setLevel(logging.DEBUG)
file_formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
file_handler.setFormatter(file_formatter)

logger.addHandler(console_handler)
logger.addHandler(file_handler)

logger.propagate = False

# Инициализация бота
load_dotenv()
BOT_TOKEN = os.getenv('BOT_TOKEN')
SPREADSHEET_ID = os.getenv('SPREADSHEET_ID')
GOOGLE_CREDS_JSON = os.getenv('GOOGLE_CREDS')
NOTIFICATION_CHAT_ID = os.getenv('NOTIFICATION_CHAT_ID')
ADMIN_USERNAMES = os.getenv('ADMINS', '').split(',')
worksheet_headers = {}

tz = pytz.timezone('Europe/Moscow')
MIN_RESERVATION_MINUTES = 30
reminder_status = {}

# Глобальные переменные для управления кэшем
safe_send_message_counter = 0

try:
    GOOGLE_CREDS = json.loads(GOOGLE_CREDS_JSON)
except Exception as e:
    logger.error(f"Ошибка загрузки JSON: {str(e)}")
    sys.exit(1)

bot = telebot.TeleBot(BOT_TOKEN)
calendar = Calendar(language=RUSSIAN_LANGUAGE)
calendar_callback = CallbackData('calendar', 'action', 'year', 'month', 'day')

# Состояния пользователя
USER_STATES = {}
STATE_TIMEOUT = 1800  # 30 минут


# Унифицированный кэш данных
class DataCache:
    def __init__(self):
        self.users = {}
        self.reservations = []
        self.carts = {}
        self.slots = {}
        # self.cart_availability = {}
        self.last_update = 0
        self.lock = Lock()
        self.expiration = 300  # 5 минут
        self.slots_ttl = 120  # 2 минуты для слотов
        self.data_hashes = {
            'users': None,
            'reservations': None,
            'carts': None
        }

    def is_expired(self):
        return time.time() - self.last_update > self.expiration

    def calculate_hash(self, data):
        """Вычисляет хеш SHA-256 для данных"""
        try:
            json_data = json.dumps(data, sort_keys=True, default=str)
            return hashlib.sha256(json_data.encode()).hexdigest()
        except Exception as e:
            logger.error(f"Ошибка вычисления хеша: {str(e)}")
            return None

    def refresh(self, force=False, partial=None):
        """Обновляет кэш с частичной поддержкой"""
        if not force and not self.is_expired():
            return False

        with self.lock:
            try:
                current_time = time.time()
                logger.info("Начало обновления кэша...")
                spreadsheet = connect_google_sheets()
                updated = False

                # Определяем, какие разделы нужно обновить
                update_users = partial is None or 'users' in partial
                update_reservations = partial is None or 'reservations' in partial
                update_carts = partial is None or 'carts' in partial

                # Обновление пользователей
                if update_users:
                    if self._update_users(spreadsheet):
                        updated = True

                # Обновление бронирований
                if update_reservations:
                    if self._update_reservations(spreadsheet):
                        updated = True

                # Обновление тележек
                if update_carts:
                    if self._update_carts(spreadsheet):
                        updated = True

                if updated:
                    self.last_update = current_time
                    # self.cart_availability = {}  # Сбрасываем кэш доступности
                    logger.info(f"Кэш обновлен за {time.time() - current_time:.2f} сек")
                return updated
            except Exception as e:
                logger.error(f"Ошибка обновления кэша: {str(e)}")
                traceback.print_exc()
                return False
            finally:
                # Всегда сбрасываем кэш слотов при обновлении бронирований
                if update_reservations:
                    self.slots = {}

    def _update_users(self, spreadsheet):
        """Обновляет только пользователей с проверкой хеша"""
        try:
            users_sheet = spreadsheet.worksheet('Пользователи')
            users_data = users_sheet.get_all_records()
            new_users = {user['Логин']: user.get('ChatID', '') for user in users_data}

            # Вычисляем хеш новых данных
            new_hash = self.calculate_hash(new_users)

            # Если хеш совпадает и данные уже есть - пропускаем обновление
            if new_hash == self.data_hashes['users'] and self.users:
                logger.debug("Хеш пользователей не изменился, пропускаем обновление")
                return False

            self.users = new_users
            self.data_hashes['users'] = new_hash
            logger.info("Данные пользователей обновлены")
            return True
        except Exception as e:
            logger.error(f"Ошибка обновления пользователей: {str(e)}")
            return False

    def _update_reservations(self, spreadsheet):
        """Обновляет только бронирования с проверкой хеша"""
        try:
            reservations_sheet = spreadsheet.worksheet('Бронирования')
            reservations_data = reservations_sheet.get_all_records()
            new_reservations = []

            for res in reservations_data:
                try:
                    if res['Статус'] in ['Отменена', 'Завершена']:
                        continue

                    if not res.get('ChatID'):
                        logger.warning(f"Бронь {res['ID']} не имеет chat_id")

                    start_time = datetime.datetime.strptime(res['Начало'], '%Y-%m-%d %H:%M')
                    start_time = tz.localize(start_time)
                    end_time = datetime.datetime.strptime(res['Конец'], '%Y-%m-%d %H:%M')
                    end_time = tz.localize(end_time)

                    actual_start = None
                    if res.get('ФактическоеНачало'):
                        actual_start = datetime.datetime.strptime(res['ФактическоеНачало'], '%Y-%m-%d %H:%M')
                        actual_start = tz.localize(actual_start)

                    actual_end = None
                    if res.get('ФактическийКонец'):
                        actual_end = datetime.datetime.strptime(res['ФактическийКонец'], '%Y-%m-%d %H:%M')
                        actual_end = tz.localize(actual_end)

                    reservation = {
                        'id': str(res['ID']),
                        'cart': res['Тележка'],
                        'start': start_time,
                        'end': end_time,
                        'actual_start': actual_start,
                        'actual_end': actual_end,
                        'username': res['Пользователь'],
                        'status': res['Статус'],
                        'photo_id': res.get('Фото', ''),
                        'chat_id': res.get('ChatID', 0)
                    }
                    new_reservations.append(reservation)
                except Exception as e:
                    logger.error(f"Ошибка обработки брони: {res} - {str(e)}")

            # Вычисляем хеш новых данных
            new_hash = self.calculate_hash(new_reservations)

            # Если хеш совпадает и данные уже есть - пропускаем обновление
            if new_hash == self.data_hashes['reservations'] and self.reservations:
                logger.debug("Хеш бронирований не изменился, пропускаем обновление")
                return False

            self.reservations = new_reservations
            self.data_hashes['reservations'] = new_hash
            logger.info(f"Данные бронирований обновлены. Активных броней: {len(new_reservations)}")
            return True
        except Exception as e:
            logger.error(f"Ошибка обновления бронирований: {str(e)}")
            return False

    def _update_carts(self, spreadsheet):
        """Обновляет только тележки с проверкой хеша"""
        try:
            carts_sheet = spreadsheet.worksheet('Тележки')
            carts_data = carts_sheet.get_all_records()
            new_carts = {}

            for cart in carts_data:
                active_status = str(cart.get('Активна', 'Да')).strip().lower()
                new_carts[cart['Название']] = {
                    'lock_code': cart['КодЗамка'],
                    'active': active_status in ['да', 'yes', '1', 'true']
                }

            # Вычисляем хеш новых данных
            new_hash = self.calculate_hash(new_carts)

            # Если хеш совпадает и данные уже есть - пропускаем обновление
            if new_hash == self.data_hashes['carts'] and self.carts:
                logger.debug("Хеш тележек не изменился, пропускаем обновление")
                return False

            self.carts = new_carts
            self.data_hashes['carts'] = new_hash
            logger.info("Данные тележек обновлены")
            return True
        except Exception as e:
            logger.error(f"Ошибка обновления тележек: {str(e)}")
            return False


# Инициализация кэша
data_cache = DataCache()

# Таймеры для проверки подтверждения броней
reservation_timers = defaultdict(list)


# Декоратор для повторных попыток при ошибках API
def retry_google_api(func):
    @backoff.on_exception(backoff.expo,
                          (gspread.exceptions.APIError, requests.exceptions.RequestException),
                          max_tries=5,
                          jitter=backoff.full_jitter,
                          giveup=lambda e: e.response.status_code not in [429, 500, 503])
    def wrapper(*args, **kwargs):
        return func(*args, **kwargs)

    return wrapper


# Декоратор для проверки личного чата
def private_chat_only(func):
    def wrapper(message):
        if message.chat.type != 'private':
            remove_keyboard = types.ReplyKeyboardRemove()
            bot.reply_to(
                message,
                "⚠️ Эта команда доступна только в личных сообщениях с @BookngCartsBot.",
                reply_markup=remove_keyboard
            )
            return
        return func(message)

    return wrapper


# Подключение к Google Sheets с повторными попытками
@retry_google_api
def connect_google_sheets():
    scope = [
        'https://www.googleapis.com/auth/spreadsheets',
        'https://www.googleapis.com/auth/drive'
    ]
    creds = ServiceAccountCredentials.from_json_keyfile_dict(GOOGLE_CREDS, scope)
    client = gspread.authorize(creds)
    return client.open_by_key(SPREADSHEET_ID)


# Улучшенная функция для обновления Google Sheets только после успешной отправки в Telegram
def update_after_successful_message(chat_id, reservation_id, updates, success_message):
    """Обновляет данные только после успешной отправки сообщения"""
    # Сначала отправляем сообщение
    if safe_send_message(chat_id, success_message, reply_markup=create_main_keyboard()):
        # После успешной отправки обновляем таблицу
        success = async_update_sheet('Бронирования', {reservation_id: updates})

        if success:
            logger.info(f"Данные брони {reservation_id} успешно обновлены в таблице и кэше")
        else:
            logger.error(f"Не удалось обновить данные брони {reservation_id} в таблице")

        return success
    else:
        logger.error(f"Не удалось отправить сообщение для брони {reservation_id}, данные не обновлены")
        return False


# Асинхронное обновление таблицы
def async_update_sheet(sheet_name, updates):
    try:
        # Проверка инициализации заголовков
        if not worksheet_headers.get(sheet_name):
            init_worksheet_headers()

        spreadsheet = connect_google_sheets()
        worksheet = spreadsheet.worksheet(sheet_name)
        all_values = worksheet.get_all_values()

        if not all_values:
            logger.error("Лист пуст")
            return False

        # Получаем заголовки
        headers = all_values[0]

        # Находим индекс столбца с ID
        id_column_index = headers.index('ID') if 'ID' in headers else 0

        # Создаем batch update запрос
        update_batch = []

        for reservation_id, column_updates in updates.items():
            # Ищем строку с нужным ID
            row_number = None
            for i, row in enumerate(all_values[1:], start=2):  # Пропускаем заголовок
                if len(row) > id_column_index and row[id_column_index] == str(reservation_id):
                    row_number = i
                    break

            if not row_number:
                logger.error(f"Строка для брони {reservation_id} не найдена")
                continue

            for col_name, value in column_updates.items():
                if col_name not in headers:
                    logger.error(f"Столбец {col_name} не найден")
                    continue

                col_index = headers.index(col_name)
                update_batch.append({
                    'range': f"{gspread.utils.rowcol_to_a1(row_number, col_index + 1)}",
                    'values': [[value]]
                })

        if update_batch:
            worksheet.batch_update(update_batch)
            logger.info(f"Успешно обновлено {len(update_batch)} ячеек в листе {sheet_name}")

            # После успешного обновления таблицы обновляем кэш
            if sheet_name == 'Бронирования':
                data_cache.refresh(partial=['reservations'])

            return True
        else:
            logger.error("Нет данных для обновления")
            return False

    except Exception as e:
        logger.error(f"Ошибка обновления таблицы: {str(e)}")
        return False


# Асинхронное добавление строки
def async_append_row(sheet_name, row_data):
    try:
        spreadsheet = connect_google_sheets()
        worksheet = spreadsheet.worksheet(sheet_name)
        worksheet.append_row(row_data)
        logger.info(f"Асинхронно добавлена строка в {sheet_name}")
    except Exception as e:
        logger.error(f"Ошибка асинхронного добавления строки: {str(e)}")


def safe_send_message(chat_id, text, reply_markup=None, parse_mode=None, max_retries=3):
    for attempt in range(max_retries):
        try:
            logger.debug(f"Попытка отправки сообщения на chat_id {chat_id}: {text[:50]}...")
            bot.send_message(
                chat_id,
                text,
                reply_markup=reply_markup,
                parse_mode=parse_mode
            )
            logger.info(f"Сообщение успешно отправлено на chat_id {chat_id}")
            return True

        except(requests.exceptions.ProxyError, RemoteDisconnected) as e:
            if attempt == max_retries - 1:
                logger.error(f"Прокси недоступен. Не удалось отправить сообщение после {max_retries} попыток")
                return False
            wait_time = (attempt + 1) * 5  # Увеличивающаяся задержка
            logger.warning(f"Ошибка прокси (попытка {attempt + 1}), ждем {wait_time} сек")
            time.sleep(wait_time)

        except(ApiTelegramException, requests.exceptions.RequestException
                # ,ConnectionError
               ) as e:
            if attempt == max_retries - 1:
                logger.error(f"Не удалось отправить сообщение после {max_retries} попыток: {str(e)}")
                return False
            logger.warning(f"Ошибка отправки (попытка {attempt+1}), повтор через 2 секунды: {str(e)}")
            time.sleep(2)
    return False

# Функция для частичного обновления кэша брони
def update_reservation_in_cache(updated_data):
    """Обновляет конкретную бронь в кэше"""
    reservation_id = str(updated_data.get('id', ''))
    if not reservation_id:
        logger.debug(f"False due to - not reservation_id")
        return False

    try:
        with data_cache.lock:
            found = False
            for i, res in enumerate(data_cache.reservations):
                logger.debug(f"res.get('id', '') {res.get('id', '')}")
                if str(res.get('id', '')) == reservation_id:
                    # Обновляем только переданные поля
                    for key, value in updated_data.items():
                        if key != 'id':  # Пропускаем поле id
                            data_cache.reservations[i][key] = value
                    logger.debug(f"Кэш брони {updated_data['id']} обновлен")
                    found = True
                    break
            if not found:
                # Если бронь не найдена в кэше
                logger.warning(f"Бронь {reservation_id} не найдена в кэше для обновления")
                return False

            # Пересчитываем хеш бронирований
            data_cache.data_hashes['reservations'] = data_cache.calculate_hash(data_cache.reservations)
            return found
    except Exception as e:
        logger.error(f"Ошибка обновления кэша: {str(e)}")
        return False


# Функция для удаления конкретной брони из кэша
def delete_reservation_in_cache(reservation_id):
    with data_cache.lock:
        data_cache.reservations = [res for res in data_cache.reservations if res.get('id') != str(reservation_id)]
        # Пересчитываем хеш бронирований
        data_cache.data_hashes['reservations'] = data_cache.calculate_hash(data_cache.reservations)
        logger.debug(f"Из кэша удалена бронь {reservation_id}")


# Инициализация кэша заголовков
def init_worksheet_headers():
    global worksheet_headers
    try:
        spreadsheet = connect_google_sheets()
        for sheet_name in ['Пользователи', 'Бронирования', 'Тележки']:
            worksheet = spreadsheet.worksheet(sheet_name)
            headers = worksheet.row_values(1)
            worksheet_headers[sheet_name] = {header: idx + 1 for idx, header in enumerate(headers)}
        logger.info("Кэш заголовков инициализирован")
    except Exception as e:
        logger.error(f"Ошибка инициализации кэша заголовков: {str(e)}")

# Получение списка всех паролей в виде строки через ", "
def get_cart_codes():
    with data_cache.lock:
        active_carts = [f"{data['lock_code']}"
                       for cart, data in data_cache.carts.items()
                       if data['active']]
        return ", ".join(active_carts) if active_carts else "нет активных тележек"


# Клавиатура основного меню
def create_main_keyboard(username=None):
    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    buttons = [
        types.KeyboardButton('Забронировать тележку'),
        types.KeyboardButton('Мои брони')
    ]
    keyboard.add(buttons[0], buttons[1])

    admin_row = [types.KeyboardButton('Обновить данные')]

    if username and username in ADMIN_USERNAMES:
        admin_row.append(types.KeyboardButton('Администрирование'))
    keyboard.add(*admin_row)
    return keyboard


# Клавиатура админского меню
def create_admin_keyboard():
    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    buttons = [
        types.KeyboardButton('Все активные брони'),
        types.KeyboardButton('Управление тележками'),
        types.KeyboardButton('Управление пользователями'),
        types.KeyboardButton('Назад')
    ]
    keyboard.add(buttons[0])
    keyboard.add(buttons[1], buttons[2])
    keyboard.add(buttons[3])
    return keyboard


# Клавиатура отмены
def create_cancel_keyboard():
    return types.ReplyKeyboardMarkup(resize_keyboard=True).add(types.KeyboardButton('Отмена'))


# Очистка устаревших состояний с исключением для подтверждения
def cleanup_states():
    current_time = time.time()

    for chat_id in list(USER_STATES.keys()):
        state = USER_STATES[chat_id]

        # Проверяем, не была ли бронь уже отменена
        if 'reservation_id' in state:
            # Проверяем статус брони напрямую в кэше
            status = None
            with data_cache.lock:
                for res in data_cache.reservations:
                    if str(res['id']) == str(state['reservation_id']):
                        status = res['status']
                        break

            if status and status in ['Отменена', 'Завершена']:
                del USER_STATES[chat_id]
                continue

        # Исключение для состояний подтверждения
        if state.get('step') in ['confirm_reservation', 'select_end_time']:
            continue

        if 'timestamp' in state and current_time - state['timestamp'] > STATE_TIMEOUT:
            logger.info(f"Очистка состояния для chat_id: {chat_id}")

            # Особые действия для состояния ожидания фото
            if state.get('step') == 'take_photo':
                reservation_id = state.get('reservation_id')
                cart = state.get('cart')
                # if reservation_id:
                #     cancel_reservation(reservation_id, "таймаут")

                try:
                    if reservation_id:
                        keyboard = types.InlineKeyboardMarkup()
                        keyboard.add(
                            types.InlineKeyboardButton('❌ Отменить', callback_data=f'cancel_{reservation_id}'),
                            types.InlineKeyboardButton('✅ Подтвердить', callback_data=f'confirm_{reservation_id}')
                        )
                        safe_send_message(
                            chat_id,
                            "❌ Время сеанса истекло. Начните сначала.",
                            reply_markup=keyboard)
                    else:
                        safe_send_message(chat_id, "❌ Время сеанса истекло. Для продолжения зайдите в 'Мои брони'")
                except Exception as e:
                    logger.error(f"Ошибка отправки сообщения: {str(e)}")
                    safe_send_message(chat_id, "❌ Время сеанса истекло. Для продолжения зайдите в 'Мои брони'")

            if chat_id in USER_STATES:
                del USER_STATES[chat_id]


# Отмена бронирования
def cancel_reservation(reservation_id, reason=""):
    try:
        if not worksheet_headers.get('Бронирования'):
            init_worksheet_headers()

        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Бронирования')
        records = sheet.get_all_records()
        reservation_id = str(reservation_id)

        for i, record in enumerate(records, start=2):
            if str(record['ID']) == reservation_id:
                if record['Статус'] in ['Отменена', 'Завершена']:
                    logger.warning(f"Бронь {reservation_id} уже отменена")
                    # Обноваление кэша конкретной брони
                    updated_res = {
                        'id': reservation_id,
                        'status': 'Отменена'
                    }
                    update_reservation_in_cache(updated_res)
                    return False

                status_col = worksheet_headers['Бронирования']['Статус']
                sheet.update_cell(i, status_col, 'Отменена')

                logger.info(f"Обноляем кэш для {reservation_id}")
                # Обноваление кэша конкретной брони
                updated_res = {
                    'id': str(reservation_id),
                    'status': 'Отменена'
                }
                update_reservation_in_cache(updated_res)

                logger.info(f"Отменяем все таймеры для {reservation_id}")
                # Отменить все таймеры для этой брони
                if reservation_id in reservation_timers:
                    for timer in reservation_timers[reservation_id]:
                        timer.cancel()
                    del reservation_timers[reservation_id]

                # Очищаем связанные напоминания
                keys_to_remove = [key for key in reminder_status if key.endswith(f"_{reservation_id}")]
                for key in keys_to_remove:
                    if key in reminder_status:
                        del reminder_status[key]

                logger.info(f"Бронь {reservation_id} отменена по причине: {reason}")
                return True
        return False
    except Exception as e:
        logger.error(f"Ошибка отмены брони: {str(e)}")
        return False


# Генерация временных слотов с учетом занятости
def generate_time_slots(date, step_minutes=15):
    with data_cache.lock:
        slots_cache_copy = data_cache.slots.copy()

    # Проверка кэша
    cache_key = f"{date.date()}_{datetime.datetime.now(tz).time().hour}"
    if cache_key in slots_cache_copy:
        cache_entry = slots_cache_copy[cache_key]
        if time.time() - cache_entry["timestamp"] < data_cache.slots_ttl:
            logger.debug(f"Используем кэшированные слоты для {date.date()}")
            return cache_entry["slots"]

    logger.info(f"Генерация слотов для {date}. Текущее время: {datetime.datetime.now(tz)}")
    time_slots = []
    current_time = datetime.datetime.now(tz)

    # Логика расчета слотов
    if date.date() < current_time.date():
        logger.debug(f"Пропускаем прошедшую дату: {date.date()}")
        with data_cache.lock:
            data_cache.slots[cache_key] = {"slots": [], "timestamp": time.time()}
        return []

    if date.date() == current_time.date():
        current_minute = current_time.minute
        remainder = current_minute % step_minutes
        rounded_minute = current_minute - remainder + step_minutes
        start_time = current_time.replace(minute=0, second=0, microsecond=0) + datetime.timedelta(
            minutes=rounded_minute)
    else:
        start_time = tz.localize(datetime.datetime.combine(date, datetime.time(0, 0)))

    end_time = tz.localize(datetime.datetime.combine(date, datetime.time(23, 45)))

    slot = start_time
    while slot <= end_time:
        slot_str = slot.strftime('%H:%M')
        slot_end = slot + datetime.timedelta(minutes=MIN_RESERVATION_MINUTES)

        # Получаем количество доступных тележек
        available_count = count_available_carts(slot, slot_end)

        if available_count > 0:
            # Добавляем слот с информацией о количестве тележек
            time_slots.append(f"{slot_str} ({available_count})")

        # available_cart = find_available_cart(slot, slot_end)
        # if available_cart:
        #     time_slots.append(slot_str)

        slot += datetime.timedelta(minutes=step_minutes)

    # Сохранение в кэш
    with data_cache.lock:
        data_cache.slots[cache_key] = {
            "slots": time_slots,
            "timestamp": time.time()
        }

    return time_slots


# Создание клавиатуры с временными слотами
def create_time_keyboard(time_slots, row_width=4):
    if not time_slots:
        return None

    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=row_width)
    buttons = [types.KeyboardButton(time) for time in time_slots]

    for i in range(0, len(buttons), row_width):
        row = buttons[i:i + row_width]
        keyboard.add(*row)

    keyboard.add(types.KeyboardButton('Отмена'))
    return keyboard


# # Поиск свободной тележки
# def find_available_cart(start_time, end_time):
#     # Принудительное обновление кэша если данные устарели
#     # data_cache.refresh()
#
#     if start_time.tzinfo is None:
#         start_time = tz.localize(start_time)
#     if end_time.tzinfo is None:
#         end_time = tz.localize(end_time)
#
#     # Создаем ключ для кэша (дата + час)
#     date_key = start_time.date()
#     hour_key = start_time.hour
#     cache_key = f"{date_key}_{hour_key}"
#
#     with data_cache.lock:
#         # Проверка кэша доступных тележек
#         if cache_key in data_cache.cart_availability:
#             return data_cache.cart_availability[cache_key]
#
#         occupied_carts = set()
#         current_reservations = data_cache.reservations.copy()
#
#         for res in current_reservations:
#             if res['status'] in ['Отменена', 'Завершена']:
#                 continue
#             if (res['start'] < end_time) and (res['end'] > start_time):
#                 occupied_carts.add(res['cart'])
#
#         available_carts = [
#             cart for cart, data in data_cache.carts.items()
#             if data['active'] and cart not in occupied_carts
#         ]
#
#         available_carts.sort(key=lambda x: int(x.split()[-1]))
#         result = available_carts[0] if available_carts else None
#
#         # Кэшируем результат
#         data_cache.cart_availability[cache_key] = result
#
#         if available_carts:
#             logger.info(f"Найдена свободная тележка: {available_carts[0]}")
#         else:
#             logger.info("Свободных тележек не найдено")
#
#         return result

# Поиск одной доступной тележки
def find_one_available_cart(start_time, end_time):
    """
    Возвращает первую доступную тележку на заданном интервале
    """
    # Получаем все активные тележки
    with data_cache.lock:
        active_carts = [cart for cart, data in data_cache.carts.items() if data['active']]

    # Перебираем тележки в порядке их названия
    for cart in sorted(active_carts):
        # Проверяем доступность конкретной тележки
        if is_cart_available(cart, start_time, end_time):
            return cart
    return None


# Функция проверки доступности конкретной тележки
def is_cart_available(cart_name, start_time, end_time):
    """
    Проверяет, доступна ли конкретная тележка на заданном интервале
    """
    with data_cache.lock:
        reservations = data_cache.reservations.copy()

    # Проверяем все бронирования для этой тележки
    for res in reservations:
        if res['cart'] != cart_name:
            continue

        if res['status'] in ['Отменена', 'Завершена']:
            continue

        # Проверяем пересечение интервалов
        if (res['start'] < end_time) and (res['end'] > start_time):
            return False

    return True


# Функция для подсчета доступных тележек на интервале
def count_available_carts(start_time, end_time):
    """
    Возвращает количество тележек, доступных на заданном интервале времени
    """
    if start_time.tzinfo is None:
        start_time = tz.localize(start_time)
    if end_time.tzinfo is None:
        end_time = tz.localize(end_time)

    with data_cache.lock:
        occupied_carts = set()
        current_reservations = data_cache.reservations.copy()
        active_carts = [cart for cart, data in data_cache.carts.items() if data['active']]

    # Если нет активных тележек
    if not active_carts:
        return 0

    # Проверяем бронирования, которые пересекаются с заданным интервалом
    for res in current_reservations:
        if res['status'] in ['Отменена', 'Завершена']:
            continue

        # Проверяем пересечение интервалов
        if (res['start'] < end_time) and (res['end'] > start_time):
            occupied_carts.add(res['cart'])

    # Доступные тележки = все активные - занятые
    available_count = len(active_carts) - len(occupied_carts)
    return max(available_count, 0)


# Генерация ID брони
def generate_reservation_id():
    return str(int(time.time() * 1000))


# Отправка уведомления в общий чат
def send_notification(message, photo_id=None):
    try:
        if NOTIFICATION_CHAT_ID:
            if photo_id:
                bot.send_photo(NOTIFICATION_CHAT_ID, photo_id, caption=message)
            else:
                safe_send_message(NOTIFICATION_CHAT_ID, message)
    except Exception as e:
        logger.error(f"Ошибка отправки уведомления: {str(e)}")


# Обработчик команды /start
@bot.message_handler(commands=['start'])
@private_chat_only
def start(message):
    try:
        # Обновляем только пользователей при старте
        data_cache.refresh(partial=['users'])
        username = message.from_user.username
        chat_id = message.chat.id
        logger.info(f'ID чата: {chat_id}')

        # Обработка активных состояний
        if chat_id in USER_STATES:
            state = USER_STATES[chat_id]

            # Отмена при ожидании фото
            if state.get('step') == 'take_photo':
                reservation_id = state.get('reservation_id')
                if reservation_id:
                    if cancel_reservation(reservation_id, "команда /start"):
                        safe_send_message(chat_id, "❌ Текущая бронь отменена.")

            # Удаление состояния
            del USER_STATES[chat_id]

        if username in data_cache.users:
            safe_send_message(chat_id, f'Привет @{username}!',
                              reply_markup=create_main_keyboard(username))

            # Обновляем ChatID пользователя
            if data_cache.users[username] != str(chat_id):
                spreadsheet = connect_google_sheets()
                users_sheet = spreadsheet.worksheet('Пользователи')

                records = users_sheet.get_all_records()
                for i, user in enumerate(records, start=2):
                    if user['Логин'] == username:
                        users_sheet.update_cell(i, 2, str(chat_id))
                        break

                # Обновляем кэш пользователей
                data_cache.refresh(partial=['users'])
        else:
            safe_send_message(chat_id, "❌ Вы не зарегистрированы в системе. Обратитесь к администратору.")

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка в /start: {error_id} - {str(e)}")
        safe_send_message(message.chat.id, f"⚠️ Произошла ошибка ({error_id}). Попробуйте позже.")


@bot.message_handler(commands=['help'])
@private_chat_only
def help(message):
    """Обработка команды помощи"""
    try:
        chat_id = message.chat.id
        username = message.from_user.username
        help_text = get_help_text(username)

        safe_send_message(chat_id, help_text, reply_markup=create_main_keyboard(username))
    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка в /help: {error_id} - {str(e)}")
        safe_send_message(message.chat.id, f"⚠️ Произошла ошибка ({error_id}). Попробуйте позже.")


# Обработчик бронирования
@bot.message_handler(func=lambda message: message.text == 'Забронировать тележку')
@private_chat_only
def start_reservation(message):
    chat_id = message.chat.id

    # Очищаем предыдущие состояния
    if chat_id in USER_STATES:
        del USER_STATES[chat_id]

    USER_STATES[chat_id] = {
        'step': 'select_date',
        'timestamp': time.time()
    }
    now = datetime.datetime.now(tz).replace(tzinfo=None)
    safe_send_message(chat_id, 'Выберите дату бронирования:',
                      reply_markup=calendar.create_calendar(
                          name=calendar_callback.prefix,
                          year=now.year,
                          month=now.month))


# Обработчик календаря
@bot.callback_query_handler(func=lambda call: call.data.startswith(calendar_callback.prefix))
def handle_calendar(call):
    try:
        chat_id = call.message.chat.id
        parts = call.data.split(calendar_callback.sep)

        if parts[1] == 'DAY':
            name, action, year, month, day = call.data.split(calendar_callback.sep)
            date = datetime.datetime(int(year), int(month), int(day))
            time_slots = generate_time_slots(date)

            if not time_slots:
                safe_send_message(chat_id, "❌ На выбранную дату нет свободных слотов. Выберите другую дату.",
                                  reply_markup=create_main_keyboard(call.from_user.username))
                return

            USER_STATES[chat_id] = {
                'step': 'select_start_time',
                'date': date,
                'timestamp': time.time()
            }
            safe_send_message(chat_id, 'Выберите время начала:',
                              reply_markup=create_time_keyboard(time_slots))
        elif parts[1] == 'CANCEL':
            if chat_id in USER_STATES:
                del USER_STATES[chat_id]

            username = call.from_user.username
            safe_send_message(
                chat_id,
                'Выбор отменен',
                reply_markup=create_main_keyboard(username)
            )
    except Exception as e:
        logger.error(f"Ошибка обработки календаря: {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка обработки календаря")


# Обработчик выбора времени начала
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'select_start_time')
@private_chat_only
def handle_start_time(message):
    chat_id = message.chat.id
    input_text = message.text.strip()

    if input_text == 'Отмена':
        safe_send_message(chat_id, 'Отмена бронирования', reply_markup=create_main_keyboard(message.from_user.username))
        if chat_id in USER_STATES:
            del USER_STATES[chat_id]
        return

    # Извлекаем только время из текста (формат "HH:MM (count)")
    time_str = input_text.split(' ')[0]

    state = USER_STATES[chat_id]
    date = state['date']

    try:
        hours, minutes = map(int, time_str.split(':'))
        start_time = tz.localize(datetime.datetime(date.year, date.month, date.day, hours, minutes))
        current_time = datetime.datetime.now(tz)

        if start_time < current_time - datetime.timedelta(minutes=5):
            safe_send_message(chat_id, '❌ Нельзя бронировать в прошлом!')
            return

        min_end_time = start_time + datetime.timedelta(minutes=MIN_RESERVATION_MINUTES)
        max_end_time = start_time + datetime.timedelta(hours=5)

        end_time_slots = []
        slot = min_end_time
        while slot <= max_end_time:
            # Проверяем доступность на всем интервале [start_time, slot]
            available_count = count_available_carts(start_time, slot)

            if available_count > 0:
                slot_str = slot.strftime('%H:%M')
                end_time_slots.append(f"{slot_str} ({available_count})")

            slot += datetime.timedelta(minutes=15)

        if not end_time_slots:
            safe_send_message(chat_id, '❌ Нет доступных слотов для окончания брони',
                              reply_markup=create_main_keyboard(message.from_user.username))
            del USER_STATES[chat_id]
            return

        USER_STATES[chat_id] = {
            'step': 'select_end_time',
            'date': date,
            'start_time': start_time,
            'timestamp': time.time()
        }
        safe_send_message(chat_id, 'Выберите время окончания:',
                          reply_markup=create_time_keyboard(end_time_slots))
    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка выбора времени: {error_id} - {str(e)}")
        safe_send_message(chat_id, f'❌ Ошибка: {str(e)}')


# Обработчик выбора времени окончания
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'select_end_time')
@private_chat_only
def handle_end_time(message):
    chat_id = message.chat.id
    username = message.from_user.username
    input_text = message.text.strip()
    state = USER_STATES[chat_id]

    try:
        logger.info(f"Обработка времени окончания для chat_id: {chat_id}, текст: {input_text}")

        if input_text == 'Отмена':
            safe_send_message(chat_id, 'Отмена бронирования',
                              reply_markup=create_main_keyboard(message.from_user.username))
            if chat_id in USER_STATES:
                del USER_STATES[chat_id]
            return

        # Извлекаем только время из текста (формат "HH:MM (count)")
        time_str = input_text.split(' ')[0]
        hours, minutes = map(int, time_str.split(':'))
        start_time = state['start_time']

        # Создаем объект времени окончания
        end_time = datetime.datetime(
            start_time.year,
            start_time.month,
            start_time.day,
            hours,
            minutes,
            tzinfo=tz
        )

        # Корректная локализация времени
        if end_time.tzinfo is None:
            end_time = tz.localize(end_time)

        # Если время окончания меньше времени начала, добавляем 1 день
        if end_time < start_time:
            end_time += datetime.timedelta(days=1)
            logger.info(f"Корректировка времени окончания +1 день: {end_time}")

        # Проверка минимального времени брони
        if (end_time - start_time) < datetime.timedelta(minutes=MIN_RESERVATION_MINUTES):
            safe_send_message(chat_id, f'❌ Минимальное время брони - {MIN_RESERVATION_MINUTES} минут!')
            return

        # Проверка доступности тележек на всем интервале
        available_count = count_available_carts(start_time, end_time)
        if available_count <= 0:
            safe_send_message(chat_id, '❌ Все тележки заняты на выбранный период!',
                              reply_markup=create_main_keyboard(message.from_user.username))
            del USER_STATES[chat_id]
            return

        # Находим конкретную свободную тележку
        cart = find_one_available_cart(start_time, end_time)

        # Генерация ID брони
        reservation_id = generate_reservation_id()

        # Обновление состояния
        USER_STATES[chat_id] = {
            'reservation_id': reservation_id,
            'end_time': end_time,
            'cart': cart,
            'step': 'confirm_reservation',
            'timestamp': time.time(),
            'date': state['date'],
            'start_time': start_time
        }

        # Получение кода замка
        # with data_cache.lock:
        #     lock_code = data_cache.carts[cart]['lock_code']
        lock_code = get_cart_codes()

        # Создание записи в Google Sheets
        new_row = [
            reservation_id,
            cart,
            start_time.strftime('%Y-%m-%d %H:%M'),
            end_time.strftime('%Y-%m-%d %H:%M'),
            "",  # ФактическоеНачало
            "",  # ФактическийКонец
            username,
            "Ожидает подтверждения",  # Статус
            "",  # Фото
            str(chat_id)
        ]
        Thread(target=async_append_row, args=('Бронирования', new_row)).start()

        # Обновление кэша
        new_reservation = {
            'id': str(reservation_id),
            'cart': cart,
            'start': start_time,
            'end': end_time,
            'actual_start': None,
            'actual_end': None,
            'username': username,
            'status': "Ожидает подтверждения",
            'photo_id': '',
            'chat_id': str(chat_id)
        }

        with data_cache.lock:
            data_cache.reservations.append(new_reservation)
            # Обновляем хеш бронирований
            data_cache.data_hashes['reservations'] = data_cache.calculate_hash(data_cache.reservations)

        # Формирование сообщения подтверждения
        confirm_text = (
            f"📋 Подтвердите бронирование:\n\n"
            f"📅 Дата: {start_time.strftime('%d.%m.%Y')}\n"
            f"⏰ Время: {start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}\n"
            f"🛒 Тележка: {cart}\n"
            f"🔒 Код замка: {lock_code}\n"
            f"🕑 В заявленное время Вы отвечаете за тележку. Вернуть тележку 🧹 чистой и без мусора."
        )

        keyboard = types.InlineKeyboardMarkup()
        keyboard.add(
            types.InlineKeyboardButton('❌ Отменить', callback_data='cancel_reservation'),
            types.InlineKeyboardButton('✅ Подтвердить', callback_data='confirm_reservation')
        )

        safe_send_message(chat_id, confirm_text, reply_markup=types.ReplyKeyboardRemove())
        safe_send_message(chat_id, "Подтвердите бронирование:", reply_markup=keyboard)
        logger.info(f"Бронирование создано для {username}: {cart} с {start_time} по {end_time}")

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка выбора времени окончания: {error_id} - {str(e)}")
        logger.error(traceback.format_exc())
        safe_send_message(chat_id, f'❌ Произошла ошибка ({error_id}). Попробуйте позже или выберите другое время.')


# Подтверждение бронирования
@bot.callback_query_handler(func=lambda call: call.data in ['confirm_reservation', 'cancel_reservation'])
def handle_confirmation(call):
    chat_id = call.message.chat.id
    username = call.from_user.username

    if chat_id not in USER_STATES:
        bot.answer_callback_query(call.id, "❌ Данные устарели")
        return

    if call.data == 'cancel_reservation':
        # Сначала пытаемся отправить сообщение об отмене
        if safe_send_message(chat_id, "❌ Бронирование отменено"):
            # Только после успешной отправки отменяем бронь
            state = USER_STATES[chat_id]
            reservation_id = state.get('reservation_id')

            if reservation_id:
                # Обновляем статус в таблице
                updates = {
                    'Статус': 'Отменена',
                    'ФактическоеНачало': datetime.datetime.now(tz).strftime('%Y-%m-%d %H:%M')
                }

                # Создаем функцию для асинхронного обновления
                def async_cancel_operation():
                    success = async_update_sheet('Бронирования', {reservation_id: updates})
                    if success:
                        logger.info(f"Бронь {reservation_id} отменена пользователем")
                        # После успешного обновления таблицы отправляем окончательное сообщение
                        safe_send_message(chat_id, "Выберите действие:", reply_markup=create_main_keyboard(username))

                        # Принудительное обновление кэша после critical действий
                        data_cache.refresh(partial=['reservations'])
                    else:
                        logger.error(f"Ошибка отмены брони {reservation_id}")
                        safe_send_message(chat_id, "❌ Ошибка при отмене брони. Попробуйте еще раз.")

                # Запускаем в отдельном потоке
                Thread(target=async_cancel_operation).start()
            else:
                logger.error("Не найден reservation_id при отмене брони")
                safe_send_message(chat_id, "❌ Ошибка при отмене брони")
        else:
            logger.error(f"Не удалось отправить сообщение об отмене для chat_id {chat_id}")
            bot.answer_callback_query(call.id, "❌ Ошибка при отправке сообщения")

        # Очищаем состояние независимо от результата
        if chat_id in USER_STATES:
            del USER_STATES[chat_id]
        return

    # Обработка подтверждения брони
    state = USER_STATES[chat_id]
    if state['step'] != 'confirm_reservation':
        bot.answer_callback_query(call.id, "❌ Неверный шаг")
        return

    try:
        # Сначала отправляем сообщение с просьбой отправить фото
        if safe_send_message(chat_id, "📸 Пожалуйста, отправьте фотографию тележки перед взятием:",
                             reply_markup=create_cancel_keyboard()):
            # Только после успешной отправки обновляем состояние для ожидания фото
            USER_STATES[chat_id] = {
                'step': 'take_photo',
                'reservation_id': state['reservation_id'],
                'cart': state['cart'],
                'start_time': state['start_time'],
                'end_time': state['end_time'],
                'timestamp': time.time()
            }

            # Обновляем статус брони в таблице после успешной отправки сообщения
            updates = {
                'Статус': 'Активна',
                'ФактическоеНачало': datetime.datetime.now(tz).strftime('%Y-%m-%d %H:%M')
            }

            # Асинхронно обновляем таблицу
            def async_confirm_operation():
                success = async_update_sheet('Бронирования', {state['reservation_id']: updates})
                if success:
                    # Обновляем кэш брони
                    updated_res = {
                        'id': state['reservation_id'],
                        'status': 'Активна',
                        'actual_start': datetime.datetime.now(tz)
                    }
                    update_reservation_in_cache(updated_res)

                    # Принудительное обновление кэша после critical действий
                    data_cache.refresh(partial=['reservations'])
                else:
                    logger.error(f"Не удалось обновить статус брони {state['reservation_id']}")
                    # Если не удалось обновить таблицу, уведомляем пользователя
                    safe_send_message(chat_id, "❌ Ошибка при подтверждении брони. Попробуйте еще раз.")
                    # Восстанавливаем предыдущее состояние
                    USER_STATES[chat_id] = state

            Thread(target=async_confirm_operation).start()
        else:
            # Если не удалось отправить сообщение, уведомляем пользователя через callback
            bot.answer_callback_query(call.id, "❌ Ошибка связи с Telegram. Попробуйте позже.")

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка бронирования: {error_id} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка бронирования")


# Обработчик фотографий при взятии тележки
@bot.message_handler(content_types=['photo'],
                     func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'take_photo')
@private_chat_only
def handle_take_photo(message):
    chat_id = message.chat.id
    state = USER_STATES[chat_id]
    username = message.from_user.username
    reservation_id = state['reservation_id']
    actual_start = datetime.datetime.now(tz)

    try:
        file_id = message.photo[-1].file_id

        # Подготавливаем обновления
        updates = {
            reservation_id: {
                'Фото': file_id,
                'ФактическоеНачало': actual_start.strftime('%Y-%m-%d %H:%M'),
                'Статус': 'Активна'
            }
        }

        # Формируем сообщение об успехе
        cart = state['cart']
        success_message = "✅ Фотография тележки сохранена! Бронирование подтверждено."

        # Обновляем после успешной отправки
        update_after_successful_message(chat_id, reservation_id, updates, success_message)

        # Отправляем уведомление в общий чат (если не получится - не критично)
        try:
            take_cart_msg = (
                f"✅ {cart} забронирована!\n\n"
                f"👤 Пользователь: @{username}\n"
                f"⏱ Фактическое время бронирования: {actual_start.strftime('%d.%m.%Y %H:%M')}\n"
                f"⏰ Плановое время возврата: {state['end_time'].strftime('%H:%M')}\n"
            )
            send_notification(take_cart_msg, file_id)
        except Exception as e:
            logger.error(f"Ошибка отправки уведомления: {str(e)}")

        # Очищаем состояние
        if chat_id in USER_STATES:
            del USER_STATES[chat_id]

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка обработки фото: {error_id} - {str(e)}")
        safe_send_message(chat_id, "❌ Ошибка обработки фото")


# Обработчик кнопки "Отмена"
@bot.message_handler(func=lambda message: message.text == 'Отмена')
@private_chat_only
def handle_general_cancel(message):
    chat_id = message.chat.id
    username = message.from_user.username

    if chat_id in USER_STATES:
        state = USER_STATES[chat_id]

        # Отмена при ожидании фото
        if state.get('step') == 'take_photo':
            reservation_id = state.get('reservation_id')
            if reservation_id:
                if cancel_reservation(reservation_id, "команда Отмена"):
                    safe_send_message(chat_id, "❌ Бронь отменена.")

        # Удаление состояния
        del USER_STATES[chat_id]

    safe_send_message(chat_id, "❌ Действие отменено",
                      reply_markup=create_main_keyboard(username))


# Обработка завершения брони
@bot.callback_query_handler(func=lambda call: call.data.startswith('return_'))
def handle_return_cart(call):
    chat_id = call.message.chat.id
    reservation_id = call.data.split('_')[1]

    try:
        with data_cache.lock:
            reservation = next((r for r in data_cache.reservations if str(r['id']) == reservation_id), None)

        if not reservation:
            bot.answer_callback_query(call.id, "❌ Бронь не найдена")
            return

        USER_STATES[chat_id] = {
            'step': 'return_photo',
            'reservation_id': reservation_id,
            'reservation_data': reservation,
            'timestamp': time.time()
        }

        safe_send_message(chat_id, "📸 Пожалуйста, отправьте фото возвращенной тележки:",
                          reply_markup=create_cancel_keyboard())

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка завершения брони: {error_id} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка")


# Обработка фотографий при возврате
@bot.message_handler(content_types=['photo'],
                     func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'return_photo')
@private_chat_only
def handle_return_photo(message):
    chat_id = message.chat.id
    state = USER_STATES[chat_id]
    reservation_id = state['reservation_id']
    reservation = state['reservation_data']
    username = message.from_user.username
    actual_end = datetime.datetime.now(tz)

    try:
        file_id = message.photo[-1].file_id

        # Асинхронное обновление таблицы
        updates = {
            reservation_id: {
                'Фото': file_id,
                'ФактическийКонец': actual_end.strftime('%Y-%m-%d %H:%M'),
                'Статус': 'Завершена'
            }
        }
        Thread(target=async_update_sheet, args=('Бронирования', updates)).start()

        # Обновление кеша конкретной брони:
        updated_res = {
            'id': str(reservation_id),
            'status': 'Завершена',
            'actual_end': actual_end
        }
        update_reservation_in_cache(updated_res)

        # Отправка уведомления
        cart = reservation['cart']
        return_msg = (
            f"✅ {cart} возвращена!\n"
            f"👤 Пользователь: @{username}\n"
            f"📅 Дата брони: {reservation['actual_start'].strftime('%d.%m.%Y')}\n"
            f"⏰ Время брони: {reservation['actual_start'].strftime('%H:%M')} - {actual_end.strftime('%H:%M')}\n"
        )
        send_notification(return_msg, file_id)

        safe_send_message(chat_id, "✅ Тележка успешно возвращена! Бронь завершена.",
                          reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка обработки фото: {error_id} - {str(e)}")
        safe_send_message(chat_id, "❌ Ошибка обработки фото")


# Обработчик кнопки "Администрирование"
@bot.message_handler(func=lambda message: message.text == 'Администрирование')
@private_chat_only
def admin_menu(message):
    chat_id = message.chat.id
    username = message.from_user.username

    if username not in ADMIN_USERNAMES:
        safe_send_message(chat_id, "❌ Доступ запрещен")
        return

    safe_send_message(chat_id, "Администрирование:",
                      reply_markup=create_admin_keyboard())


# Управление тележками
@bot.message_handler(func=lambda message: message.text == 'Управление тележками')
@private_chat_only
def manage_carts(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        safe_send_message(chat_id, "❌ Доступ запрещен")
        return

    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
    keyboard.add(
        types.KeyboardButton('Добавить тележку'),
        types.KeyboardButton('Изменить статус тележки'),
        types.KeyboardButton('Изменить пароль тележки'),
        types.KeyboardButton('Назад')
    )
    safe_send_message(chat_id, "Управление тележками:", reply_markup=keyboard)


# Обработчик кнопки "Назад"
@bot.message_handler(func=lambda message: message.text == 'Назад')
@private_chat_only
def back_to_main(message):
    chat_id = message.chat.id
    username = message.from_user.username
    safe_send_message(chat_id, "Главное меню:",
                      reply_markup=create_main_keyboard(username))


# Обработчик callback "Назад"
@bot.callback_query_handler(func=lambda call: call.data == 'back_to_list')
def back_to_list(call):
    try:
        back_to_main(call.message)
    except Exception as e:
        logger.error(f"Ошибка возврата к списку: {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка при возврате к списку")


# Добавление новой тележки (асинхронное)
@bot.message_handler(func=lambda message: message.text == 'Добавить тележку')
@private_chat_only
def add_cart(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        safe_send_message(chat_id, "❌ Доступ запрещен")
        return

    USER_STATES[chat_id] = {
        'step': 'adding_cart_name',
        'timestamp': time.time()
    }
    safe_send_message(chat_id, "Введите название новой тележки:", reply_markup=create_cancel_keyboard())


# Обработчик ввода названия тележки
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'adding_cart_name')
@private_chat_only
def handle_new_cart_name(message):
    chat_id = message.chat.id
    cart_name = message.text.strip()

    if cart_name == 'Отмена':
        safe_send_message(chat_id, "❌ Действие отменено", reply_markup=create_admin_keyboard())
        del USER_STATES[chat_id]
        return

    with data_cache.lock:
        if cart_name in data_cache.carts:
            safe_send_message(chat_id, "❌ Тележка с таким названием уже существует")
            return

    USER_STATES[chat_id] = {
        'step': 'adding_cart_password',
        'cart_name': cart_name,
        'timestamp': time.time()
    }
    safe_send_message(chat_id, f"Введите пароль (4 цифры) для тележки '{cart_name}':")


# Обработчик ввода пароля тележки
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'adding_cart_password')
@private_chat_only
def handle_new_cart_password(message):
    chat_id = message.chat.id
    password = message.text.strip()
    state = USER_STATES[chat_id]
    cart_name = state['cart_name']

    if not re.match(r'^\d{4}$', password):
        safe_send_message(chat_id, "❌ Пароль должен состоять из 4 цифр")
        return

    # Асинхронное добавление тележки
    def async_add_cart():
        try:
            spreadsheet = connect_google_sheets()
            sheet = spreadsheet.worksheet('Тележки')
            new_row = [cart_name, password, "Да"]  # Название, Пароль, Активна
            sheet.append_row(new_row)
            # Обновляем только тележки
            data_cache.refresh(partial=['carts'])
            safe_send_message(chat_id, f"✅ Тележка '{cart_name}' успешно добавлена!",
                              reply_markup=create_admin_keyboard())
        except Exception as e:
            error_id = str(uuid.uuid4())[:8]
            logger.error(f"Ошибка добавления тележки: {error_id} - {str(e)}")
            safe_send_message(chat_id, f"❌ Ошибка при добавлении тележки: {str(e)}")
        finally:
            if chat_id in USER_STATES:
                del USER_STATES[chat_id]

    Thread(target=async_add_cart).start()
    safe_send_message(chat_id, "🔄 Добавляем тележку...")


# Изменение пароля тележки
@bot.message_handler(func=lambda message: message.text == 'Изменить пароль тележки')
@private_chat_only
def change_cart_code(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        safe_send_message(chat_id, "❌ Доступ запрещен")
        return

    # Формируем список тележек
    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
    with data_cache.lock:
        for cart in data_cache.carts:
            status = "🟢" if data_cache.carts[cart]['active'] else "🔴"
            keyboard.add(types.KeyboardButton(f"{status} {cart}"))
    keyboard.add(types.KeyboardButton('Отмена'))

    USER_STATES[chat_id] = {
        'step': 'select_cart_for_password_change',
        'timestamp': time.time()
    }
    safe_send_message(chat_id, "Выберите тележку для изменения кода:", reply_markup=keyboard)


# Обработчик выбора тележки для изменения пароля
@bot.message_handler(
    func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'select_cart_for_password_change')
@private_chat_only
def handle_cart_selection_for_password_change(message):
    chat_id = message.chat.id
    cart_name = message.text[2:].strip()  # Убираем эмодзи статуса

    if message.text == 'Отмена':
        safe_send_message(chat_id, "❌ Действие отменено", reply_markup=create_admin_keyboard())
        del USER_STATES[chat_id]
        return

    with data_cache.lock:
        if cart_name not in data_cache.carts:
            safe_send_message(chat_id, "❌ Тележка не найдена")
            return

    USER_STATES[chat_id] = {
        'step': 'enter_new_cart_password',
        'cart_name': cart_name,
        'timestamp': time.time()
    }
    safe_send_message(chat_id, f"Введите новый пароль для тележки '{cart_name}':",
                      reply_markup=create_cancel_keyboard())


# Обработчик ввода нового пароля
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'enter_new_cart_password')
@private_chat_only
def handle_change_cart_password(message):
    chat_id = message.chat.id
    new_code = message.text.strip()
    state = USER_STATES[chat_id]

    if new_code == 'Отмена':
        safe_send_message(chat_id, "❌ Действие отменено", reply_markup=create_admin_keyboard())
        del USER_STATES[chat_id]
        return

    # Проверка формата кода (4 цифры)
    if not re.match(r'^\d{4}$', new_code):
        safe_send_message(chat_id, "❌ Пароль должен состоять из 4 цифр")
        return

    # Асинхронное обновление пароля
    def async_update_password():
        try:
            spreadsheet = connect_google_sheets()
            sheet = spreadsheet.worksheet('Тележки')

            # Находим строку с тележкой
            records = sheet.get_all_records()
            for i, record in enumerate(records, start=2):
                if record['Название'] == state['cart_name']:
                    sheet.update_cell(i, 2, new_code)  # Используем индекс столбца
                    break

            # Обновляем только тележки
            data_cache.refresh(partial=['carts'])
            safe_send_message(chat_id, f"✅ Пароль тележки '{state['cart_name']}' успешно изменен на {new_code}",
                              reply_markup=create_admin_keyboard())
        except Exception as e:
            error_id = str(uuid.uuid4())[:8]
            logger.error(f"Ошибка изменения пароля: {error_id} - {str(e)}")
            safe_send_message(chat_id, f"❌ Ошибка при изменении пароля: {str(e)}")
        finally:
            if chat_id in USER_STATES:
                del USER_STATES[chat_id]

    Thread(target=async_update_password).start()
    safe_send_message(chat_id, "🔄 Обновляем пароль...")


# Изменение статуса тележки
@bot.message_handler(func=lambda message: message.text == 'Изменить статус тележки')
@private_chat_only
def change_cart_status(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        safe_send_message(chat_id, "❌ Доступ запрещен")
        return

    # Формируем список тележек
    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
    with data_cache.lock:
        for cart in data_cache.carts:
            status = "🟢" if data_cache.carts[cart]['active'] else "🔴"
            keyboard.add(types.KeyboardButton(f"{status} {cart}"))
    keyboard.add(types.KeyboardButton('Отмена'))

    USER_STATES[chat_id] = {
        'step': 'select_cart_for_status_change',
        'timestamp': time.time()
    }
    safe_send_message(chat_id, "Выберите тележку для изменения статуса:", reply_markup=keyboard)


# Обработчик выбора тележки для изменения статуса
@bot.message_handler(
    func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'select_cart_for_status_change')
@private_chat_only
def handle_cart_status_change(message):
    chat_id = message.chat.id
    cart_name = message.text[2:].strip()  # Убираем эмодзи статуса

    if message.text == 'Отмена':
        safe_send_message(chat_id, "❌ Действие отменено", reply_markup=create_admin_keyboard())
        del USER_STATES[chat_id]
        return

    with data_cache.lock:
        if cart_name not in data_cache.carts:
            safe_send_message(chat_id, "❌ Тележка не найдена")
            return

    # Асинхронное изменение статуса
    def async_change_status():
        try:
            new_status = "Нет" if data_cache.carts[cart_name]['active'] else "Да"
            spreadsheet = connect_google_sheets()
            sheet = spreadsheet.worksheet('Тележки')

            # Находим строку с тележкой
            records = sheet.get_all_records()
            for i, record in enumerate(records, start=2):
                if record['Название'] == cart_name:
                    sheet.update_cell(i, 3, new_status)  # Используем индекс столбца
                    break

            # Обновляем только тележки
            data_cache.refresh(partial=['carts'])
            status_text = "активирована" if new_status == "Да" else "деактивирована"
            safe_send_message(chat_id, f"✅ Тележка '{cart_name}' успешно {status_text}!",
                              reply_markup=create_admin_keyboard())
        except Exception as e:
            error_id = str(uuid.uuid4())[:8]
            logger.error(f"Ошибка изменения статуса: {error_id} - {str(e)}")
            safe_send_message(chat_id, f"❌ Ошибка при изменении статуса: {str(e)}")
        finally:
            if chat_id in USER_STATES:
                del USER_STATES[chat_id]

    Thread(target=async_change_status).start()
    safe_send_message(chat_id, "🔄 Изменяем статус...")


# Управление пользователями
@bot.message_handler(func=lambda message: message.text == 'Управление пользователями')
@private_chat_only
def manage_users(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        safe_send_message(chat_id, "❌ Доступ запрещен")
        return

    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
    keyboard.add(
        types.KeyboardButton('Добавить пользователя'),
        types.KeyboardButton('Удалить пользователя'),
        types.KeyboardButton('Назад')
    )
    safe_send_message(chat_id, "Управление пользователями:", reply_markup=keyboard)


# Добавление пользователя (асинхронное)
@bot.message_handler(func=lambda message: message.text == 'Добавить пользователя')
@private_chat_only
def add_user(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        safe_send_message(chat_id, "❌ Доступ запрещен")
        return

    USER_STATES[chat_id] = {
        'step': 'adding_user',
        'timestamp': time.time()
    }
    safe_send_message(chat_id, "Введите логин нового пользователя (без @):",
                      reply_markup=create_cancel_keyboard())


# Обработчик добавления пользователя
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'adding_user')
@private_chat_only
def handle_add_user(message):
    chat_id = message.chat.id
    new_username = message.text.strip()

    if new_username == 'Отмена':
        safe_send_message(chat_id, "❌ Действие отменено", reply_markup=create_admin_keyboard())
        del USER_STATES[chat_id]
        return

    with data_cache.lock:
        if new_username in data_cache.users:
            safe_send_message(chat_id, "❌ Пользователь уже существует")
            return

    Thread(target=async_add_user, args=(new_username, chat_id,)).start()
    safe_send_message(chat_id, "🔄 Добавляем пользователя...")


# Асинхронное добавление пользователя
def async_add_user(new_username, chat_id):
    try:
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Пользователи')
        new_row = [new_username, ""]  # Логин, ChatID
        sheet.append_row(new_row)
        # Обновляем только пользователей
        data_cache.refresh(partial=['users'])
        if chat_id != NOTIFICATION_CHAT_ID:
            safe_send_message(chat_id, f"✅ Пользователь @{new_username} успешно добавлен!",
                              reply_markup=create_admin_keyboard())
    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка добавления пользователя: {error_id} - {str(e)}")
        safe_send_message(chat_id, f"❌ Ошибка при добавлении пользователя: {str(e)}")
    finally:
        if chat_id in USER_STATES:
            del USER_STATES[chat_id]


# Удаление пользователя (асинхронное)
@bot.message_handler(func=lambda message: message.text == 'Удалить пользователя')
@private_chat_only
def delete_user(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        safe_send_message(chat_id, "❌ Доступ запрещен")
        return

    # Формируем список пользователей
    with data_cache.lock:
        if not data_cache.users:
            safe_send_message(chat_id, "❌ Нет пользователей для удаления")
            return

        keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
        for user in data_cache.users:
            keyboard.add(types.KeyboardButton(f"👤 @{user}"))
    keyboard.add(types.KeyboardButton('Отмена'))

    USER_STATES[chat_id] = {
        'step': 'deleting_user',
        'timestamp': time.time()
    }
    safe_send_message(chat_id, "Выберите пользователя для удаления:", reply_markup=keyboard)


# Обработчик удаления пользователя
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'deleting_user')
@private_chat_only
def handle_delete_user(message):
    chat_id = message.chat.id
    username = message.text.replace('👤 @', '').strip()

    if message.text == 'Отмена':
        safe_send_message(chat_id, "❌ Действие отменено", reply_markup=create_admin_keyboard())
        del USER_STATES[chat_id]
        return

    with data_cache.lock:
        if username not in data_cache.users:
            safe_send_message(chat_id, "❌ Пользователь не найден")
            return

        # Проверка активных броней пользователя
        active_reservations = any(
            r for r in data_cache.reservations
            if r['username'] == username and r['status'] == 'Активна'
        )

    if active_reservations:
        safe_send_message(chat_id, "❌ Нельзя удалить пользователя с активными бронями")
        return

    # Асинхронное удаление пользователя
    def async_delete_user():
        try:
            spreadsheet = connect_google_sheets()
            sheet = spreadsheet.worksheet('Пользователи')

            # Находим строку пользователя
            records = sheet.get_all_records()
            for i, record in enumerate(records, start=2):
                if record['Логин'] == username:
                    sheet.delete_rows(i)
                    break

            # Обновляем только пользователей
            data_cache.refresh(partial=['users'])
            safe_send_message(chat_id, f"✅ Пользователь @{username} успешно удален!",
                              reply_markup=create_admin_keyboard())
        except Exception as e:
            error_id = str(uuid.uuid4())[:8]
            logger.error(f"Ошибка удаления пользователя: {error_id} - {str(e)}")
            safe_send_message(chat_id, f"❌ Ошибка при удалении пользователя: {str(e)}")
        finally:
            if chat_id in USER_STATES:
                del USER_STATES[chat_id]

    Thread(target=async_delete_user).start()
    safe_send_message(chat_id, "🔄 Удаляем пользователя...")


# Показать активные брони пользователя
@bot.message_handler(func=lambda message: message.text == 'Мои брони')
@private_chat_only
def handle_my_reservations(message):
    chat_id = message.chat.id
    username = message.from_user.username

    try:
        # Используем блокировку для безопасного доступа к кэшу
        with data_cache.lock:
            user_reservations = [
                r for r in data_cache.reservations
                if r['username'] == username and
                   r['status'] in ['Активна', 'Ожидает подтверждения']
            ]

        if not user_reservations:
            safe_send_message(chat_id, "У вас нет активных бронирований")
            return

        keyboard = types.InlineKeyboardMarkup()
        for res in user_reservations:
            status_icon = "🟢" if res['status'] == 'Активна' else "🟡"
            start_time = res['actual_start'] or res['start']
            btn_text = f"{status_icon} {res['cart']} {start_time.strftime('%d.%m %H:%M')}"
            callback_data = f"res_{res['id']}_{res['status']}"
            keyboard.add(types.InlineKeyboardButton(btn_text, callback_data=callback_data))

        safe_send_message(chat_id, "Ваши брони:", reply_markup=keyboard)

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка в handle_my_reservations: {error_id} - {str(e)}")


# Обработка отмены и подтверждения брони
@bot.callback_query_handler(func=lambda call: call.data.startswith('res_'))
def handle_reservation_action(call):
    try:
        chat_id = call.message.chat.id
        parts = call.data.split('_')
        if len(parts) < 3:
            bot.answer_callback_query(call.id, "❌ Ошибка формата данных")
            return

        reservation_id = parts[1]
        status = parts[2]

        with data_cache.lock:
            reservation = next((r for r in data_cache.reservations if str(r['id']) == reservation_id), None)
            # lock_code = data_cache.carts[reservation['cart']]['lock_code'] if reservation else ""
        lock_code = get_cart_codes()

        if not reservation:
            bot.answer_callback_query(call.id, "❌ Бронь не найдена")
            return

        keyboard = types.InlineKeyboardMarkup()

        if status == 'Ожидает подтверждения':
            keyboard.add(
                types.InlineKeyboardButton('❌ Отменить', callback_data=f'cancel_{reservation_id}'),
                types.InlineKeyboardButton('✅ Подтвердить', callback_data=f'confirm_{reservation_id}')
            )
        elif status == 'Активна':
            keyboard.add(
                types.InlineKeyboardButton('✅ Завершить бронь', callback_data=f'return_{reservation_id}')
            )

        keyboard.add(types.InlineKeyboardButton('↩️ Назад', callback_data='back_to_list'))

        # Форматируем информацию о брони
        start_time = reservation['actual_start'] or reservation['start']
        message_text = (
            f"🛒 Тележка: {reservation['cart']}\n"
            f"⏰ Время: {start_time.strftime('%d.%m %H:%M')} - {reservation['end'].strftime('%H:%M')}\n"
            f"🔒 Код замка: {lock_code}\n"
            f"📊 Статус: {reservation['status']}"
        )

        bot.edit_message_text(
            message_text,
            chat_id,
            call.message.message_id,
            reply_markup=keyboard
        )
    except Exception as e:
        logger.error(f"Ошибка в callback: {call.data} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка обработки")


# Обработка отмены брони
@bot.callback_query_handler(func=lambda call: call.data.startswith('cancel_'))
def handle_cancel_reservation(call):
    chat_id = call.message.chat.id
    reservation_id = call.data.split('_')[1]

    try:
        # Находим бронирование
        with data_cache.lock:
            reservation = next((r for r in data_cache.reservations if str(r['id']) == reservation_id), None)

        if not reservation:
            bot.answer_callback_query(call.id, "❌ Бронь не найдена")
            return

        if reservation['status'] != 'Ожидает подтверждения':
            bot.answer_callback_query(call.id, "❌ Бронь не находится в статусе 'Ожидает подтверждения'")
            return

        # Асинхронная отмена брони
        def async_cancel_reservation():
            if cancel_reservation(reservation_id, "отменено пользователем"):
                start_str = reservation['start'].strftime('%d.%m %H:%M')
                end_str = reservation['end'].strftime('%H:%M')
                cart_name = reservation['cart']

                success_msg = f"✅ Бронь {cart_name} на {start_str}-{end_str} отменена"
                bot.edit_message_text(success_msg, chat_id, call.message.message_id)

        Thread(target=async_cancel_reservation).start()
        bot.answer_callback_query(call.id, "Отменяем бронь...")
    except requests.exceptions.ProxyError as e:
        logger.error(f"Ошибка прокси при обработке callback: {str(e)}")
        try:
            bot.answer_callback_query(call.id, "⚠️ Временная ошибка сети")
        except:
            pass
    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка отмены брони: {error_id} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка отмены брони")


# Все активные брони (админ)
@bot.message_handler(func=lambda message: message.text == 'Все активные брони')
@private_chat_only
def show_all_active(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        safe_send_message(chat_id, "❌ Доступ запрещен")
        return

    # Фильтруем брони по статусу
    with data_cache.lock:
        active_reservations = [r for r in data_cache.reservations if r['status'] == 'Активна']
        pending_reservations = [r for r in data_cache.reservations if r['status'] == 'Ожидает подтверждения']

    if not active_reservations and not pending_reservations:
        safe_send_message(chat_id, "Нет активных или ожидающих бронирований")
        return

    keyboard = types.InlineKeyboardMarkup()

    # Активные брони
    if active_reservations:
        safe_send_message(chat_id, "✅ Активные брони:")
        for res in active_reservations:
            text = (
                f"{res['cart']} - @{res['username']} - "
                f"{res['start'].strftime('%d.%m %H:%M')} → "
                f"{res['end'].strftime('%H:%M')}"
            )
            callback_data = f"admin_action_{res['id']}"
            keyboard.add(types.InlineKeyboardButton(text, callback_data=callback_data))

    # Ожидающие брони
    if pending_reservations:
        safe_send_message(chat_id, "🕒 Ожидающие подтверждения:")
        for res in pending_reservations:
            text = (
                f"{res['cart']} - @{res['username']} - "
                f"{res['start'].strftime('%d.%m %H:%M')} → "
                f"{res['end'].strftime('%H:%M')}"
            )
            callback_data = f"admin_action_{res['id']}"
            keyboard.add(types.InlineKeyboardButton(text, callback_data=callback_data))

    safe_send_message(chat_id, "Выберите бронь для управления:", reply_markup=keyboard)


# Обработчик действий администратора над бронями
@bot.callback_query_handler(func=lambda call: call.data.startswith('admin_action_'))
def handle_admin_reservation_action(call):
    chat_id = call.message.chat.id
    reservation_id = call.data.split('_')[2]

    try:
        with data_cache.lock:
            reservation = next((r for r in data_cache.reservations if str(r['id']) == reservation_id), None)
        if not reservation:
            bot.answer_callback_query(call.id, "❌ Бронь не найдена")
            return

        # Создаем клавиатуру действий
        keyboard = types.InlineKeyboardMarkup()

        if reservation['status'] == 'Активна':
            keyboard.add(
                types.InlineKeyboardButton('✅ Завершить бронь', callback_data=f'admin_complete_{reservation_id}'),
                types.InlineKeyboardButton('❌ Отменить бронь', callback_data=f'admin_cancel_{reservation_id}')
            )
        elif reservation['status'] == 'Ожидает подтверждения':
            keyboard.add(
                types.InlineKeyboardButton('❌ Отменить бронь', callback_data=f'admin_cancel_{reservation_id}')
            )

        bot.edit_message_text(
            f"Управление бронированием:\n\n"
            f"🛒 Тележка: {reservation['cart']}\n"
            f"👤 Пользователь: @{reservation['username']}\n"
            f"⏰ Время: {reservation['start'].strftime('%d.%m %H:%M')} → {reservation['end'].strftime('%H:%M')}\n"
            f"📊 Статус: {reservation['status']}",
            chat_id,
            call.message.message_id,
            reply_markup=keyboard
        )

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка управления бронированием: {error_id} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка")


# Обработчик завершения брони администратором
@bot.callback_query_handler(func=lambda call: call.data.startswith('admin_complete_'))
def handle_admin_complete(call):
    chat_id = call.message.chat.id
    reservation_id = call.data.split('_')[2]
    actual_end = datetime.datetime.now(tz)

    try:
        with data_cache.lock:
            reservation = next((r for r in data_cache.reservations if str(r['id']) == reservation_id), None)
        if not reservation:
            bot.answer_callback_query(call.id, "❌ Бронь не найдена")
            return

        # Асинхронное завершение брони
        def async_complete_reservation():
            try:
                # Асинхронное обновление таблицы
                updates = {
                    reservation_id: {
                        'ФактическийКонец': actual_end.strftime('%Y-%m-%d %H:%M'),
                        'Статус': 'Завершена'
                    }
                }
                Thread(target=async_update_sheet, args=('Бронирования', updates)).start()

                # Обновление кеша конкретной брони:
                updated_res = {
                    'id': str(reservation_id),
                    'status': 'Завершена',
                    'actual_end': actual_end
                }
                update_reservation_in_cache(updated_res)

                # Уведомление пользователя
                user_msg = f"✅ Ваша бронь тележки {reservation['cart']} завершена администратором."
                safe_send_message(reservation['chat_id'], user_msg, reply_markup=create_main_keyboard())

                bot.edit_message_text(
                    f"✅ Бронь тележки {reservation['cart']} успешно завершена!",
                    chat_id,
                    call.message.message_id
                )
            except Exception as e:
                error_id = str(uuid.uuid4())[:8]
                logger.error(f"Ошибка завершения брони: {error_id} - {str(e)}")
                bot.answer_callback_query(call.id, "❌ Ошибка завершения")

        Thread(target=async_complete_reservation).start()
        bot.answer_callback_query(call.id, "Завершаем бронь...")

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка завершения брони: {error_id} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка")


# Обработчик отмены брони администратором
@bot.callback_query_handler(func=lambda call: call.data.startswith('admin_cancel_'))
def handle_admin_cancel(call):
    chat_id = call.message.chat.id
    reservation_id = call.data.split('_')[2]

    try:
        with data_cache.lock:
            reservation = next((r for r in data_cache.reservations if str(r['id']) == reservation_id), None)
        if not reservation:
            bot.answer_callback_query(call.id, "❌ Бронь не найдена")
            return

        # Асинхронная отмена брони
        def async_cancel_reservation():
            if cancel_reservation(reservation_id, "отменена администратором"):
                # Уведомление пользователя
                user_msg = f"❌ Ваша бронь тележки {reservation['cart']} отменена администратором."
                safe_send_message(reservation['chat_id'], user_msg, reply_markup=create_main_keyboard())

                bot.edit_message_text(
                    f"✅ Бронь тележки {reservation['cart']} успешно отменена!",
                    chat_id,
                    call.message.message_id
                )

        Thread(target=async_cancel_reservation).start()
        bot.answer_callback_query(call.id, "Отменяем бронь...")

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка отмены брони: {error_id} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка")


# Обновление данных
@bot.message_handler(func=lambda message: message.text == 'Обновить данные')
@private_chat_only
def handle_refresh(message):
    try:
        # Обновляем только бронирования (самые частые изменения)
        data_cache.refresh(partial=['reservations'])
        safe_send_message(message.chat.id, "✅ Данные обновлены!")
    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка обновления: {error_id} - {str(e)}")
        safe_send_message(message.chat.id, f"❌ Ошибка обновления: {str(e)}")


# Функция для отправки напоминаний
def send_reminders():
    try:
        current_time = datetime.datetime.now(tz)
        logger.info(f"Проверка напоминаний в {current_time} (UTC: {current_time.astimezone(pytz.utc)})")

        with data_cache.lock:
            reservations_cache_copy = data_cache.reservations.copy()

        for reservation in reservations_cache_copy:
            if not reservation.get('chat_id'):
                continue

            # Создаем уникальный ключ для напоминаний
            start_reminder_key = f"start_{reservation['id']}"
            end_reminder_key = f"end_{reservation['id']}"

            if reservation['status'] == 'Ожидает подтверждения':
                # Напоминание за 15 минут до начала
                reminder_time = reservation['start'] - datetime.timedelta(minutes=15)
                if (reminder_time <= current_time <= reminder_time + datetime.timedelta(minutes=1)
                        and not reminder_status.get(start_reminder_key)):
                    lock_code = get_cart_codes()
                    message = (
                        f"⏰ Напоминание!\n\n"
                        f"Через 15 минут начинается ваша бронь тележки:\n"
                        f"🛒 Тележка: {reservation['cart']}\n"
                        f"⏰ Время: {reservation['start'].strftime('%H:%M')} - {reservation['end'].strftime('%H:%M')}\n"
                        f"🔒 Код: {lock_code}\n\n"
                        f"Не забудьте взять тележку!"
                    )
                    try:
                        safe_send_message(reservation['chat_id'], message)
                        reminder_status[start_reminder_key] = True
                        logger.info(f"Отправлено напоминание о начале для брони {reservation['id']}")
                    except Exception as e:
                        logger.error(f"Ошибка отправки напоминания: {str(e)}")
            # Напоминание в момент окончания брони о необходимости завершения брони
            elif reservation['status'] == 'Активна':
                reminder_time = reservation['end']  # - datetime.timedelta(minutes=15)
                if (reminder_time <= current_time <= reminder_time + datetime.timedelta(minutes=1)
                        and not reminder_status.get(end_reminder_key)):
                    message = (
                        f"⏰ Напоминание!\n\n"
                        f"Не забудьте вернуть тележку и сделать фото:\n"
                        f"🛒 Тележка: {reservation['cart']}\n"
                        f"⏰ Окончание в: {reservation['end'].strftime('%H:%M')}\n"
                    )
                    try:
                        safe_send_message(reservation['chat_id'], message)
                        reminder_status[end_reminder_key] = True
                        logger.info(f"Отправлено напоминание об окончании для брони {reservation['id']}")
                    except Exception as e:
                        logger.error(f"Ошибка отправки напоминания: {str(e)}")

    except Exception as e:
        logger.error(f"Ошибка отправки напоминаний: {str(e)}")


# Проверка всех ожидающих броней
def check_all_pending_reservations():
    now = datetime.datetime.now(tz)
    logger.info(f"Проверка неподтвержденных броней в {now}")

    # Собираем данные для обработки без длительной блокировки
    pending_reservations = []
    with data_cache.lock:
        reservations_cache_copy = data_cache.reservations.copy()

    for reservation in reservations_cache_copy:
        if reservation['status'] != 'Ожидает подтверждения':
            continue

        # Проверяем, не было ли уже отправлено уведомление об отмене
        cancel_key = f"auto_cancel_{reservation['id']}"
        if reminder_status.get(cancel_key):
            continue

        pending_reservations.append({
            'id': reservation['id'],
            'cart': reservation['cart'],
            'start': reservation['start'],
            'end': reservation['end'],
            'chat_id': reservation.get('chat_id', 0)
        })

    # Обрабатываем каждую бронь отдельно
    for res in pending_reservations:
        reservation_id = res['id']

        # Автоотмена при наступлении времени возврата
        if now >= res['end']:
            # Дополнительная проверка статуса в Google Sheets
            try:
                spreadsheet = connect_google_sheets()
                worksheet = spreadsheet.worksheet('Бронирования')
                records = worksheet.get_all_records()

                for record in records:
                    if str(record['ID']) == reservation_id:
                        if record['Статус'] != 'Ожидает подтверждения':
                            logger.info(f"Бронь {reservation_id} уже обновлена, пропускаем отмену")
                            continue
                        break
                else:
                    logger.warning(f"Бронь {reservation_id} не найдена в таблице")
            except Exception as e:
                logger.error(f"Ошибка проверки статуса брони {reservation_id}: {str(e)}")

            # Отменяем бронь
            if cancel_reservation(reservation_id, "время возврата наступило без подтверждения"):
                logger.info(f"reservation.get('chat_id'): {res.get('chat_id')}")
                if res.get('chat_id'):
                    message = (
                        f"❌ Ваша бронь тележки '{res['cart']}' отменена, "
                        f"❌ Ваша бронь тележки '{res['cart']}' отменена, "
                        f"так как время возврата наступило, а бронь не была подтверждена."
                    )
                    try:
                        safe_send_message(res['chat_id'], message, reply_markup=create_main_keyboard())
                        logger.info(f"Бронь {reservation_id} отменена из-за неподтверждения к моменту возврата")
                    except Exception as e:
                        logger.error(f"Ошибка отправки уведомления: {str(e)}")
                else:
                    logger.warning(
                        f"Не удалось отправить уведомление: отсутствует chat_id для брони {reservation_id}")

                # Помечаем как обработанное
                reminder_status[cancel_key] = True


@bot.message_handler(content_types=['new_chat_members'])
def welcome_new_member(message):
    for user in message.new_chat_members:
        chat_id = message.chat.id

        # Получение username без @
        username = user.username.lstrip('@') if user.username else None
        full_name = user.first_name
        if user.last_name:
            full_name += f" {user.last_name}"
        # user_id = user.id

        help_text = get_help_text(username)

        # Если username отсутствует
        if not username:
            send_username_requirement(chat_id, help_text)
        else:
            async_add_user(username, chat_id)

            # Отправка приветствия
            welcome_text = fr"""
👋 Добро пожаловать, {full_name}!
✅ Ваш логин: @{username} успешно зарегистрирован

            """ + help_text

            safe_send_message(
                message.chat.id,
                welcome_text,
                reply_markup=create_main_keyboard(),
                parse_mode='Markdown'
            )
            # send_personal_reminder(user_id, message_text)


def get_help_text(username=None):
    lock_code = get_cart_codes()
    # Общая часть сообщения
    base_text = f"""

----------------------------------------
🚨 **Правила бронирования через общий чат:**

**🔑 Коды цепей:** {lock_code}

**Форматы запросов:**
✅ *На сегодня*:
`Бронь 19:00-21:00`

✅ *На другую дату*:
`29.07.2025 19:00-20:00`

**Обязательные условия:**
1. При использовании тележки:
   - ⌨️ Сообщайте в чат когда берете/возвращаете тележки
   - 📸 К сообщениям прикладывайте фото *до* и *после* использования
2. Возвращайте тележку **🧹чистой** и **без мусора**.

----------------------------------------
💡 **Важно:**
• Если бронировали тележку, но передумали напишите в чат об отмене
• Добавление новых участников: оплата 300₽ через СБП на:
  `Озон Банк | 8(913)508-64-18 | Дмитрий Петрович Б.`
• Чек об оплате отправляйте @MexmodN в *личные сообщения*
    """

    if username:
        base_text = fr"""
    🚨 **Основные правила работы с ботом:**
1. Чтобы начать работу, отправьте команду /start в личные сообщения боту @BookngCartsBot
   - Это нужно сделать при первом использовании
   - Или если вы не видите меню управления
2. После запуска бота вы увидите главное меню с кнопками:
   - 🛒 *Забронировать тележку*, в данном разделе можно посмотреть когда тележка не занята и оформить предварительную бронь, с подсказками на каждом шаге
   - 📋 *Мои брони*, в данном разделе можно увидеть свои активные брони и отменить, подтвердить или завершить их
   - 🔄 *Обновить данные*, используйте ТОЛЬКО если видите неактуальную информацию, в большинстве случаев не требуется!

⚠️ *Важно!* Бот автоматически обновляет данные каждые 30 минут + запоминает ваши запросы между синхронизациями. Не злоупотребляйте ручным обновлением, это расходует ресурсы бесплатного хостинга, на котором развернут бот.
        """ + base_text

    return base_text



def send_username_requirement(chat_id, message_text):
    warning_msg = """
👋 Добро пожаловать! 👋

⚠️ Для работы с ботом необходимо:
1. Указать *Username* в настройках Telegram
   *ИЛИ*
2. Бронировать тележки через общий чат

----------------------------------------
📌 **Инструкция по настройке Username:**
1. Откройте "Настройки" → "Изменить профиль"
2. В поле *Username* введите уникальное имя (например: @Ivanov_2025)
3. Нажмите "Готово"
4. Написать в общий чат, чтобы ваше Username добавили в список пользователей
5. Напишите в личку боту @BookngCartsBot команду /start
6. После активации появятся кнопки управления бронированием
    """ + message_text

    safe_send_message(chat_id, warning_msg, parse_mode='Markdown')


# def send_personal_reminder(user_id, message_text):
#     hello_text = """
#
#     🚨 **Правила бронирования через бота:**
#     В качестве первого сообщения, либо если отсутствует необходимое основное меню бота, то отправьте команду /start
#     В основном меню будет представлено несколько кнопок:
#     • Забронировать тележку, с подсказками что необходимо сделать на каждом шаге
#     • Проверить брони, в данном разделе можно увидеть свои активные брони и отменить, подтвердить или завершить их
#     """ + message_text
#
#     safe_send_message(
#         user_id,
#         hello_text,
#         reply_markup=create_main_keyboard()
#     )


def periodic_refresh():
    """Периодическое обновление данных с оптимизацией"""
    try:
        # Полное обновление раз в 4 часа
        if datetime.datetime.now().hour % 4 == 0:
            logger.info("Запущено полное обновление кэша")
            data_cache.refresh(force=True)
        else:
            # Всегда обновляем бронирования (самые частые изменения)
            data_cache.refresh(partial=['reservations'])
    except Exception as e:
        logger.error(f"Ошибка периодического обновления: {str(e)}")


def start_scheduler():
    # Напоминания за 15 минут до начала и окончания
    schedule.every(1).minutes.do(send_reminders)
    # Отмена неподтвержденных броней
    schedule.every(2).minutes.do(check_all_pending_reservations)
    # Регулярное обновление кэша
    schedule.every(30).minutes.do(periodic_refresh)
    # Очистка устаревших состояний
    schedule.every(30).minutes.do(cleanup_states)

    while True:
        try:
            schedule.run_pending()
            time.sleep(60)
        except Exception as e:
            logger.error(f"Ошибка в планировщике: {str(e)}")
            time.sleep(60)  # Пауза перед перезапуском


def keep_alive():
    max_retries = 5
    retry_delay = 10  # секунд между попытками
    retry_count = 0

    while True:
        try:
            bot.get_me()
            # requests.get('https://google.com', timeout=10)
            # Проверяем обычное интернет-соединение (без прокси)
            session = requests.Session()
            session.trust_env = False  # Игнорируем системные прокси
            session.get('https://google.com', timeout=10)

            logger.info("✓ Соединение с Telegram API и интернетом установлено")
            retry_count = 0  # Сбрасываем счетчик при успехе
            time.sleep(240 + random.randint(0, 120))

        except (requests.exceptions.ProxyError,
                requests.exceptions.ConnectionError,
                RemoteDisconnected) as e:

            retry_count += 1
            if retry_count > max_retries:
                logger.error(f"Прокси недоступен после {max_retries} попыток. Ждем {retry_delay} сек.")
                time.sleep(retry_delay)
                retry_count = 0  # Сбрасываем после длительного ожидания
            else:
                wait_time = 10 * retry_count  # Экспоненциальная задержка
                logger.warning(f"Ошибка прокси ({retry_count}/{max_retries}), ждем {wait_time} сек: {str(e)}")
                time.sleep(wait_time)

        except Exception as e:
            logger.error(f"Ошибка поддержания активности: {str(e)}")


def main_loop():
    retry_delay = 10  # Начальная задержка между перезапусками
    max_retry_delay = 300  # Максимальная задержка (5 минут)

    while True:
        try:
            logger.info("🤖 Starting Telegram bot...")
            bot.infinity_polling(timeout=90, long_polling_timeout=60)
            logger.info("Bot polling exited normally")
            break  # Выход при нормальном завершении

        except (requests.exceptions.ProxyError,
                requests.exceptions.ConnectionError,
                RemoteDisconnected,
                requests.exceptions.SSLError) as e:
            error_id = str(uuid.uuid4())[:8]
            logger.error(f"Сетевая ошибка ({error_id}): {str(e)}")

            # Экспоненциальная задержка с рондомизацией
            sleep_time = min(retry_delay, max_retry_delay) + random.randint(0, 10)
            logger.info(f"🔄 Перезапуск бота через {sleep_time} сек...")
            time.sleep(sleep_time)
            retry_delay *= 2  # Увеличиваем задержку для следующей попытки

        except Exception as e:
            error_id = str(uuid.uuid4())[:8]
            logger.error(f"Критическая ошибка ({error_id}): {str(e)}")
            logger.error(traceback.format_exc())

            sleep_time = min(retry_delay, max_retry_delay)
            logger.info(f"🔄 Перезапуск бота через {sleep_time} сек...")
            time.sleep(sleep_time)
            retry_delay *= 2


if __name__ == '__main__':

    try:
        required_envs = ['BOT_TOKEN', 'SPREADSHEET_ID', 'GOOGLE_CREDS']
        missing = [var for var in required_envs if not os.getenv(var)]

        if missing:
            logger.error(f"❌ Отсутствуют переменные окружения: {', '.join(missing)}")
            sys.exit(1)

        logger.info(f"Текущее время сервера: {datetime.datetime.now()}")
        logger.info(f"Часовой пояс: {tz}")

        # Проверка доступности бота
        bot_info = bot.get_me()
        logger.info(f"Бот запущен: @{bot_info.username} ({bot_info.id})")

        keep_alive_thread = Thread(target=keep_alive, daemon=True)
        keep_alive_thread.start()

        scheduler_thread = Thread(target=start_scheduler, daemon=True)
        scheduler_thread.start()

        init_worksheet_headers()
        data_cache.refresh(force=True)  # Полное обновление при старте

        main_loop()
    except KeyboardInterrupt:
        logger.info("🚦 Graceful shutdown initiated")
        sys.exit(0)