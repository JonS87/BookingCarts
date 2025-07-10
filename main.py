import telebot
from telebot import types
from telebot_calendar import Calendar, CallbackData, RUSSIAN_LANGUAGE
import datetime
import gspread
from oauth2client.service_account import ServiceAccountCredentials
import re
import os
import json
import time
import sys
import traceback
from flask import Flask
import schedule
import pytz
from threading import Thread, Timer
import logging
import uuid
import requests

# Настройка логирования
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler('bot.log')
    ]
)
logger = logging.getLogger(__name__)

# Инициализация бота
BOT_TOKEN = os.getenv('BOT_TOKEN')
SPREADSHEET_ID = os.getenv('SPREADSHEET_ID')
GOOGLE_CREDS_JSON = os.getenv('GOOGLE_CREDS')
NOTIFICATION_CHAT_ID = os.getenv('NOTIFICATION_CHAT_ID')
ADMIN_USERNAMES = os.getenv('ADMINS', '').split(',')
worksheet_headers = {}  # Кэш заголовков листов

tz = pytz.timezone('Europe/Moscow')
# Константа для минимального времени брони (30 минут)
MIN_RESERVATION_MINUTES = 30

try:
    GOOGLE_CREDS = json.loads(GOOGLE_CREDS_JSON)
except Exception as e:
    logger.error(f"Ошибка загрузки JSON: {str(e)}")
    sys.exit(1)

bot = telebot.TeleBot(BOT_TOKEN)
calendar = Calendar(language=RUSSIAN_LANGUAGE)
calendar_callback = CallbackData('calendar', 'action', 'year', 'month', 'day')
timezone = pytz.timezone('Europe/Moscow')

# Состояния пользователя
USER_STATES = {}
STATE_TIMEOUT = 1800  # 30 минут

# Кэш данных
users_cache = {}
reservations_cache = []
carts_cache = {}
last_update = {}


# Подключение к Google Sheets
def connect_google_sheets():
    scope = [
        'https://www.googleapis.com/auth/spreadsheets',
        'https://www.googleapis.com/auth/drive'
    ]
    creds = ServiceAccountCredentials.from_json_keyfile_dict(GOOGLE_CREDS, scope)
    client = gspread.authorize(creds)
    return client.open_by_key(SPREADSHEET_ID)


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


# Клавиатура основного меню
def create_main_keyboard(username=None):
    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    buttons = [
        types.KeyboardButton('Забронировать тележку'),
        types.KeyboardButton('Мои активные брони'),
        types.KeyboardButton('Завершить бронь'),
        types.KeyboardButton('Отменить бронь')
    ]
    keyboard.add(buttons[0], buttons[1])
    keyboard.add(buttons[2], buttons[3])

    # Добавляем строку с админской кнопкой и обновлением данных
    admin_row = []
    admin_row.append(types.KeyboardButton('Обновить данные'))

    # Добавляем кнопку администрирования только для админов
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


# Очистка устаревших состояний
def cleanup_states():
    current_time = time.time()
    for chat_id in list(USER_STATES.keys()):
        state = USER_STATES[chat_id]
        if 'timestamp' in state and current_time - state['timestamp'] > STATE_TIMEOUT:
            logger.info(f"Очистка состояния для chat_id: {chat_id}")
            try:
                bot.send_message(chat_id, "❌ Время сеанса истекло. Начните заново.",
                                 reply_markup=create_main_keyboard())
            except Exception as e:
                logger.error(f"Ошибка отправки сообщения: {str(e)}")
            del USER_STATES[chat_id]


# Генерация временных слотов с учетом занятости
def generate_time_slots(date, step_minutes=15):
    """Генерация временных слотов с учетом занятости тележек"""
    time_slots = []
    current_time = datetime.datetime.now(timezone)

    # Для текущей даты минимальное время - текущее время
    if date.date() == current_time.date():
        # Округляем текущее время вверх до ближайшего шага
        current_minute = current_time.minute
        remainder = current_minute % step_minutes
        if remainder > 0:
            rounded_minute = current_minute - remainder + step_minutes
        else:
            rounded_minute = current_minute
        start_time = current_time.replace(minute=0, second=0, microsecond=0) + datetime.timedelta(
            minutes=rounded_minute)
    else:
        start_time = timezone.localize(datetime.datetime(date.year, date.month, date.day, 0, 0))

    end_time = timezone.localize(datetime.datetime(date.year, date.month, date.day, 23, 45))

    # Генерируем все возможные слоты с шагом 15 минут
    slot = start_time
    while slot <= end_time:
        slot_str = slot.strftime('%H:%M')
        slot_end = slot + datetime.timedelta(minutes=MIN_RESERVATION_MINUTES)

        # Проверяем доступность тележки для этого слота
        available_cart = find_available_cart(slot, slot_end)
        if available_cart:
            time_slots.append(slot_str)

        slot += datetime.timedelta(minutes=step_minutes)

    return time_slots


# Создание клавиатуры с временными слотами
def create_time_keyboard(time_slots, row_width=4):
    if not time_slots:
        return None

    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=row_width)
    buttons = [types.KeyboardButton(time) for time in time_slots]

    # Разбиваем на ряды
    for i in range(0, len(buttons), row_width):
        row = buttons[i:i + row_width]
        keyboard.add(*row)

    keyboard.add(types.KeyboardButton('Отмена'))
    return keyboard


# Обновление кэша тележек
def refresh_carts_cache():
    try:
        spreadsheet = connect_google_sheets()
        carts_sheet = spreadsheet.worksheet('Тележки')
        carts_data = carts_sheet.get_all_records()
        global carts_cache
        carts_cache = {}

        for cart in carts_data:
            active_status = str(cart.get('Активна', 'Да')).strip().lower()
            carts_cache[cart['Название']] = {
                'lock_code': cart['КодЗамка'],
                'active': active_status in ['да', 'yes', '1', 'true']
            }
        logger.info(f"Обновлено {len(carts_cache)} тележек")
    except Exception as e:
        logger.error(f"Ошибка обновления кэша тележек: {str(e)}")


# Обновление кэша
def refresh_cache():
    global users_cache, reservations_cache, last_update

    try:
        logger.info("Обновление кэша...")
        spreadsheet = connect_google_sheets()

        # Обновление пользователей
        users_sheet = spreadsheet.worksheet('Пользователи')
        users_data = users_sheet.get_all_records()
        users_cache = {user['Логин']: user.get('ChatID', '') for user in users_data}

        # Обновление бронирований
        reservations_sheet = spreadsheet.worksheet('Бронирования')
        reservations_data = reservations_sheet.get_all_records()
        reservations_cache = []

        for res in reservations_data:
            try:
                # Исправление: обработка дат без часового пояса
                start_time = datetime.datetime.strptime(res['Начало'], '%Y-%m-%d %H:%M')
                start_time = timezone.localize(start_time)

                end_time = datetime.datetime.strptime(res['Конец'], '%Y-%m-%d %H:%M')
                end_time = timezone.localize(end_time)

                actual_start = None
                if res.get('ФактическоеНачало'):
                    actual_start = datetime.datetime.strptime(res['ФактическоеНачало'], '%Y-%m-%d %H:%M')
                    actual_start = timezone.localize(actual_start)

                actual_end = None
                if res.get('ФактическийКонец'):
                    actual_end = datetime.datetime.strptime(res['ФактическийКонец'], '%Y-%m-%d %H:%M')
                    actual_end = timezone.localize(actual_end)

                allowed_statuses = ['Активна', 'Завершена', 'Отменена', 'Ожидает подтверждения']
                if res['Статус'] not in allowed_statuses:
                    logger.warning(f"Неверный статус брони {res['ID']}: {res['Статус']}")
                    res['Статус'] = 'Активна'

                reservation = {
                    'id': res['ID'],
                    'cart': res['Тележка'],
                    'start': start_time,
                    'end': end_time,
                    'actual_start': actual_start,
                    'actual_end': actual_end,
                    'username': res['Пользователь'],
                    'status': res['Статус'],
                    'photo_id': res.get('Фото', ''),
                    'chat_id': res.get('ChatID', '')
                }
                reservations_cache.append(reservation)
            except Exception as e:
                logger.error(f"Ошибка обработки брони: {res} - {str(e)}")

        logger.info(f"Обновлено {len(reservations_cache)} бронирований")
        last_update['time'] = time.time()

        # Обновление тележек
        refresh_carts_cache()

    except Exception as e:
        logger.error(f"Ошибка обновления кэша: {str(e)}")
        traceback.print_exc()


# Поиск свободной тележки
def find_available_cart(start_time, end_time):
    if start_time.tzinfo is None:
        start_time = tz.localize(start_time)
    if end_time.tzinfo is None:
        end_time = tz.localize(end_time)

    occupied_carts = set()

    for res in reservations_cache:
        if res['status'] in ['Отменена', 'Завершена']:
            continue

        # Проверка пересечения интервалов
        if (res['start'] < end_time) and (res['end'] > start_time):
            occupied_carts.add(res['cart'])
            logger.info(f"Тележка '{res['cart']}'' занята: {res['start']}-{res['end']}")

    logger.info(f"Занятые тележки: {occupied_carts}")

    # Возвращаем список ВСЕХ свободных тележек
    available_carts = [
        cart for cart, data in carts_cache.items()
        if data['active'] and cart not in occupied_carts
    ]

    # Сортируем по номеру (если названия "Тележка 1", "Тележка 2")
    available_carts.sort(key=lambda x: int(x.split()[-1]))

    if available_carts:
        logger.info(f"Найдена свободная тележка: {available_carts[0]}")
        return available_carts[0]
    else:
        logger.info("Свободных тележек не найдено")
        return None


# Генерация ID брони
def generate_reservation_id():
    return int(time.time() * 1000)


# Отправка уведомления в общий чат
def send_notification(message, photo_id=None):
    try:
        if NOTIFICATION_CHAT_ID:
            if photo_id:
                bot.send_photo(NOTIFICATION_CHAT_ID, photo_id, caption=message)
            else:
                bot.send_message(NOTIFICATION_CHAT_ID, message)
    except Exception as e:
        logger.error(f"Ошибка отправки уведомления: {str(e)}")


# Обработчик ошибок (ИСПРАВЛЕННЫЙ)
def handle_errors(messages):
    try:
        # Если пришел одиночный message, а не список
        if not isinstance(messages, list):
            messages = [messages]

        for message in messages:
            try:
                bot.process_new_messages([message])
            except Exception as e:
                error_id = str(uuid.uuid4())[:8]
                logger.error(f"Ошибка обработки сообщения {error_id}: {str(e)}")
                try:
                    # Проверяем наличие необходимых атрибутов
                    if hasattr(message, 'chat') and hasattr(message.chat, 'id'):
                        bot.send_message(message.chat.id,
                                         f"⚠️ Произошла ошибка ({error_id}). Пожалуйста, попробуйте позже.")
                    else:
                        logger.error(f"Сообщение не содержит информацию о чате: {message}")
                except Exception as inner_e:
                    logger.error(f"Ошибка отправки сообщения об ошибке: {str(inner_e)}")
    except Exception as e:
        logger.error(f"Критическая ошибка в обработчике ошибок: {str(e)}")


# Обработчик команды /start
@bot.message_handler(commands=['start'])
def start(message):
    try:
        refresh_cache()
        username = message.from_user.username
        chat_id = message.chat.id
        logger.info(f'ID чата: {chat_id}')

        if username in users_cache:
            bot.send_message(chat_id, f'Привет @{username}!',
                             reply_markup=create_main_keyboard(username))

            # Обновляем ChatID пользователя
            if users_cache[username] != str(chat_id):
                spreadsheet = connect_google_sheets()
                users_sheet = spreadsheet.worksheet('Пользователи')

                # Находим пользователя и обновляем ChatID
                records = users_sheet.get_all_records()
                for i, user in enumerate(records, start=2):
                    if user['Логин'] == username:
                        users_sheet.update_cell(i, 2, str(chat_id))  # Используем индекс столбца
                        break

                refresh_cache()
        else:
            bot.send_message(chat_id, "❌ Вы не зарегистрированы в системе. Обратитесь к администратору.")

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка в /start: {error_id} - {str(e)}")
        bot.send_message(message.chat.id, f"⚠️ Произошла ошибка ({error_id}). Попробуйте позже.")


# Обработчик бронирования
@bot.message_handler(func=lambda message: message.text == 'Забронировать тележку')
def start_reservation(message):
    chat_id = message.chat.id
    USER_STATES[chat_id] = {
        'step': 'select_date',
        'timestamp': time.time()
    }
    now = datetime.datetime.now(timezone)
    bot.send_message(chat_id, 'Выберите дату бронирования:',
                     reply_markup=calendar.create_calendar(
                         name=calendar_callback.prefix,
                         year=now.year,
                         month=now.month))


# Обработчик календаря
@bot.callback_query_handler(func=lambda call: call.data.startswith(calendar_callback.prefix))
def handle_calendar(call):
    chat_id = call.message.chat.id
    name, action, year, month, day = call.data.split(calendar_callback.sep)
    date = calendar.calendar_query_handler(
        bot=bot, call=call, name=name,
        action=action, year=year, month=month, day=day
    )

    if action == 'DAY':
        # Генерируем временные слоты для выбранной даты
        time_slots = generate_time_slots(date)

        if not time_slots:
            bot.send_message(chat_id, "❌ На выбранную дату нет свободных слотов. Выберите другую дату.",
                             reply_markup=create_main_keyboard(call.from_user.username))
            return

        USER_STATES[chat_id] = {
            'step': 'select_start_time',
            'date': date,
            'timestamp': time.time()
        }
        bot.send_message(chat_id, 'Выберите время начала:',
                         reply_markup=create_time_keyboard(time_slots))

    elif action == 'CANCEL':
        bot.send_message(chat_id, 'Выбор отменен', reply_markup=create_main_keyboard(call.from_user.username))
        if chat_id in USER_STATES:
            del USER_STATES[chat_id]


# Обработчик выбора времени начала
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'select_start_time')
def handle_start_time(message):
    chat_id = message.chat.id
    time_str = message.text.strip()

    if time_str == 'Отмена':
        bot.send_message(chat_id, 'Отмена бронирования', reply_markup=create_main_keyboard(message.from_user.username))
        if chat_id in USER_STATES:
            del USER_STATES[chat_id]
        return

    state = USER_STATES[chat_id]
    date = state['date']

    try:
        hours, minutes = map(int, time_str.split(':'))
        start_time = timezone.localize(datetime.datetime(date.year, date.month, date.day, hours, minutes))
        current_time = datetime.datetime.now(timezone)

        if start_time < current_time - datetime.timedelta(minutes=15):
            bot.send_message(chat_id, '❌ Нельзя бронировать в прошлом!')
            return

        # Генерируем временные слоты для окончания
        min_end_time = start_time + datetime.timedelta(minutes=MIN_RESERVATION_MINUTES)
        max_end_time = start_time + datetime.timedelta(hours=3)

        # Создаем слоты с шагом 15 минут
        end_time_slots = []
        slot = min_end_time
        while slot <= max_end_time:
            end_time_slots.append(slot.strftime('%H:%M'))
            slot += datetime.timedelta(minutes=15)

        USER_STATES[chat_id] = {
            'step': 'select_end_time',
            'date': date,
            'start_time': start_time,
            'timestamp': time.time()
        }
        bot.send_message(chat_id, 'Выберите время окончания:',
                         reply_markup=create_time_keyboard(end_time_slots))

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка выбора времени: {error_id} - {str(e)}")
        bot.send_message(chat_id, f'❌ Ошибка: {str(e)}')


# Обработчик выбора времени окончания
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'select_end_time')
def handle_end_time(message):
    chat_id = message.chat.id
    time_str = message.text.strip()
    state = USER_STATES[chat_id]

    if time_str == 'Отмена':
        bot.send_message(chat_id, 'Отмена бронирования', reply_markup=create_main_keyboard(message.from_user.username))
        if chat_id in USER_STATES:
            del USER_STATES[chat_id]
        return

    try:
        hours, minutes = map(int, time_str.split(':'))
        start_time = state['start_time']
        end_time = timezone.localize(datetime.datetime(
            start_time.year,
            start_time.month,
            start_time.day,
            hours, minutes
        ))

        if end_time <= start_time:
            bot.send_message(chat_id, '❌ Время окончания должно быть позже времени начала!')
            return

        # Минимальное время брони - 15 минут
        if (end_time - start_time) < datetime.timedelta(minutes=MIN_RESERVATION_MINUTES):
            bot.send_message(chat_id, f'❌ Минимальное время брони - {MIN_RESERVATION_MINUTES} минут!')
            return

        # Поиск свободной тележки
        cart = find_available_cart(start_time, end_time)
        if not cart:
            bot.send_message(chat_id, '❌ Все тележки заняты на выбранный период!',
                             reply_markup=create_main_keyboard(message.from_user.username))
            del USER_STATES[chat_id]
            return

        # Сохраняем данные
        state['end_time'] = end_time
        state['cart'] = cart
        state['step'] = 'confirm_reservation'
        state['timestamp'] = time.time()

        # Формируем подтверждение
        lock_code = carts_cache[cart]['lock_code']
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
            types.InlineKeyboardButton('✅ Подтвердить', callback_data='confirm_reservation'),
            types.InlineKeyboardButton('❌ Отменить', callback_data='cancel_reservation')
        )

        bot.send_message(chat_id, confirm_text, reply_markup=types.ReplyKeyboardRemove())
        bot.send_message(chat_id, "Подтвердите бронирование:", reply_markup=keyboard)

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка выбора времени окончания: {error_id} - {str(e)}")
        bot.send_message(chat_id, f'❌ Ошибка: {str(e)}')


# Подтверждение бронирования
@bot.callback_query_handler(func=lambda call: call.data in ['confirm_reservation', 'cancel_reservation'])
def handle_confirmation(call):
    chat_id = call.message.chat.id
    username = call.from_user.username

    if call.data == 'cancel_reservation':
        bot.edit_message_text("❌ Бронирование отменено",
                              chat_id,
                              call.message.message_id)
        bot.send_message(chat_id, "Выберите действие:", reply_markup=create_main_keyboard(call.from_user.username))
        if chat_id in USER_STATES:
            del USER_STATES[chat_id]
        return

    if chat_id not in USER_STATES:
        bot.answer_callback_query(call.id, "❌ Данные устарели")
        return

    state = USER_STATES[chat_id]
    if state['step'] != 'confirm_reservation':
        bot.answer_callback_query(call.id, "❌ Неверный шаг")
        return

    try:
        # Создаем запись бронирования
        reservation_id = generate_reservation_id()
        start_time = state['start_time']
        end_time = state['end_time']
        cart = state['cart']
        lock_code = carts_cache[cart]['lock_code']

        # Добавляем в Google Sheets
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Бронирования')

        new_row = [
            reservation_id,
            cart,
            start_time.strftime('%Y-%m-%d %H:%M'),
            end_time.strftime('%Y-%m-%d %H:%M'),
            "",  # ФактическоеНачало
            "",  # ФактическийКонец
            username,
            "Ожидает подтверждения",
            "",  # Фото
            str(chat_id)
        ]
        sheet.append_row(new_row)

        # Обновляем кэш
        refresh_cache()

        USER_STATES[chat_id] = {
            'step': 'take_photo',
            'reservation_id': reservation_id,
            'cart': cart,
            'start_time': start_time,
            'end_time': end_time,
            'timestamp': time.time()
        }

        bot.send_message(chat_id, "📸 Пожалуйста, отправьте фотографию тележки перед взятием:",
                         reply_markup=create_cancel_keyboard())

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка бронирования: {error_id} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка бронирования")


# Обработчик кнопки "Администрирование"
@bot.message_handler(func=lambda message: message.text == 'Администрирование')
def admin_menu(message):
    chat_id = message.chat.id
    username = message.from_user.username

    if username not in ADMIN_USERNAMES:
        bot.send_message(chat_id, "❌ Доступ запрещен")
        return

    bot.send_message(chat_id, "Администрирование:",
                     reply_markup=create_admin_keyboard())


# Просмотр всех активных броней
@bot.message_handler(func=lambda message: message.text == 'Все активные брони')
def show_all_active(message):
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        bot.send_message(message.chat.id, "❌ Доступ запрещен")
        return

    active_reservations = [r for r in reservations_cache if r['status'] == 'Активна']
    if not active_reservations:
        bot.send_message(message.chat.id, "Нет активных бронирований")
        return

    response = "📋 Все активные брони:\n\n"
    for i, res in enumerate(active_reservations, 1):
        start_time = res['actual_start'] if res.get('actual_start') else res['start']
        response += (
            f"{i}. 🛒 {res['cart']}\n"
            f"   👤 @{res['username']}\n"
            f"   📅 {start_time.strftime('%d.%m.%Y %H:%M')} - {res['end'].strftime('%H:%M')}\n"
            f"   🔒 Код: {carts_cache[res['cart']]['lock_code']}\n\n"
        )

    bot.send_message(message.chat.id, response)


# Управление тележками
@bot.message_handler(func=lambda message: message.text == 'Управление тележками')
def manage_carts(message):
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        bot.send_message(message.chat.id, "❌ Доступ запрещен")
        return

    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
    keyboard.add(
        types.KeyboardButton('Добавить тележку'),
        types.KeyboardButton('Изменить статус тележки'),
        types.KeyboardButton('Изменить пароль тележки'),
        types.KeyboardButton('Назад')
    )
    bot.send_message(message.chat.id, "Управление тележками:", reply_markup=keyboard)


# Обработчик кнопки "Назад"
@bot.message_handler(func=lambda message: message.text == 'Назад')
def back_to_main(message):
    chat_id = message.chat.id
    username = message.from_user.username
    bot.send_message(chat_id, "Главное меню:",
                     reply_markup=create_main_keyboard(username))


# Добавление новой тележки
@bot.message_handler(func=lambda message: message.text == 'Добавить тележку')
def add_cart(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        bot.send_message(chat_id, "❌ Доступ запрещен")
        return

    USER_STATES[chat_id] = {
        'step': 'adding_cart_name',
        'timestamp': time.time()
    }
    bot.send_message(chat_id, "Введите название новой тележки:", reply_markup=create_cancel_keyboard())


# Обработчик ввода названия тележки
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'adding_cart_name')
def handle_new_cart_name(message):
    chat_id = message.chat.id
    cart_name = message.text.strip()

    if cart_name == 'Отмена':
        bot.send_message(chat_id, "❌ Действие отменено", reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]
        return

    if cart_name in carts_cache:
        bot.send_message(chat_id, "❌ Тележка с таким названием уже существует")
        return

    USER_STATES[chat_id] = {
        'step': 'adding_cart_password',
        'cart_name': cart_name,
        'timestamp': time.time()
    }
    bot.send_message(chat_id, f"Введите пароль (4 цифры) для тележки '{cart_name}':")


# Обработчик ввода пароля тележки
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'adding_cart_password')
def handle_new_cart_password(message):
    chat_id = message.chat.id
    password = message.text.strip()
    state = USER_STATES[chat_id]
    cart_name = state['cart_name']

    if not re.match(r'^\d{4}$', password):
        bot.send_message(chat_id, "❌ Пароль должен состоять из 4 цифр")
        return

    try:
        # Добавляем тележку в Google Sheets
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Тележки')
        new_row = [cart_name, password, "Да"]  # Название, Пароль, Активна
        sheet.append_row(new_row)

        # Обновляем кэш
        refresh_carts_cache()

        bot.send_message(chat_id, f"✅ Тележка '{cart_name}' успешно добавлена!",
                         reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка добавления тележки: {error_id} - {str(e)}")
        bot.send_message(chat_id, f"❌ Ошибка при добавлении тележки: {str(e)}")


# Обработчик изменения пароля тележки
@bot.message_handler(func=lambda message: message.text == 'Изменить пароль тележки')
def change_cart_code(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        bot.send_message(chat_id, "❌ Доступ запрещен")
        return

    # Формируем список тележек
    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
    for cart in carts_cache:
        status = "🟢" if carts_cache[cart]['active'] else "🔴"
        keyboard.add(types.KeyboardButton(f"{status} {cart}"))
    keyboard.add(types.KeyboardButton('Отмена'))

    USER_STATES[chat_id] = {
        'step': 'select_cart_for_password_change',
        'timestamp': time.time()
    }
    bot.send_message(chat_id, "Выберите тележку для изменения кода:", reply_markup=keyboard)


# Обработчик выбора тележки для изменения пароля
@bot.message_handler(
    func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'select_cart_for_password_change')
def handle_cart_selection_for_password_change(message):
    chat_id = message.chat.id
    cart_name = message.text[2:].strip()  # Убираем эмодзи статуса

    if message.text == 'Отмена':
        bot.send_message(chat_id, "❌ Действие отменено", reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]
        return

    if cart_name not in carts_cache:
        bot.send_message(chat_id, "❌ Тележка не найдена")
        return

    USER_STATES[chat_id] = {
        'step': 'enter_new_cart_password',
        'cart_name': cart_name,
        'timestamp': time.time()
    }
    bot.send_message(chat_id, f"Введите новый пароль для тележки '{cart_name}':",
                     reply_markup=create_cancel_keyboard())


# Обработчик ввода нового пароля
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'enter_new_cart_password')
def handle_change_cart_password(message):
    chat_id = message.chat.id
    new_code = message.text.strip()
    state = USER_STATES[chat_id]

    if new_code == 'Отмена':
        bot.send_message(chat_id, "❌ Действие отменено", reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]
        return

    # Проверка формата кода (4 цифры)
    if not re.match(r'^\d{4}$', new_code):
        bot.send_message(chat_id, "❌ Пароль должен состоять из 4 цифр")
        return

    try:
        # Обновляем код в Google Sheets
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Тележки')

        # Находим строку с тележкой
        records = sheet.get_all_records()
        for i, record in enumerate(records, start=2):
            if record['Название'] == state['cart_name']:
                sheet.update_cell(i, 2, new_code)  # Используем индекс столбца
                break

        # Обновляем кэш
        refresh_carts_cache()

        bot.send_message(chat_id, f"✅ Пароль тележки '{state['cart_name']}' успешно изменен на {new_code}",
                         reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка изменения пароля: {error_id} - {str(e)}")
        bot.send_message(chat_id, f"❌ Ошибка при изменении пароля: {str(e)}")


# Изменение статуса тележки
@bot.message_handler(func=lambda message: message.text == 'Изменить статус тележки')
def change_cart_status(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        bot.send_message(chat_id, "❌ Доступ запрещен")
        return

    # Формируем список тележек
    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
    for cart in carts_cache:
        status = "🟢" if carts_cache[cart]['active'] else "🔴"
        keyboard.add(types.KeyboardButton(f"{status} {cart}"))
    keyboard.add(types.KeyboardButton('Отмена'))

    USER_STATES[chat_id] = {
        'step': 'select_cart_for_status_change',
        'timestamp': time.time()
    }
    bot.send_message(chat_id, "Выберите тележку для изменения статуса:", reply_markup=keyboard)


# Обработчик выбора тележки для изменения статуса
@bot.message_handler(
    func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'select_cart_for_status_change')
def handle_cart_status_change(message):
    chat_id = message.chat.id
    cart_name = message.text[2:].strip()  # Убираем эмодзи статуса

    if message.text == 'Отмена':
        bot.send_message(chat_id, "❌ Действие отменено", reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]
        return

    if cart_name not in carts_cache:
        bot.send_message(chat_id, "❌ Тележка не найдена")
        return

    try:
        # Меняем статус на противоположный
        new_status = "Нет" if carts_cache[cart_name]['active'] else "Да"

        # Обновляем в Google Sheets
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Тележки')

        # Находим строку с тележкой
        records = sheet.get_all_records()
        for i, record in enumerate(records, start=2):
            if record['Название'] == cart_name:
                sheet.update_cell(i, 3, new_status)  # Используем индекс столбца
                break

        # Обновляем кэш
        refresh_carts_cache()

        status_text = "активирована" if new_status == "Да" else "деактивирована"
        bot.send_message(chat_id, f"✅ Тележка '{cart_name}' успешно {status_text}!",
                         reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка изменения статуса: {error_id} - {str(e)}")
        bot.send_message(chat_id, f"❌ Ошибка при изменении статуса: {str(e)}")


# Управление пользователями
@bot.message_handler(func=lambda message: message.text == 'Управление пользователями')
def manage_users(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        bot.send_message(chat_id, "❌ Доступ запрещен")
        return

    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
    keyboard.add(
        types.KeyboardButton('Добавить пользователя'),
        types.KeyboardButton('Удалить пользователя'),
        types.KeyboardButton('Назад')
    )
    bot.send_message(chat_id, "Управление пользователями:", reply_markup=keyboard)


# Добавление пользователя
@bot.message_handler(func=lambda message: message.text == 'Добавить пользователя')
def add_user(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        bot.send_message(chat_id, "❌ Доступ запрещен")
        return

    USER_STATES[chat_id] = {
        'step': 'adding_user',
        'timestamp': time.time()
    }
    bot.send_message(chat_id, "Введите логин нового пользователя (без @):",
                     reply_markup=create_cancel_keyboard())


# Обработчик добавления пользователя
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'adding_user')
def handle_add_user(message):
    chat_id = message.chat.id
    new_username = message.text.strip().lower()

    if new_username == 'Отмена':
        bot.send_message(chat_id, "❌ Действие отменено", reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]
        return

    if new_username in users_cache:
        bot.send_message(chat_id, "❌ Пользователь уже существует")
        return

    try:
        # Добавляем пользователя в Google Sheets
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Пользователи')
        new_row = [new_username, ""]  # Логин, ChatID
        sheet.append_row(new_row)

        # Обновляем кэш
        refresh_cache()

        bot.send_message(chat_id, f"✅ Пользователь @{new_username} успешно добавлен!",
                         reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка добавления пользователя: {error_id} - {str(e)}")
        bot.send_message(chat_id, f"❌ Ошибка при добавлении пользователя: {str(e)}")


# Удаление пользователя
@bot.message_handler(func=lambda message: message.text == 'Удалить пользователя')
def delete_user(message):
    chat_id = message.chat.id
    username = message.from_user.username
    if username not in ADMIN_USERNAMES:
        bot.send_message(chat_id, "❌ Доступ запрещен")
        return

    # Формируем список пользователей
    if not users_cache:
        bot.send_message(chat_id, "❌ Нет пользователей для удаления")
        return

    keyboard = types.ReplyKeyboardMarkup(resize_keyboard=True)
    for user in users_cache:
        keyboard.add(types.KeyboardButton(f"👤 @{user}"))
    keyboard.add(types.KeyboardButton('Отмена'))

    USER_STATES[chat_id] = {
        'step': 'deleting_user',
        'timestamp': time.time()
    }
    bot.send_message(chat_id, "Выберите пользователя для удаления:", reply_markup=keyboard)


# Обработчик удаления пользователя
@bot.message_handler(func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'deleting_user')
def handle_delete_user(message):
    chat_id = message.chat.id
    username = message.text.replace('👤 @', '').strip()

    if message.text == 'Отмена':
        bot.send_message(chat_id, "❌ Действие отменено", reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]
        return

    if username not in users_cache:
        bot.send_message(chat_id, "❌ Пользователь не найден")
        return

    # Проверка активных броней пользователя
    active_reservations = any(
        r for r in reservations_cache
        if r['username'] == username and r['status'] == 'Активна'
    )

    if active_reservations:
        bot.send_message(chat_id, "❌ Нельзя удалить пользователя с активными бронями")
        return

    try:
        # Удаляем пользователя из Google Sheets
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Пользователи')

        # Находим строку пользователя
        records = sheet.get_all_records()
        for i, record in enumerate(records, start=2):
            if record['Логин'] == username:
                sheet.delete_rows(i)
                break

        # Обновляем кэш
        refresh_cache()

        bot.send_message(chat_id, f"✅ Пользователь @{username} успешно удален!",
                         reply_markup=create_main_keyboard(message.from_user.username))
        del USER_STATES[chat_id]

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка удаления пользователя: {error_id} - {str(e)}")
        bot.send_message(chat_id, f"❌ Ошибка при удалении пользователя: {str(e)}")


# Общий обработчик команды "Отмена"
@bot.message_handler(func=lambda message: message.text == 'Отмена')
def handle_general_cancel(message):
    chat_id = message.chat.id
    bot.send_message(chat_id, "❌ Действие отменено", reply_markup=create_main_keyboard(message.from_user.username))
    if chat_id in USER_STATES:
        del USER_STATES[chat_id]


# Обработчик фотографий при взятии тележки
@bot.message_handler(content_types=['photo'],
                     func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'take_photo')
def handle_take_photo(message):
    chat_id = message.chat.id
    state = USER_STATES[chat_id]
    username = message.from_user.username
    reservation_id = state['reservation_id']
    actual_start = datetime.datetime.now(timezone)  # Фактическое время взятия

    try:
        # Сохраняем фото
        file_id = message.photo[-1].file_id

        # Обновляем запись в Google Sheets
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Бронирования')

        # Находим строку
        records = sheet.get_all_records()
        for i, record in enumerate(records, start=2):
            if record['ID'] == reservation_id:
                # Обновляем фото и фактическое время начала
                sheet.update_cell(i, 9, file_id)  # Фото
                sheet.update_cell(i, 5, actual_start.strftime('%Y-%m-%d %H:%M'))  # ФактическоеНачало
                sheet.update_cell(i, 8, "Активна")  # ОБНОВЛЯЕМ СТАТУС
                break

        # Отправляем уведомление в общий чат
        cart = state['cart']
        lock_code = carts_cache[cart]['lock_code']
        take_cart_msg = (
            f"✅ {cart} забронирована!\n\n"
            f"👤 Пользователь: @{username}\n"
            f"⏱ Фактическое время бронирования: {actual_start.strftime('%d.%m.%Y %H:%M')}\n"
            f"⏰ Плановое время возврата: {state['end_time'].strftime('%H:%M')}\n"
        )

        send_notification(take_cart_msg, file_id)

        bot.send_message(chat_id, "✅ Фотография тележки сохранена! Бронирование подтверждено.",
                         reply_markup=create_main_keyboard(message.from_user.username))

        # Обновляем кэш
        refresh_cache()
        del USER_STATES[chat_id]

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка обработки фото: {error_id} - {str(e)}")
        bot.send_message(chat_id, "❌ Ошибка обработки фото")


# Показать активные брони пользователя
@bot.message_handler(func=lambda message: message.text in ['Мои активные брони', 'Отменить бронь', 'Завершить бронь'])
def handle_user_actions(message):
    chat_id = message.chat.id
    username = message.from_user.username

    if username not in users_cache:
        bot.send_message(chat_id, "❌ Пользователь не найден")
        return

    # Фильтруем брони
    user_reservations = []
    current_time = datetime.datetime.now(timezone)

    for res in reservations_cache:
        if res['username'] != username:
            continue

        if message.text == 'Мои активные брони':
            if res['status'] == 'Активна':
                user_reservations.append(res)

        elif message.text == 'Отменить бронь':
            # Можно отменять только брони без подтверждения
            if res['status'] == 'Ожидает подтверждения' and not res.get('actual_start', ''):
                user_reservations.append(res)

        elif message.text == 'Завершить бронь':
            # Можно завершать только активные и начавшиеся брони
            if res['status'] == 'Активна' and res.get('photo_id', ''):
                user_reservations.append(res)

    if not user_reservations:
        action_name = {
            'Мои активные брони': 'активных бронирований',
            'Отменить бронь': 'бронирований для отмены',
            'Завершить бронь': 'бронирований для завершения'
        }
        bot.send_message(chat_id, f"❌ У вас нет {action_name[message.text]}")
        return

    # Формируем список бронирований
    keyboard = types.InlineKeyboardMarkup()

    for res in user_reservations:
        text = (
            f"{res['cart']} - "
            f"{res['start'].strftime('%d.%m %H:%M')} → "
            f"{res['end'].strftime('%H:%M')}"
        )

        if message.text == 'Отменить бронь':
            callback_data = f"cancel_{res['id']}"
        elif message.text == 'Завершить бронь':
            callback_data = f"return_{res['id']}"
        else:  # Только просмотр
            continue

        keyboard.add(types.InlineKeyboardButton(text, callback_data=callback_data))

    if message.text == 'Мои активные брони':
        response = "📋 Ваши активные брони:"
        for i, res in enumerate(user_reservations, 1):
            start_time = res['actual_start'] if res.get('actual_start') else res['start']
            response += (
                f"\n\n{i}. 🛒 {res['cart']}\n"
                f"   📅 {start_time.strftime('%d.%m.%Y')}\n"
                f"   ⏰ {start_time.strftime('%H:%M')} - {res['end'].strftime('%H:%M')}\n"
                f"   🔒 Код: {carts_cache[res['cart']]['lock_code']}"
            )
        bot.send_message(chat_id, response)
    else:
        action = 'отмены' if message.text == 'Отменить бронь' else 'завершения'
        bot.send_message(chat_id, f"Выберите бронь для {action}:", reply_markup=keyboard)


# Обработка отмены брони
@bot.callback_query_handler(func=lambda call: call.data.startswith('cancel_'))
def handle_cancel_reservation(call):
    chat_id = call.message.chat.id
    reservation_id = call.data.split('_')[1]
    username = call.from_user.username

    try:
        # Находим бронирование
        reservation = next((r for r in reservations_cache if str(r['id']) == reservation_id), None)

        if not reservation:
            bot.answer_callback_query(call.id, "❌ Бронь не найдена")
            return

        if reservation['status'] != 'Ожидает подтверждения':
            bot.answer_callback_query(call.id, "❌ Бронь не находится в статусе 'Ожидает подтверждения'")
            return

        # Обновляем в Google Sheets
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Бронирования')

        # Находим строку для обновления
        records = sheet.get_all_records()
        row_index = None

        for i, record in enumerate(records, start=2):
            if str(record['ID']) == reservation_id:
                row_index = i
                break

        if not row_index:
            bot.answer_callback_query(call.id, "❌ Бронь не найдена в таблице")
            return

        # Обновляем статус
        sheet.update_cell(row_index, 8, 'Отменена')  # Статус

        # Обновляем кэш
        refresh_cache()

        start_str = reservation['start'].strftime('%d.%m %H:%M')
        end_str = reservation['end'].strftime('%H:%M')
        cart_name = reservation['cart']
        success_msg = f"✅ Бронь {cart_name} на {start_str}-{end_str} отменена"
        bot.edit_message_text(success_msg, chat_id, call.message.message_id)

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка отмены брони: {error_id} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка отмены брони")


# Обработка завершения брони
@bot.callback_query_handler(func=lambda call: call.data.startswith('return_'))
def handle_return_cart(call):
    chat_id = call.message.chat.id
    reservation_id = call.data.split('_')[1]

    try:
        # Находим бронирование
        reservation = next((r for r in reservations_cache if str(r['id']) == reservation_id), None)

        if not reservation:
            bot.answer_callback_query(call.id, "❌ Бронь не найдена")
            return

        # Сохраняем состояние
        USER_STATES[chat_id] = {
            'step': 'return_photo',
            'reservation_id': reservation_id,
            'reservation_data': reservation,
            'timestamp': time.time()
        }

        bot.send_message(chat_id, "📸 Пожалуйста, отправьте фото возвращенной тележки:")

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка завершения брони: {error_id} - {str(e)}")
        bot.answer_callback_query(call.id, "❌ Ошибка")


# Обработка фотографий при возврате
@bot.message_handler(content_types=['photo'],
                     func=lambda message: USER_STATES.get(message.chat.id, {}).get('step') == 'return_photo')
def handle_return_photo(message):
    chat_id = message.chat.id
    state = USER_STATES[chat_id]
    reservation_id = state['reservation_id']
    reservation = state['reservation_data']
    username = message.from_user.username
    actual_end = datetime.datetime.now(timezone)  # Фактическое время возврата

    try:
        # Сохраняем фото
        file_id = message.photo[-1].file_id

        # Обновляем запись в Google Sheets
        spreadsheet = connect_google_sheets()
        sheet = spreadsheet.worksheet('Бронирования')

        # Находим строку
        records = sheet.get_all_records()
        for i, record in enumerate(records, start=2):
            if record['ID'] == int(reservation_id):
                # Обновляем фото, фактическое время окончания и статус
                sheet.update_cell(i, 9, file_id)  # Фото
                sheet.update_cell(i, 6, actual_end.strftime('%Y-%m-%d %H:%M'))  # ФактическийКонец
                sheet.update_cell(i, 8, 'Завершена')  # Статус
                break

        # Отправляем уведомление в общий чат
        cart = reservation['cart']
        lock_code = carts_cache[cart]['lock_code']
        return_msg = (
            f"✅ {cart} возвращена!\n"
            f"👤 Пользователь: @{username}\n"
            f"📅 Дата брони: {reservation['start'].strftime('%d.%m.%Y')}\n"
            f"⏰ Время брони: {actual_end.strftime('%H:%M')} - {reservation['end'].strftime('%H:%M')}\n"
        )

        send_notification(return_msg, file_id)

        bot.send_message(chat_id, "✅ Тележка успешно возвращена! Бронь завершена.",
                         reply_markup=create_main_keyboard(message.from_user.username))

        # Обновляем кэш
        refresh_cache()
        del USER_STATES[chat_id]

    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка обработки фото: {error_id} - {str(e)}")
        bot.send_message(chat_id, "❌ Ошибка обработки фото")


# Обновление данных
@bot.message_handler(func=lambda message: message.text == 'Обновить данные')
def handle_refresh(message):
    try:
        refresh_cache()
        bot.send_message(message.chat.id, "✅ Данные обновлены!")
    except Exception as e:
        error_id = str(uuid.uuid4())[:8]
        logger.error(f"Ошибка обновления: {error_id} - {str(e)}")
        bot.send_message(message.chat.id, f"❌ Ошибка обновления: {str(e)}")


# Функция для отправки напоминаний
def send_reminders():
    try:
        current_time = datetime.datetime.now(timezone)
        logger.info(f"Проверка напоминаний в {current_time}")

        for reservation in reservations_cache:
            if reservation['status'] != 'Активна':
                continue

            # Проверяем наличие chat_id
            if not reservation.get('chat_id'):
                logger.info(f"Пропуск брони {reservation['id']}: отсутствует chat_id")
                continue

            # Напоминание за 15 минут до начала
            time_until_start = (reservation['start'] - current_time).total_seconds() / 60
            if 14 <= time_until_start <= 16:  # Диапазон для надежности
                message = (
                    f"⏰ Напоминание!\n\n"
                    f"Через 15 минут начинается ваша бронь тележки:\n"
                    f"🛒 Тележка: {reservation['cart']}\n"
                    f"⏰ Время: {reservation['start'].strftime('%H:%M')} - {reservation['end'].strftime('%H:%M')}\n"
                    f"🔒 Код замка: {carts_cache[reservation['cart']]['lock_code']}\n\n"
                    f"Не забудьте взять тележку!"
                )
                try:
                    bot.send_message(reservation['chat_id'], message)
                except Exception as e:
                    logger.error(f"Ошибка отправки напоминания: {str(e)}")

            # Напоминание за 15 минут до окончания
            time_until_end = (reservation['end'] - current_time).total_seconds() / 60
            if time_until_end == 15:
                message = (
                    f"⏰ Напоминание!\n\n"
                    f"Через 15 минут заканчивается ваша бронь тележки:\n"
                    f"🛒 Тележка: {reservation['cart']}\n"
                    f"⏰ Окончание в: {reservation['end'].strftime('%H:%M')}\n\n"
                    f"Не забудьте вернуть тележку и сделать фото!"
                )
                try:
                    bot.send_message(reservation['chat_id'], message)
                except Exception as e:
                    logger.error(f"Ошибка отправки напоминания: {str(e)}")

    except Exception as e:
        logger.error(f"Ошибка отправки напоминаний: {str(e)}")


# Планировщик для напоминаний
def reminder_scheduler():
    while True:
        schedule.run_pending()
        cleanup_states()  # Очистка устаревших состояний
        time.sleep(60)


def refresh_cache_async():
    """Асинхронное обновление кэша"""
    Thread(target=refresh_cache).start()


# Веб-сервер для UptimeRobot
app = Flask(__name__)


@app.route('/')
def home():
    return "🛒 Бот работает! /start"


@app.route('/ping')
def ping():
    return "OK", 200


@app.errorhandler(500)
def internal_error(e):
    logger.error(f"Flask error: {e}")
    return "Internal server error", 500


def run_flask():
    port = int(os.environ.get('PORT', 8080))
    logger.info(f"Starting web server on port {port}...")
    app.run(host='0.0.0.0', port=port, debug=False, use_reloader=False)


if __name__ == '__main__':
    # Проверка обязательных переменных
    required_envs = ['BOT_TOKEN', 'SPREADSHEET_ID', 'GOOGLE_CREDS']
    missing = [var for var in required_envs if not os.getenv(var)]

    if missing:
        logger.error(f"❌ Отсутствуют переменные окружения: {', '.join(missing)}")
        sys.exit(1)

    # Настраиваем планировщик напоминаний
    schedule.every(5).minutes.do(send_reminders)

    # Запускаем потоки
    refresh_cache()
    Thread(target=reminder_scheduler, daemon=True).start()
    Thread(target=run_flask, daemon=True).start()

    # Запускаем бота
    try:
        logger.info("🤖 Starting Telegram bot...")
        bot.infinity_polling()
    except Exception as e:
        logger.error(f"❌ Bot crashed: {e}")
        traceback.print_exc()