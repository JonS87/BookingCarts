#!/bin/bash

# Переходим в папку проекта
cd /home/EvgeniyC87/BookingCarts

# Активируем виртуальное окружение
source venv/bin/activate

# Запускаем бота
python main.py >> bot.log 2>&1