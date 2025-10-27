# multiuser_bot.py
# -*- coding: utf-8 -*-
"""
Многопользовательский Poker Monitor Bot - v7.0
С базой данных, изолированными сессиями, красивым интерфейсом,
ConcurrencyManager и динамическим управлением типами игр
"""

import os
import re
import sys
import json
import time
import random
import sqlite3
import pathlib
import datetime as dt
import asyncio
from typing import Dict, Tuple, List, Optional, Set
from collections import defaultdict
from dataclasses import dataclass, field
from urllib.parse import urlparse, parse_qs
from contextlib import contextmanager

import pandas as pd
import pytz
from dotenv import load_dotenv

from google.auth.transport.requests import Request as GoogleRequest
from google.oauth2.credentials import Credentials
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError

from playwright.async_api import (
    async_playwright,
    Page,
    Browser,
    BrowserContext,
    Route,
    Request,
)

from telegram import Update, InlineKeyboardMarkup, InlineKeyboardButton
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    ContextTypes,
    JobQueue,
    CallbackQueryHandler,
    MessageHandler,
    ConversationHandler,
    filters,
)

load_dotenv()

# ====================== Constants ======================

DB_FILE = "users.db"
DEFAULT_INTERVAL_MIN = 15
REPORT_DIVIDER = "\n" + "═" * 45 + "\n"
TG_CHUNK = 3800
REFRESH_CACHE_TTL_MIN = 3  # Кэш refresh на 3 минуты (минимум)
REFRESH_CACHE_TTL_MAX = 5  # Кэш refresh на 5 минут (максимум)

# Google Sheets API settings
SCOPES = ['https://www.googleapis.com/auth/spreadsheets.readonly']
CREDENTIALS_FILE = 'credentials.json'
TOKEN_FILE = 'token.json'

# Основной пользователь для групповых команд
MAIN_USER_ID = 8480800405  # Все команды в группах работают с источниками этого пользователя


# ====================== Concurrency Manager ======================

@dataclass
class RefreshCacheEntry:
    """Запись о последнем обновлении страницы"""
    timestamp: float
    ttl_minutes: int = 3

@dataclass
class ScrapeTask:
    """Задача парсинга с блокировкой"""
    url: str
    uid: str
    lock: asyncio.Lock = field(default_factory=asyncio.Lock)
    future: Optional[asyncio.Future] = None
    result: Optional[List[dict]] = None

class ConcurrencyManager:
    """
    Менеджер конкурентного доступа:
    - Кэширует время обновления страниц (НЕ результаты парсинга!)
    - Управляет очередями парсинга (чтобы не было дублирующихся операций)
    - Приоритет активным операциям (если парсинг идет, все ждут)
    """
    def __init__(self):
        # Кэш обновлений страниц: {(user_id, site): RefreshCacheEntry}
        self.refresh_cache: Dict[Tuple[int, str], RefreshCacheEntry] = {}
        # Активные задачи парсинга: {(url, uid): ScrapeTask}
        self.scrape_tasks: Dict[Tuple[str, str], ScrapeTask] = {}
        # Глобальная блокировка для критических секций
        self.global_lock = asyncio.Lock()

    def should_refresh_page(self, user_id: int, site: str) -> bool:
        """Проверить, нужно ли обновлять страницу"""
        key = (user_id, site)
        if key not in self.refresh_cache:
            return True

        entry = self.refresh_cache[key]
        elapsed = time.time() - entry.timestamp
        return elapsed > (entry.ttl_minutes * 60)

    def mark_page_refreshed(self, user_id: int, site: str, ttl_minutes: int = REFRESH_CACHE_TTL_MIN):
        """Отметить, что страница была обновлена"""
        key = (user_id, site)
        self.refresh_cache[key] = RefreshCacheEntry(
            timestamp=time.time(),
            ttl_minutes=ttl_minutes
        )

    async def get_or_create_scrape_task(self, url: str, uid: str) -> ScrapeTask:
        """Получить или создать задачу парсинга"""
        key = (url, uid)
        async with self.global_lock:
            if key not in self.scrape_tasks:
                self.scrape_tasks[key] = ScrapeTask(url=url, uid=uid)
            return self.scrape_tasks[key]

    async def execute_scrape(self, task: ScrapeTask, scrape_func) -> List[dict]:
        """
        Выполнить парсинг с блокировкой.
        Если парсинг уже идет, ждем его результата.
        Приоритет активной операции - все остальные ждут!
        """
        # Пытаемся захватить блокировку
        if task.lock.locked():
            # Парсинг уже идет, ждем результата
            print(f"⏳ Парсинг уже выполняется для {task.url}/{task.uid}, ожидаем...")
            async with task.lock:
                # Когда блокировка освободилась, результат уже готов
                return task.result or []

        # Мы первые - выполняем парсинг
        async with task.lock:
            print(f"🔄 Начинаю парсинг для {task.url}/{task.uid}")
            try:
                result = await scrape_func()
                task.result = result
                return result
            except Exception as e:
                print(f"❌ Ошибка парсинга: {e}")
                task.result = []
                raise
            finally:
                # Очищаем задачу после выполнения
                key = (task.url, task.uid)
                async with self.global_lock:
                    if key in self.scrape_tasks:
                        del self.scrape_tasks[key]

# Глобальный менеджер конкурентности
concurrency_manager = ConcurrencyManager()

# ====================== Google Sheets OAuth2 ======================

def get_google_sheets_service():
    """
    Получить сервис Google Sheets API с OAuth2 авторизацией.

    При первом запуске открывает браузер для авторизации.
    Сохраняет токен в token.json для последующего использования.
    Автоматически обновляет токен при необходимости.

    Returns:
        Google Sheets API service object
    """
    creds = None

    # Проверяем существующий токен
    if os.path.exists(TOKEN_FILE):
        creds = Credentials.from_authorized_user_file(TOKEN_FILE, SCOPES)

    # Если токена нет или он недействителен
    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            # Обновляем токен
            print("🔄 Обновление Google API токена...")
            creds.refresh(GoogleRequest())
        else:
            # Первая авторизация - открываем браузер
            if not os.path.exists(CREDENTIALS_FILE):
                raise FileNotFoundError(
                    f"Файл {CREDENTIALS_FILE} не найден! "
                    "Пожалуйста, скачайте credentials.json из Google Cloud Console."
                )

            print("🔐 Требуется авторизация Google Sheets API...")
            print("Сейчас откроется браузер для авторизации.")
            flow = InstalledAppFlow.from_client_secrets_file(CREDENTIALS_FILE, SCOPES)
            # Используем prompt='consent' чтобы всегда получать refresh_token
            creds = flow.run_local_server(
                port=0,
                prompt='consent'
            )

        # Сохраняем токен для будущего использования
        with open(TOKEN_FILE, 'w') as token:
            token.write(creds.to_json())
        print("✅ Токен сохранен в token.json")

    try:
        service = build('sheets', 'v4', credentials=creds)
        return service
    except HttpError as error:
        print(f"❌ Ошибка Google Sheets API: {error}")
        raise

def read_google_sheet(spreadsheet_id: str, range_name: str = 'A:Z') -> pd.DataFrame:
    """
    Прочитать Google таблицу через API.

    Args:
        spreadsheet_id: ID таблицы из URL
        range_name: Диапазон ячеек (по умолчанию все колонки A:Z)

    Returns:
        pandas DataFrame с данными таблицы
    """
    try:
        service = get_google_sheets_service()

        # Получаем данные из таблицы
        sheet = service.spreadsheets()
        result = sheet.values().get(spreadsheetId=spreadsheet_id, range=range_name).execute()
        values = result.get('values', [])

        if not values:
            # Пустая таблица
            return pd.DataFrame()

        # Конвертируем в DataFrame без заголовков (как в CSV варианте)
        df = pd.DataFrame(values)
        return df

    except HttpError as error:
        print(f"❌ Ошибка чтения таблицы {spreadsheet_id}: {error}")
        raise

def extract_spreadsheet_id(url: str) -> Optional[str]:
    """
    Извлечь ID таблицы из URL Google Sheets.

    Поддерживает оба формата:
    - https://docs.google.com/spreadsheets/d/SPREADSHEET_ID/edit...
    - https://docs.google.com/spreadsheets/d/SPREADSHEET_ID/export?format=csv...

    Args:
        url: URL Google таблицы

    Returns:
        ID таблицы или None если не удалось извлечь
    """
    # Паттерн для извлечения ID из любого URL Google Sheets
    pattern = r'/spreadsheets/d/([a-zA-Z0-9-_]+)'
    match = re.search(pattern, url)
    if match:
        return match.group(1)
    return None

def extract_gid_from_url(url: str) -> Optional[str]:
    """
    Извлечь GID (ID листа) из URL Google Sheets.

    Примеры:
    - https://docs.google.com/spreadsheets/d/ID/edit?gid=123#gid=123 -> "123"
    - https://docs.google.com/spreadsheets/d/ID/export?format=csv&gid=123 -> "123"

    Args:
        url: URL Google таблицы

    Returns:
        GID как строка или None если не найден
    """
    # Ищем gid в параметрах URL или в хэше
    patterns = [
        r'[?&]gid=([0-9]+)',  # ?gid=123 или &gid=123
        r'#gid=([0-9]+)',      # #gid=123
    ]

    for pattern in patterns:
        match = re.search(pattern, url)
        if match:
            return match.group(1)

    return None

def get_sheet_name_by_gid(spreadsheet_id: str, gid: str) -> Optional[str]:
    """
    Получить название листа по его GID.

    Args:
        spreadsheet_id: ID таблицы
        gid: GID листа

    Returns:
        Название листа или None если не найден
    """
    try:
        service = get_google_sheets_service()
        spreadsheet = service.spreadsheets().get(spreadsheetId=spreadsheet_id).execute()

        for sheet in spreadsheet.get('sheets', []):
            sheet_props = sheet.get('properties', {})
            if str(sheet_props.get('sheetId')) == str(gid):
                return sheet_props.get('title')

        return None
    except Exception as e:
        print(f"⚠️ Ошибка получения имени листа для gid={gid}: {e}")
        return None

def read_sheet_smart(sheet_url: str) -> pd.DataFrame:
    """
    Умное чтение Google таблицы - пробует API, откатывается на CSV при ошибке.

    Сначала пытается использовать Google Sheets API (работает для приватных таблиц).
    Если это не удается (нет авторизации, таблица публичная, и т.д.),
    откатывается на старый метод чтения через CSV export.

    Поддерживает чтение конкретного листа по gid из URL.

    Args:
        sheet_url: URL таблицы (любой формат Google Sheets)

    Returns:
        pandas DataFrame с данными
    """
    # Извлекаем ID таблицы и gid листа
    spreadsheet_id = extract_spreadsheet_id(sheet_url)
    gid = extract_gid_from_url(sheet_url)

    if spreadsheet_id:
        try:
            # Пробуем читать через API
            if gid:
                print(f"📊 Чтение таблицы через Google Sheets API: {spreadsheet_id} (лист gid={gid})")
                # Получаем название листа по gid
                sheet_name = get_sheet_name_by_gid(spreadsheet_id, gid)
                if sheet_name:
                    print(f"   📄 Лист: {sheet_name}")
                    df = read_google_sheet(spreadsheet_id, f"{sheet_name}!A:AZ")
                else:
                    print(f"⚠️ Не найден лист с gid={gid}, читаю первый лист")
                    df = read_google_sheet(spreadsheet_id, "A:AZ")
            else:
                print(f"📊 Чтение таблицы через Google Sheets API: {spreadsheet_id}")
                df = read_google_sheet(spreadsheet_id, "A:AZ")
            return df
        except Exception as e:
            # Если API не работает, используем CSV
            print(f"⚠️ Не удалось прочитать через API ({e}), откатываемся на CSV...")

    # Откатываемся на CSV метод
    # Конвертируем URL в CSV export формат если нужно
    if '/export?' not in sheet_url:
        if spreadsheet_id:
            # Используем gid если есть, иначе gid=0
            gid_param = gid if gid else "0"
            sheet_url = f"https://docs.google.com/spreadsheets/d/{spreadsheet_id}/export?format=csv&gid={gid_param}"
        else:
            print(f"⚠️ Не удалось извлечь ID таблицы из URL: {sheet_url}")

    print(f"📄 Чтение таблицы через CSV export (публичная таблица)")
    return pd.read_csv(sheet_url, header=None)

# ====================== Database ======================

class Database:
    def __init__(self, db_file=DB_FILE):
        self.db_file = db_file
        self.init_db()

    @contextmanager
    def get_connection(self):
        conn = sqlite3.connect(self.db_file)
        conn.row_factory = sqlite3.Row
        try:
            yield conn
            conn.commit()
        except:
            conn.rollback()
            raise
        finally:
            conn.close()

    def init_db(self):
        with self.get_connection() as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS users (
                    user_id INTEGER PRIMARY KEY,
                    username TEXT,
                    first_name TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    interval_min INTEGER DEFAULT 15,
                    use_icons INTEGER DEFAULT 1,
                    parsing_active INTEGER DEFAULT 0,
                    gg_login TEXT,
                    gg_password TEXT,
                    ebp_login TEXT,
                    ebp_password TEXT,
                    fish_login TEXT,
                    fish_password TEXT
                )
            """)

            # Добавляем колонку parsing_active если её нет (для существующих БД)
            try:
                conn.execute("ALTER TABLE users ADD COLUMN parsing_active INTEGER DEFAULT 0")
            except sqlite3.OperationalError:
                pass  # Колонка уже существует

            # Добавляем колонку group_chat_id если её нет (для существующих БД)
            try:
                conn.execute("ALTER TABLE users ADD COLUMN group_chat_id INTEGER")
            except sqlite3.OperationalError:
                pass  # Колонка уже существует


            conn.execute("""
                CREATE TABLE IF NOT EXISTS sources (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    name TEXT NOT NULL,
                    site TEXT NOT NULL,
                    base_url TEXT NOT NULL,
                    unique_id TEXT NOT NULL,
                    sheet_url TEXT NOT NULL,
                    mode TEXT NOT NULL,
                    enabled INTEGER DEFAULT 1,
                    auth_state_file TEXT,
                    group_id INTEGER,
                    interval_minutes INTEGER DEFAULT 15,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    FOREIGN KEY (user_id) REFERENCES users(user_id)
                )
            """)

            # Добавляем новые колонки если их нет (для существующих БД)
            try:
                conn.execute("ALTER TABLE sources ADD COLUMN group_id INTEGER")
            except sqlite3.OperationalError:
                pass  # Колонка уже существует

            try:
                conn.execute("ALTER TABLE sources ADD COLUMN interval_minutes INTEGER DEFAULT 15")
            except sqlite3.OperationalError:
                pass  # Колонка уже существует

            try:
                conn.execute("ALTER TABLE sources ADD COLUMN last_checked_at TIMESTAMP")
            except sqlite3.OperationalError:
                pass  # Колонка уже существует

    def get_user(self, user_id: int) -> Optional[dict]:
        with self.get_connection() as conn:
            row = conn.execute("SELECT * FROM users WHERE user_id = ?", (user_id,)).fetchone()
            return dict(row) if row else None

    def create_user(self, user_id: int, username: str = None, first_name: str = None):
        with self.get_connection() as conn:
            conn.execute("""
                INSERT OR IGNORE INTO users (user_id, username, first_name)
                VALUES (?, ?, ?)
            """, (user_id, username, first_name))

    def update_user_credentials(self, user_id: int, site: str, login: str, password: str):
        with self.get_connection() as conn:
            if site == "clubgg":
                conn.execute("UPDATE users SET gg_login = ?, gg_password = ? WHERE user_id = ?",
                           (login, password, user_id))
            elif site == "fishpoker":
                conn.execute("UPDATE users SET fish_login = ?, fish_password = ? WHERE user_id = ?",
                           (login, password, user_id))
            else:  # ebpoker
                conn.execute("UPDATE users SET ebp_login = ?, ebp_password = ? WHERE user_id = ?",
                           (login, password, user_id))

    def get_next_available_id(self) -> int:
        """Find the lowest available ID, reusing deleted IDs to avoid gaps"""
        with self.get_connection() as conn:
            # Get all existing IDs
            rows = conn.execute("SELECT id FROM sources ORDER BY id").fetchall()
            existing_ids = [row['id'] for row in rows]

            # If no sources exist, start from 1
            if not existing_ids:
                return 1

            # Find the first gap in the sequence
            for i in range(1, existing_ids[-1] + 1):
                if i not in existing_ids:
                    return i

            # No gaps, use next ID after the highest
            return existing_ids[-1] + 1

    def add_source(self, user_id: int, name: str, site: str, base_url: str,
                   unique_id: str, sheet_url: str, mode: str, auth_state_file: str = None):
        with self.get_connection() as conn:
            # Get the next available ID (reusing deleted IDs)
            next_id = self.get_next_available_id()

            conn.execute("""
                INSERT INTO sources (id, user_id, name, site, base_url, unique_id, sheet_url, mode, auth_state_file)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (next_id, user_id, name, site, base_url, unique_id, sheet_url, mode, auth_state_file))

    def get_user_sources(self, user_id: int, enabled_only: bool = False) -> List[dict]:
        with self.get_connection() as conn:
            query = "SELECT * FROM sources WHERE user_id = ?"
            if enabled_only:
                query += " AND enabled = 1"
            rows = conn.execute(query, (user_id,)).fetchall()
            return [dict(row) for row in rows]

    def get_source_by_id(self, source_id: int) -> Optional[dict]:
        with self.get_connection() as conn:
            row = conn.execute("SELECT * FROM sources WHERE id = ?", (source_id,)).fetchone()
            return dict(row) if row else None

    def get_group_sources(self, group_id: int, enabled_only: bool = False) -> List[dict]:
        """Get all sources for a group"""
        with self.get_connection() as conn:
            query = "SELECT * FROM sources WHERE group_id = ?"
            if enabled_only:
                query += " AND enabled = 1"
            rows = conn.execute(query, (group_id,)).fetchall()
            return [dict(row) for row in rows]

    def remove_source(self, user_id: int, source_id: int) -> bool:
        with self.get_connection() as conn:
            cursor = conn.execute("DELETE FROM sources WHERE id = ? AND user_id = ?",
                                 (source_id, user_id))
            return cursor.rowcount > 0

    def toggle_source(self, user_id: int, source_id: int) -> bool:
        with self.get_connection() as conn:
            conn.execute("""
                UPDATE sources
                SET enabled = 1 - enabled
                WHERE id = ? AND user_id = ?
            """, (source_id, user_id))
            return True

    def set_interval(self, user_id: int, minutes: int):
        with self.get_connection() as conn:
            conn.execute("UPDATE users SET interval_min = ? WHERE user_id = ?",
                        (minutes, user_id))

    def toggle_icons(self, user_id: int) -> bool:
        with self.get_connection() as conn:
            row = conn.execute("SELECT use_icons FROM users WHERE user_id = ?",
                              (user_id,)).fetchone()
            new_val = 0 if row['use_icons'] else 1
            conn.execute("UPDATE users SET use_icons = ? WHERE user_id = ?",
                        (new_val, user_id))
            return bool(new_val)

    def set_icons(self, user_id: int, value: bool):
        """Set icons state for user"""
        with self.get_connection() as conn:
            conn.execute("UPDATE users SET use_icons = ? WHERE user_id = ?",
                        (1 if value else 0, user_id))

    def set_parsing_active(self, user_id: int, active: bool):
        """Установить статус активности парсинга для пользователя"""
        with self.get_connection() as conn:
            conn.execute("UPDATE users SET parsing_active = ? WHERE user_id = ?",
                        (1 if active else 0, user_id))

    def is_parsing_active(self, user_id: int) -> bool:
        """Проверить активен ли парсинг для пользователя"""
        with self.get_connection() as conn:
            row = conn.execute("SELECT parsing_active FROM users WHERE user_id = ?",
                              (user_id,)).fetchone()
            return bool(row['parsing_active']) if row else False

    def set_group_chat_id(self, user_id: int, group_chat_id: Optional[int]):
        """Установить ID группы для отправки сообщений"""
        with self.get_connection() as conn:
            conn.execute("UPDATE users SET group_chat_id = ? WHERE user_id = ?",
                        (group_chat_id, user_id))

    def get_group_chat_id(self, user_id: int) -> Optional[int]:
        """Получить ID группы для пользователя"""
        with self.get_connection() as conn:
            row = conn.execute("SELECT group_chat_id FROM users WHERE user_id = ?",
                              (user_id,)).fetchone()
            return row['group_chat_id'] if row and row['group_chat_id'] else None

    def get_all_users_with_sources(self) -> List[int]:
        """Get users with active sources"""
        with self.get_connection() as conn:
            rows = conn.execute("""
                SELECT DISTINCT user_id FROM sources WHERE enabled = 1
            """).fetchall()
            return [row['user_id'] for row in rows]

    def get_all_users(self) -> List[int]:
        """Get all registered users"""
        with self.get_connection() as conn:
            rows = conn.execute("SELECT user_id FROM users").fetchall()
            return [row['user_id'] for row in rows]

    def set_source_group(self, source_id: int, group_id: Optional[int]):
        """Привязать источник к группе или отвязать (None)"""
        with self.get_connection() as conn:
            conn.execute("UPDATE sources SET group_id = ? WHERE id = ?", (group_id, source_id))

    def get_sources_by_group(self, group_id: int, enabled_only: bool = False) -> List[dict]:
        """Получить все источники группы"""
        with self.get_connection() as conn:
            query = "SELECT * FROM sources WHERE group_id = ?"
            params = [group_id]
            if enabled_only:
                query += " AND enabled = 1"
            rows = conn.execute(query, params).fetchall()
            return [dict(row) for row in rows]

    def set_source_interval(self, source_id: int, minutes: int):
        """Установить интервал для источника и обновить время проверки к текущему моменту"""
        with self.get_connection() as conn:
            conn.execute(
                "UPDATE sources SET interval_minutes = ?, last_checked_at = ? WHERE id = ?",
                (minutes, dt.datetime.now().isoformat(), source_id)
            )

    def get_source_interval(self, source_id: int) -> int:
        """Получить интервал источника"""
        with self.get_connection() as conn:
            row = conn.execute("SELECT interval_minutes FROM sources WHERE id = ?", (source_id,)).fetchone()
            return row['interval_minutes'] if row else 15

    def set_source_last_checked(self, source_id: int):
        """Обновить время последней проверки источника"""
        with self.get_connection() as conn:
            conn.execute(
                "UPDATE sources SET last_checked_at = ? WHERE id = ?",
                (dt.datetime.now().isoformat(), source_id)
            )

    def get_source_last_checked(self, source_id: int) -> Optional[dt.datetime]:
        """Получить время последней проверки источника"""
        with self.get_connection() as conn:
            row = conn.execute("SELECT last_checked_at FROM sources WHERE id = ?", (source_id,)).fetchone()
            if row and row['last_checked_at']:
                return dt.datetime.fromisoformat(row['last_checked_at'])
            return None


db = Database()

# ====================== Helper Functions ======================

def norm(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").strip()).lower()

def to_csv_export(url: str) -> str:
    if "/export" in url and "format=csv" in url:
        return url
    m = re.search(r"/spreadsheets/d/([a-zA-Z0-9-_]+)", url)
    if not m:
        return url
    doc_id = m.group(1)
    gid = "0"
    if "#gid=" in url:
        gid = url.split("#gid=")[-1].split("&")[0]
    elif "?gid=" in url or "&gid=" in url:
        qs = urlparse(url).query
        qd = parse_qs(qs)
        if "gid" in qd and qd["gid"]:
            gid = qd["gid"][0]
    return f"https://docs.google.com/spreadsheets/d/{doc_id}/export?format=csv&gid={gid}"

def plural_ru(n: int, forms: Tuple[str, str, str]) -> str:
    nabs = abs(n) % 100
    n1 = nabs % 10
    if 10 < nabs < 20:
        return forms[2]
    if 1 == n1:
        return forms[0]
    if 2 <= n1 <= 4:
        return forms[1]
    return forms[2]

def format_live_inline(n: int, use_icons: bool) -> str:
    if n <= 0:
        return ""
    if use_icons:
        return " " + "\U0001f464" * n
    else:
        return f", {n} {plural_ru(n, ('живой игрок', 'живых игрока', 'живых игроков'))}"

def format_live_stat(n: int, use_icons: bool) -> str:
    if n <= 0:
        return ""
    if use_icons:
        return ", " + "\U0001f464" * n
    else:
        return f", +{n} {plural_ru(n, ('живой игрок', 'живых игрока', 'живых игроков'))}"

def chunk_text(s: str, limit: int = TG_CHUNK) -> List[str]:
    parts, cur = [], ""
    for ln in s.splitlines(True):
        if len(cur) + len(ln) > limit:
            parts.append(cur)
            cur = ln
        else:
            cur += ln
    if cur.strip():
        parts.append(cur)
    return parts

def tz_now(tz_name: str) -> dt.datetime:
    return dt.datetime.now(pytz.timezone(tz_name))

# ====================== Google Sheets Parsers ======================

HH_RE = re.compile(r"^\s*(\d{1,2})(?::\d{2})?\s*$", re.IGNORECASE)
TIME_RX = re.compile(
    r"^\s*(?:Time\s+([A-Za-zА-Яа-я]+)|([A-Za-zА-Яа-я]+)\s+Time)\s*$", re.IGNORECASE
)

def _hour_cols_on_row(df: pd.DataFrame, row: int) -> Dict[int, int]:
    col_map: Dict[int, int] = {}
    for j in range(1, df.shape[1]):
        s = str(df.iloc[row, j]).strip()
        m = HH_RE.match(s)
        if m:
            col_map[j] = int(m.group(1)) % 24
    return col_map

def _find_schedule_blocks(df: pd.DataFrame, hour_msk: int):
    header_rows = []
    for i in range(df.shape[0]):
        first = str(df.iloc[i, 0]).strip()
        has_time_word = bool(TIME_RX.match(first)) or first.lower() in (
            "time msk",
            "msk",
            "time (msk)",
            "time",
            "time msc",
        )
        col_map = _hour_cols_on_row(df, i)
        if has_time_word and len(col_map) >= 3:
            header_rows.append((i, col_map))

    if not header_rows:
        for i in range(min(20, df.shape[0])):
            col_map = _hour_cols_on_row(df, i)
            if len(col_map) >= 6:
                header_rows.append((i, col_map))

    blocks = []
    for idx, (row, col_map) in enumerate(header_rows):
        jmax = max(col_map.keys())
        label = ""
        for k in range(jmax + 1, df.shape[1]):
            v = str(df.iloc[row, k]).strip()
            if v and v.lower() not in {"ok", "nan"}:
                label = v
                break

        h = hour_msk % 24
        same = [c for c, hh in col_map.items() if hh == h]
        if same:
            col_hour = same[0]
        else:
            lesser = [c for c, hh in col_map.items() if hh <= h]
            col_hour = (
                max(lesser, key=lambda x: col_map[x]) if lesser else min(col_map.keys())
            )

        hour_print = h
        try:
            raw = str(df.iloc[row, col_hour]).strip()
            mm = re.search(r"(\d{1,2})", raw)
            if mm:
                hour_print = int(mm.group(1))
        except:
            pass

        start = row + 1
        stop = header_rows[idx + 1][0] if idx + 1 < len(header_rows) else df.shape[0]
        blocks.append(
            {
                "row": row,
                "col_hour": col_hour,
                "start": start,
                "stop": stop,
                "hour_print": hour_print,
                "label": label,
            }
        )
    return blocks

def schedule_clubgg_blocks(csv_url: str, hour_msk: int):
    """
    Парсит расписание для ClubGG с поддержкой нового формата.

    Теперь поддерживает два формата:
    1. Полное название стола (старый формат)
    2. "Название ТИП ЛИМИТ" (новый формат) - например "Global NLH 0.05/0.1$ NLH 10"

    Returns список блоков, где каждый блок содержит:
    - rows: список словарей с полями {raw, name, game, limit, plan, key}
    - hour_print: время в формате "HH:00"
    - label: метка блока (например "Morning")
    """
    df = read_sheet_smart(csv_url)
    blocks_meta = _find_schedule_blocks(df, hour_msk)
    blocks = []
    for b in blocks_meta:
        rows = []
        for i in range(b["start"], b["stop"]):
            raw = df.iloc[i, 0]
            if pd.isna(raw):
                continue
            label = str(raw).strip()
            if not label or label.lower() in ("итого", "total"):
                continue

            # Парсим название стола на компоненты
            table_name, game_type, limit = parse_table_name(label)

            # Получаем количество ботов из расписания
            val = df.iloc[i, b["col_hour"]]
            bots = 0
            try:
                if pd.notna(val):
                    bots = int(float(str(val).replace(",", ".")))
            except:
                bots = 0

            # Ключ для сопоставления - нормализованное полное название
            key = norm(label)

            rows.append({
                "raw": label,          # Оригинальное название из таблицы
                "name": table_name,    # Название без типа и лимита
                "game": game_type,     # Тип игры (NLH, PLO и т.д.)
                "limit": limit,        # Лимит
                "plan": max(0, bots),  # Количество ботов по плану
                "key": key,            # Нормализованный ключ для поиска
            })
        blocks.append((rows, b["hour_print"], b["label"]))
    return blocks

def parse_type_limit(label: str) -> Tuple[str, int]:
    """Парсит тип игры и лимит из строки (УСТАРЕЛО - используйте parse_table_name)"""
    s = re.sub(r"\s+", " ", str(label or "")).strip()
    if not s:
        return "", 0
    numbers = re.findall(r"\d+", s)
    if not numbers:
        return "", 0
    limit = int(numbers[-1])
    last_num_match = None
    for m in re.finditer(r"\d+", s):
        last_num_match = m
    if not last_num_match:
        return "", 0
    text_before_limit = s[: last_num_match.start()].strip()
    words = text_before_limit.split()
    if not words:
        return "", 0
    gtype = re.sub(r"[^A-Za-z0-9]", "", words[-1]).upper()
    return gtype, limit

def parse_table_name(label: str) -> Tuple[str, str, int]:
    """
    Унифицированная функция парсинга названия стола.

    Формат: "Название игры ТИП ЛИМИТ"
    Пример: "Global NLH 0.05/0.1$ NLH 10" -> ("Global NLH 0.05/0.1$", "NLH", 10)

    Логика:
    - Последнее число - это лимит
    - Предпоследнее слово (перед лимитом) - это тип игры
    - Все остальное - название

    Returns:
        Tuple[name, game_type, limit] где:
        - name: полное название стола (без типа и лимита)
        - game_type: тип игры (NLH, PLO, и т.д.)
        - limit: лимит стола
    """
    s = re.sub(r"\s+", " ", str(label or "")).strip()
    if not s:
        return "", "", 0

    # Находим все числа в строке
    numbers = re.findall(r"\d+", s)
    if not numbers:
        return s, "", 0  # Если нет чисел, возвращаем как есть

    # Последнее число - это лимит
    limit = int(numbers[-1])

    # Находим позицию последнего числа
    last_num_match = None
    for m in re.finditer(r"\d+", s):
        last_num_match = m

    if not last_num_match:
        return s, "", 0

    # Берем текст до последнего числа
    text_before_limit = s[: last_num_match.start()].strip()
    words = text_before_limit.split()

    if not words:
        return "", "", limit

    # Последнее слово перед лимитом - это тип игры
    gtype = re.sub(r"[^A-Za-z0-9]", "", words[-1]).upper()

    # Все что до типа игры - это название
    if len(words) > 1:
        name = " ".join(words[:-1])
    else:
        name = ""

    return name, gtype, limit

def schedule_diamond_blocks(csv_url: str, hour_msk: int):
    """
    Парсит расписание для Diamond/FishPoker/EBPoker с поддержкой названий столов.

    Теперь поддерживает два формата:
    1. Только тип и лимит: "NLH 100"
    2. С названием: "Holdem 500/1000 UZS NLH 100" -> название="Holdem 500/1000 UZS", тип="NLH", лимит=100
    """
    df = read_sheet_smart(csv_url)
    meta = _find_schedule_blocks(df, hour_msk)
    blocks = []
    for b in meta:
        rows = []
        for i in range(b["start"], b["stop"]):
            label = str(df.iloc[i, 0]).strip()
            if not label or label.lower() in ("итого", "total", "nan"):
                continue

            # Используем новую функцию парсинга
            table_name, gtype, limit = parse_table_name(label)

            if not gtype or not limit:
                continue

            # Читаем размер стола из второго столбца (если есть)
            raw_size = df.iloc[i, 1] if df.shape[1] > 1 else 6
            try:
                size = (
                    int(float(str(raw_size).replace(",", ".")))
                    if pd.notna(raw_size)
                    else 6
                )
            except:
                size = 6

            # Читаем план из столбца с текущим часом
            plan = None
            try:
                val = df.iloc[i, b["col_hour"]]
                if pd.notna(val) and str(val).strip() != "":
                    plan = int(float(str(val).replace(",", ".")))
            except:
                plan = None

            rows.append(
                {
                    "name": table_name,    # Название стола (может быть пустым)
                    "game": gtype,         # Тип игры
                    "limit": int(limit),   # Лимит
                    "size": int(size),     # Размер стола
                    "plan": plan,          # План ботов
                    "raw": label,          # Оригинальная строка
                }
            )
        blocks.append((rows, b["hour_print"], b["label"]))
    return blocks

# ====================== Scraper ======================

TABLE_RE_CLUB = re.compile(
    r"Table name:\s*(?P<name>.+?)\n.*?"
    r"Unique IDs:\s*(?P<uid>.+?)\n.*?"
    r"Players:\s*(?P<total>\d+)/(?P<cap>\d+)\((?P<bots>\d+)\)",
    re.DOTALL,
)

TABLE_RE_EB = re.compile(
    r"Table name:\s*(?P<name>.+?)\n.*?"
    r"Unique IDs:\s*(?P<uid>.+?)\n.*?"
    r"Table limit:\s*(?P<lim>[\d/\.]+\$?)\n.*?"
    r"Game (?:type|Type):\s*(?P<game>.+?)\n.*?"
    r"Players:\s*(?P<total>\d+)/(?P<cap>\d+)\((?P<bots>\d+)\)\n.*?"
    r"Game started:\s*(?P<started>Yes|No)",
    re.DOTALL | re.IGNORECASE,
)

def parse_limit_to_int(lim: str) -> int:
    lim = str(lim or "")
    m = re.search(r"(\d+)", lim)
    return int(m.group(1)) if m else 0

class SiteClient:
    def __init__(
        self,
        site: str,
        login: str,
        password: str,
        auth_state_file: Optional[str] = None,
    ):
        self.site = site
        self.login = login
        self.password = password
        self.auth_state_file = auth_state_file
        self.play = None
        self.browser: Optional[Browser] = None
        self.ctx: Optional[BrowserContext] = None
        self.page: Optional[Page] = None
        self.headful = str(os.getenv("HEADFUL", "0")).lower() in ("1", "true", "yes")
        try:
            self.slowmo = int(os.getenv("PW_SLOWMO", "0") or 0)
        except:
            self.slowmo = 0
        try:
            self.burger_retry_ms = max(
                50, min(1000, int(os.getenv("BURGER_RETRY_MS", "250")))
            )
        except:
            self.burger_retry_ms = 250
        try:
            self.burger_max_ms = max(
                1000, min(15000, int(os.getenv("BURGER_MAX_MS", "5000")))
            )
        except:
            self.burger_max_ms = 5000
        self.tables_ready_selector = ".ActiveTables-Component .TableInfo-Component"
        self.filter_applied = False
        # Отслеживание применённых типов игр
        self.applied_game_types: set = set()

    async def _route_filter(self, route: Route, request: Request):
        rtype = request.resource_type
        if rtype in ("image", "font", "media"):
            await route.abort()
        else:
            await route.continue_()

    async def _is_tables_open(self) -> bool:
        try:
            await self.page.wait_for_selector(self.tables_ready_selector, timeout=200)
            return True
        except:
            return False

    async def _click_burger_safe_once(self):
        sels = [
            "button.sidebar-button",
            "button:has(.pi.pi-bars)",
            ".pi.pi-bars",
            "//button[contains(@class,'sidebar-button')]",
            "//span[contains(@class,'pi-bars')]",
        ]
        for sel in sels:
            try:
                loc = self.page.locator(sel).first
                if await loc.count() > 0:
                    await loc.click(timeout=1200, force=True)
                    return True
            except:
                continue
        return False

    async def _open_tables_panel_until_ready(self) -> bool:
        t0 = time.monotonic()
        while (time.monotonic() - t0) * 1000 < self.burger_max_ms:
            if await self._is_tables_open():
                return True
            await self._click_burger_safe_once()
            await self.page.wait_for_timeout(self.burger_retry_ms)
        return await self._is_tables_open()

    async def _get_game_types_from_schedule(self, sheet_url: str) -> set:
        """Получить уникальные типы игр из расписания"""
        try:
            df = read_sheet_smart(sheet_url)
            game_types = set()
            for i in range(df.shape[0]):
                label = str(df.iloc[i, 0]).strip()
                if not label or label.lower() in (
                    "итого", "total", "nan", "time msk", "msk", "time", "time (msk)",
                ):
                    continue
                gtype, limit = parse_type_limit(label)
                if gtype:
                    game_types.add(gtype)
            return game_types
        except Exception as e:
            print(f"Ошибка при чтении расписания для фильтра: {e}")
            return set()

    async def _update_game_filter_from_schedules(self, all_sheet_urls: List[str]):
        """
        Обновить фильтр типов игр на основе ВСЕХ расписаний пользователя.
        Собирает типы из всех расписаний и синхронизирует фильтр.
        """
        if not all_sheet_urls:
            return

        # Собираем типы игр из всех расписаний
        all_game_types = set()
        for sheet_url in all_sheet_urls:
            types = await self._get_game_types_from_schedule(to_csv_export(sheet_url))
            all_game_types.update(types)

        if all_game_types:
            print(f"📋 Собрано типов игр из {len(all_sheet_urls)} расписаний: {len(all_game_types)}")
            await self._apply_game_filter(all_game_types)

    async def _apply_game_filter(self, game_types: set):
        """
        Применить фильтр по типам игр (динамически).
        Добавляет новые типы и удаляет неиспользуемые.
        """
        if not game_types:
            return

        # Определяем что добавить и что удалить
        new_types = game_types - self.applied_game_types  # Новые типы для добавления
        removed_types = self.applied_game_types - game_types  # Типы для удаления

        if not new_types and not removed_types:
            print("✓ Фильтр актуален, изменений не требуется")
            return

        try:
            print(f"🔄 Обновляю фильтр типов игр...")
            if new_types:
                print(f"  ➕ Добавляю: {', '.join(sorted(new_types))}")
            if removed_types:
                print(f"  ➖ Удаляю: {', '.join(sorted(removed_types))}")

            # Открываем панель фильтров
            search_icon_selectors = [
                ".pi.pi-search.cursor-pointer",
                "span.pi-search",
                "//span[contains(@class, 'pi-search')]",
            ]
            clicked_search = False
            for selector in search_icon_selectors:
                try:
                    icon = self.page.locator(selector).first
                    if await icon.count() > 0:
                        await icon.click(timeout=3000)
                        await self.page.wait_for_timeout(1000)
                        clicked_search = True
                        print("  ✓ Открыл панель фильтров (лупа)")
                        break
                except:
                    continue
            if not clicked_search:
                print("  ❌ Не удалось найти иконку поиска (лупу)")
                return

            await self.page.wait_for_timeout(800)

            # Открываем мультиселект
            multiselect_selectors = [
                "#game-type",
                "div[id='game-type'].p-multiselect",
                "//label[contains(text(), 'Game type')]/following-sibling::div[contains(@class, 'p-multiselect')]",
            ]
            clicked_multiselect = False
            for selector in multiselect_selectors:
                try:
                    ms = self.page.locator(selector).first
                    if await ms.count() > 0:
                        await ms.click(timeout=3000)
                        await self.page.wait_for_timeout(800)
                        clicked_multiselect = True
                        print("  ✓ Открыл мультиселект Game type")
                        break
                except:
                    continue
            if not clicked_multiselect:
                print("  ❌ Не удалось открыть мультиселект Game type")
                return

            await self.page.wait_for_selector(".p-multiselect-panel", timeout=3000)
            await self.page.wait_for_timeout(500)

            # Если это первый запуск - снимаем все галочки
            if not self.applied_game_types:
                try:
                    select_all_checkbox = self.page.locator(
                        ".p-multiselect-header .p-checkbox"
                    ).first
                    if await select_all_checkbox.count() > 0:
                        classes = await select_all_checkbox.get_attribute("class")
                        if "p-highlight" in (classes or ""):
                            await select_all_checkbox.click(timeout=1000)
                            await self.page.wait_for_timeout(400)
                            print("  ✓ Снял все галочки")
                except Exception as e:
                    print(f"  ⚠️ Предупреждение при снятии галочек: {e}")

            # УДАЛЯЕМ неиспользуемые типы (снимаем галочки)
            for game_type in sorted(removed_types):
                try:
                    item_xpath = f"//li[contains(@class, 'p-multiselect-item')]//span[text()='{game_type}']"
                    item = self.page.locator(item_xpath).first
                    if await item.count() > 0:
                        parent_li = item.locator(
                            "xpath=ancestor::li[contains(@class, 'p-multiselect-item')]"
                        ).first
                        if await parent_li.count() > 0:
                            # Проверяем, выбран ли элемент
                            li_classes = await parent_li.get_attribute("class")
                            if "p-highlight" in (li_classes or ""):
                                await parent_li.click(timeout=1500)
                                await self.page.wait_for_timeout(200)
                                self.applied_game_types.discard(game_type)
                                print(f"    ➖ Удалён: {game_type}")
                except Exception as e:
                    print(f"    ⚠️ Не удалось удалить {game_type}: {e}")

            # ДОБАВЛЯЕМ новые типы (ставим галочки)
            added_count = 0
            for game_type in sorted(new_types):
                try:
                    item_xpath = f"//li[contains(@class, 'p-multiselect-item')]//span[text()='{game_type}']"
                    item = self.page.locator(item_xpath).first
                    if await item.count() > 0:
                        parent_li = item.locator(
                            "xpath=ancestor::li[contains(@class, 'p-multiselect-item')]"
                        ).first
                        if await parent_li.count() > 0:
                            # Проверяем, не выбран ли уже
                            li_classes = await parent_li.get_attribute("class")
                            if "p-highlight" not in (li_classes or ""):
                                await parent_li.click(timeout=1500)
                                await self.page.wait_for_timeout(200)
                                self.applied_game_types.add(game_type)
                                added_count += 1
                                print(f"    ➕ Добавлен: {game_type}")
                except Exception as e:
                    print(f"    ⚠️ Не удалось добавить {game_type}: {e}")

            # Если это первый запуск, добавляем все существующие типы
            if not self.filter_applied:
                for game_type in sorted(game_types):
                    if game_type not in self.applied_game_types:
                        try:
                            item_xpath = f"//li[contains(@class, 'p-multiselect-item')]//span[text()='{game_type}']"
                            item = self.page.locator(item_xpath).first
                            if await item.count() > 0:
                                parent_li = item.locator(
                                    "xpath=ancestor::li[contains(@class, 'p-multiselect-item')]"
                                ).first
                                if await parent_li.count() > 0:
                                    await parent_li.click(timeout=1500)
                                    await self.page.wait_for_timeout(200)
                                    self.applied_game_types.add(game_type)
                                    added_count += 1
                                    print(f"    ✓ Выбран: {game_type}")
                        except Exception as e:
                            print(f"    ⚠️ Не удалось выбрать {game_type}: {e}")

            # Закрываем панель
            await self.page.wait_for_timeout(500)
            try:
                await self.page.keyboard.press("Escape")
                await self.page.wait_for_timeout(500)
            except:
                try:
                    await self.page.click("body", position={"x": 10, "y": 10})
                    await self.page.wait_for_timeout(500)
                except:
                    pass

            self.filter_applied = True
            print(f"✅ Фильтр обновлён! Активно типов игр: {len(self.applied_game_types)}")
            if self.applied_game_types:
                print(f"   Типы: {', '.join(sorted(self.applied_game_types))}")
        except Exception as e:
            print(f"❌ Ошибка при применении фильтра: {e}")

    async def ensure(self, base_url: str, sheet_url: Optional[str] = None, all_sheet_urls: Optional[List[str]] = None):
        """
        Инициализировать браузер.

        Args:
            base_url: URL сайта
            sheet_url: Текущее расписание (для ClubGG)
            all_sheet_urls: Все расписания пользователя для данного сайта (не используется, для совместимости)
        """
        if self.page and not self.page.is_closed():
            return

        for obj, closer in (
            (self.ctx, "close"),
            (self.browser, "close"),
            (self.play, "stop"),
        ):
            try:
                if obj:
                    await getattr(obj, closer)()
            except:
                pass

        if os.environ.get("PWDEBUG"):
            try:
                del os.environ["PWDEBUG"]
            except:
                pass

        self.play = await async_playwright().start()
        self.browser = await self.play.chromium.launch(
            headless=not self.headful,
            slow_mo=self.slowmo,
            args=[
                "--no-sandbox",
                "--disable-gpu",
                "--disable-dev-shm-usage",
                "--disable-background-networking",
                "--disable-background-timer-throttling",
                "--disable-popup-blocking",
                "--disable-renderer-backgrounding",
                "--disable-sync",
                "--no-first-run",
                "--force-color-profile=srgb",
            ],
        )

        ctx_opts = {
            "viewport": {"width": 1360, "height": 900},
            "user_agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
            ),
            "locale": "en-US",
            "timezone_id": os.getenv("TZ", "Europe/Moscow"),
        }

        if self.auth_state_file and pathlib.Path(self.auth_state_file).exists():
            ctx_opts["storage_state"] = self.auth_state_file

        self.ctx = await self.browser.new_context(**ctx_opts)
        await self.ctx.route("**/*", self._route_filter)
        self.page = await self.ctx.new_page()
        await self.page.goto(base_url, wait_until="domcontentloaded", timeout=30000)

        if not await self._is_tables_open():
            try:
                await self.page.wait_for_load_state("domcontentloaded", timeout=15000)
                for sel in [
                    "input[name='login']",
                    "input[autocomplete='username']",
                    "input[type='text']",
                    "input[type='email']",
                ]:
                    try:
                        await self.page.wait_for_selector(
                            sel, timeout=4000, state="visible"
                        )
                        await self.page.fill(sel, self.login, timeout=2000)
                        break
                    except:
                        pass
                for sel in [
                    "input[type='password']",
                    "input[autocomplete='current-password']",
                ]:
                    try:
                        await self.page.wait_for_selector(
                            sel, timeout=4000, state="visible"
                        )
                        await self.page.fill(sel, self.password, timeout=2000)
                        break
                    except:
                        pass
                clicked = False
                for btn in [
                    "button:has-text('Login')",
                    "button:has-text('Log in')",
                    "button:has-text('Sign in')",
                    "button[type='submit']",
                ]:
                    try:
                        if await self.page.locator(btn).first.count() > 0:
                            await self.page.locator(btn).first.click(timeout=3000)
                            clicked = True
                            break
                    except:
                        pass
                if not clicked:
                    try:
                        await self.page.keyboard.press("Enter")
                    except:
                        pass
                if self.auth_state_file:
                    await self.page.wait_for_timeout(2000)
                    await self.ctx.storage_state(path=self.auth_state_file)
            except:
                pass

        await self._open_tables_panel_until_ready()

    async def refresh_page(self):
        if not self.page or self.page.is_closed():
            return
        await self.page.reload(wait_until="domcontentloaded")
        await self._open_tables_panel_until_ready()

    async def close(self):
        for obj, closer in (
            (self.ctx, "close"),
            (self.browser, "close"),
            (self.play, "stop"),
        ):
            try:
                if obj:
                    await getattr(obj, closer)()
            except:
                pass
        self.page = None
        self.ctx = None
        self.browser = None
        self.play = None

    async def scrape(self, base_url: str) -> List[dict]:
        if not self.page or self.page.is_closed():
            raise RuntimeError("Страница не инициализирована. Вызовите ensure() перед scrape()")

        cards = self.page.locator(".ActiveTables-Component .TableInfo-Component")
        n = await cards.count()
        out: List[dict] = []
        for i in range(n):
            root = cards.nth(i)
            try:
                text = await root.inner_text(timeout=5000)  # 5 сек вместо 30
            except:
                # Элемент исчез или не загрузился - пропускаем
                continue

            if self.site in ("ebpoker", "fishpoker"):
                m = TABLE_RE_EB.search(text)
                if not m:
                    continue
                raw_uid = m.group("uid").strip()
                uids = [norm(x) for x in re.split(r"[,;]\s*", raw_uid) if x.strip()]
                total = int(m.group("total"))
                cap = int(m.group("cap"))
                bots = int(m.group("bots"))
                live = max(0, total - bots)
                active = m.group("started").strip().lower() == "yes"
                out.append(
                    {
                        "name": m.group("name").strip(),
                        "uid": raw_uid,
                        "uids": uids,
                        "limit": parse_limit_to_int(m.group("lim")),
                        "game": (m.group("game") or "").strip().upper(),
                        "total": total,
                        "cap": cap,
                        "bots": bots,
                        "live": live,
                        "active": active,
                    }
                )
            else:
                m = TABLE_RE_CLUB.search(text)
                if not m:
                    continue
                total = int(m.group("total"))
                cap = int(m.group("cap"))
                bots = int(m.group("bots"))
                live = max(0, total - bots)
                active = True
                out.append(
                    {
                        "name": m.group("name").strip(),
                        "uid": m.group("uid").strip(),
                        "uids": [norm(m.group("uid").strip())],
                        "limit": None,
                        "game": None,
                        "total": total,
                        "cap": cap,
                        "bots": bots,
                        "live": live,
                        "active": active,
                    }
                )
        return out

# ====================== Reports ======================

def titleize_simple(s: str) -> str:
    t = re.sub(r"\bnlh\b", "NLH", s, flags=re.I)
    t = re.sub(r"\bplo6\b", "PLO6", t, flags=re.I)
    t = re.sub(r"\bplo\b", "PLO", t, flags=re.I)
    t = re.sub(r"\bnlp\b", "NLP", t, flags=re.I)
    t = re.sub(r"\bplo5\b", "PLO5", t, flags=re.I)
    t = re.sub(r"\bplob\b", "PLOB", t, flags=re.I)
    t = re.sub(r"\bofc\b", "OFC", t, flags=re.I)
    parts = []
    for w in t.split():
        parts.append(w if w.isupper() else (w[:1].upper() + w[1:]))
    return " ".join(parts)

def build_report_clubgg(
    source_name: str, sheet_url: str, scraped: List[dict], uid: str, tz_out: str, use_icons: bool
) -> str:
    """
    Создает отчет для ClubGG с улучшенной логикой сопоставления столов.

    Логика сопоставления (в порядке приоритета):
    1. По полному названию стола (нормализованному)
    2. По типу игры + лимиту (если название не найдено)
    """
    hour_msk = tz_now("Europe/Moscow").hour
    blocks = schedule_clubgg_blocks(to_csv_export(sheet_url), hour_msk)
    filt = [r for r in scraped if norm(r["uid"]) == norm(uid)]
    now_text = tz_now(tz_out).strftime("%H:%M")
    parts = []
    grand_plan = 0
    grand_fact = 0

    for rows, hour_print, label in blocks:
        header = f"{source_name} ({now_text} MSK)\nUID: {uid}"
        if label:
            header += f"\nБлок: {label}"
        lines = [header, ""]
        total_plan = 0
        total_actual_bots = 0
        table_lines = []
        issues = []

        # Создаем индексы для быстрого поиска столов
        active_tables_by_name = {norm(r["name"]): r for r in filt if r.get("active", True)}
        inactive_tables_by_name = {norm(r["name"]): r for r in filt if not r.get("active", True)}

        # Для поиска по типу+лимиту парсим названия столов с сайта
        active_tables_by_type_limit = {}
        inactive_tables_by_type_limit = {}
        for r in filt:
            table_full_name = r.get("name", "")
            parsed_name, parsed_game, parsed_limit = parse_table_name(table_full_name)
            if parsed_game and parsed_limit:
                key = (parsed_game, parsed_limit)
                if r.get("active", True):
                    if key not in active_tables_by_type_limit:
                        active_tables_by_type_limit[key] = []
                    active_tables_by_type_limit[key].append(r)
                else:
                    if key not in inactive_tables_by_type_limit:
                        inactive_tables_by_type_limit[key] = []
                    inactive_tables_by_type_limit[key].append(r)

        for row in rows:
            p = row["plan"]
            disp = titleize_simple(row["raw"])
            total_plan += max(0, p)

            # Сначала ищем по полному названию
            r = active_tables_by_name.get(row["key"]) or inactive_tables_by_name.get(row["key"])

            # Если не нашли по названию и есть тип+лимит, ищем по ним
            if r is None and row["game"] and row["limit"]:
                search_key = (row["game"], row["limit"])
                candidates = active_tables_by_type_limit.get(search_key, []) + inactive_tables_by_type_limit.get(search_key, [])
                if candidates:
                    # Берем первый подходящий стол
                    r = candidates[0]
            if r is None:
                if p > 0:
                    prefix = "\u274c " if use_icons else ""
                    table_lines.append(f"{prefix}{disp} — нет стола (план: {p})")
                    stat_prefix = "\u274c " if use_icons else ""
                    issues.append(f"{stat_prefix}{disp}: -{p}")
                continue

            bots = int(r.get("bots") or 0)
            total_actual_bots += bots
            total = int(r.get("total") or 0)
            cap = int(r.get("cap") or 6)
            live = max(0, int(r.get("live") or (total - bots)))
            is_active = r.get("active", True)

            live_str = format_live_inline(live, use_icons)

            # Для ClubGG используем название с сайта (только название, без дублирования)
            site_table_name = r.get("name", "")
            if site_table_name:
                disp = titleize_simple(site_table_name)
            # Если стола нет на сайте, используем то что в таблице (уже в disp)

            if not is_active:
                missing = max(0, p - bots)
                prefix = "\u26a0️ " if use_icons else ""
                table_lines.append(
                    f"{prefix}{disp}: {total}/{cap} ({bots}) план: {p} (неактивный){live_str}"
                )
                stat_prefix = "\u26a0️ " if use_icons else ""
                issues.append(
                    f"{stat_prefix}{disp}: -{missing} (неактивный){format_live_stat(live, use_icons)}"
                )
            elif bots == p and live == 0:
                prefix = "\u2705 " if use_icons else ""
                table_lines.append(f"{prefix}{disp}: {total}/{cap} ({bots}) план: {p}")
            elif bots == p and live > 0:
                # Ботов в норме, но есть живые игроки
                prefix = "\u2705 " if use_icons else ""
                table_lines.append(
                    f"{prefix}{disp}: {total}/{cap} ({bots}) план: {p}{live_str}"
                )
            elif bots < p:
                # Если стол полный, есть живые игроки и ботов = план - живые - это норма
                # (боты вышли, чтобы освободить места живым игрокам)
                if total == cap and live > 0 and bots == p - live:
                    prefix = "\u2705 " if use_icons else ""
                    table_lines.append(
                        f"{prefix}{disp}: {total}/{cap} ({bots}) план: {p}{live_str}"
                    )
                else:
                    # Остальные случаи - реальная ошибка
                    prefix = "\u26a0️ " if use_icons else ""
                    table_lines.append(
                        f"{prefix}{disp}: {total}/{cap} ({bots}) план: {p}{live_str}"
                    )
                    diff = p - bots
                    stat_prefix = "\u26a0️ " if use_icons else ""
                    issues.append(
                        f"{stat_prefix}{disp}: -{diff}{format_live_stat(live, use_icons)}"
                    )
            else:
                # bots > p - лишние боты
                prefix = "\U0001f53c " if use_icons else ""
                table_lines.append(
                    f"{prefix}{disp}: {total}/{cap} ({bots}) план: {p}{live_str}"
                )
                diff = bots - p
                stat_prefix = "\U0001f53c " if use_icons else ""
                issues.append(
                    f"{stat_prefix}{disp}: +{diff} {plural_ru(diff, ('лишний бот', 'лишних бота', 'лишних ботов'))}{format_live_stat(live, use_icons)}"
                )

        lines.extend(table_lines)
        if issues:
            lines.append("")
            lines.append("Статистика по лимитам:")
            lines.extend(issues)
        else:
            lines.append("")
            norm_prefix = "\u2705 " if use_icons else ""
            lines.append(f"{norm_prefix}Посадка в норме")
        lines.append("")
        lines.append(
            f"Итого ботов: {total_actual_bots}/{total_plan} (на {hour_print:02d}:00)"
        )
        parts.append("\n".join(lines))
        grand_plan += total_plan
        grand_fact += total_actual_bots

    if len(parts) > 1:
        parts.append(
            f"Общее количество ботов: {grand_fact}/{grand_plan} (на {blocks[0][1]:02d}:00)"
        )
    return REPORT_DIVIDER.join(parts) if parts else f"\u274c [{source_name}] нет данных"

def build_report_diamond(
    source_name: str, sheet_url: str, scraped: List[dict], uid: str, tz_out: str, use_icons: bool, site: str = "fishpoker"
) -> str:
    hour_msk = tz_now("Europe/Moscow").hour
    blocks = schedule_diamond_blocks(to_csv_export(sheet_url), hour_msk)
    uid_n = norm(uid)
    filt: List[dict] = []
    for r in scraped:
        uids = r.get("uids") or [norm(r.get("uid", ""))]
        if uid_n not in uids:
            continue
        if uid_n == "vader.diamond" and len(uids) != 1:
            continue
        filt.append(r)

    all_used_tables = set()

    # Индексируем столы по (game, limit, size)
    active_by = defaultdict(list)
    inactive_by = defaultdict(list)
    for r in filt:
        key = (
            (r.get("game") or "").upper(),
            int(r.get("limit") or 0),
            int(r.get("cap") or 6),
        )
        (active_by if r.get("active", True) else inactive_by)[key].append(r)
    for d in (active_by, inactive_by):
        for k in d:
            d[k] = sorted(d[k], key=lambda x: int(x.get("bots") or 0), reverse=True)

    # Также индексируем столы по названию (для поиска по названию)
    active_by_name = {norm(r["name"]): r for r in filt if r.get("active", True)}
    inactive_by_name = {norm(r["name"]): r for r in filt if not r.get("active", True)}

    def pop_best(tables: List[dict], target: int) -> Optional[dict]:
        if not tables:
            return None
        best_i, best_key = 0, (10**9, 0)
        for i, r in enumerate(tables):
            b = int(r.get("bots") or 0)
            key = (abs(b - (target or 0)), -b)
            if key < best_key:
                best_key, best_i = key, i
        return tables.pop(best_i)

    now_text = tz_now(tz_out).strftime("%H:%M")
    parts = []
    grand_plan = 0
    grand_fact = 0

    for rows, hour_print, label in blocks:
        header = f"{source_name} ({now_text} MSK)\nUID: {uid}"
        if label:
            header += f"\nБлок: {label}"
        lines = [header, ""]
        total_plan = 0
        total_fact_bots = 0
        table_lines = []
        issues = []

        table_counts = defaultdict(int)
        for r in rows:
            if r["plan"] is not None and r["plan"] > 0:
                key = (r["game"], r["limit"], r["size"])
                table_counts[key] += 1

        for r in rows:
            p = r["plan"]
            if p is None or p == 0:
                continue
            total_plan += max(0, p)
            key = (r["game"], r["limit"], r["size"])

            # Сначала пытаемся найти по названию (если оно указано в расписании)
            chosen = None
            if r.get("name"):  # Если есть название стола
                # Составляем полное название для поиска: название + тип + лимит
                full_name_key = norm(r["name"] + " " + r["game"] + " " + str(r["limit"]))

                # Ищем точное совпадение по полному названию
                chosen = active_by_name.get(full_name_key)
                if not chosen or id(chosen) in all_used_tables:
                    # Если не нашли точное совпадение, пробуем искать частичное
                    # Может быть на сайте название уже содержит тип и лимит
                    for table_name_norm, table in active_by_name.items():
                        if id(table) in all_used_tables:
                            continue
                        # Проверяем: содержит ли название с сайта нужное название, тип и лимит
                        if (r["name"] and norm(r["name"]) in table_name_norm and
                            r["game"] and norm(r["game"]) in table_name_norm and
                            str(r["limit"]) in table_name_norm):
                            chosen = table
                            break

            # Если не нашли по названию, ищем по типу+лимиту+размеру
            if chosen is None:
                chosen = pop_best(active_by[key], p)
            if chosen:
                all_used_tables.add(id(chosen))
                bots = int(chosen.get("bots") or 0)
                total_fact_bots += bots
                total = int(chosen.get("total") or 0)
                cap = int(chosen.get("cap") or r["size"])
                live = max(0, total - bots)
                live_str = format_live_inline(live, use_icons)

                # Формируем отображаемое имя
                # Для EBPoker: показываем то что в таблице
                # Для FishPoker: название с сайта + тип + лимит
                if site == "ebpoker":
                    # EBPoker: используем то что написано в таблице
                    if r.get("name"):
                        display_name = f"{r['name']} {r['game']} {r['limit']}"
                        stats_name = f"{r['name']} {r['game']} {r['limit']} {r['size']}max"
                    else:
                        display_name = f"{r['game']} {r['limit']}"
                        stats_name = f"{r['game']} {r['limit']} {r['size']}max"
                else:
                    # FishPoker: название с сайта + тип + лимит
                    site_table_name = chosen.get("name", "")
                    if site_table_name:
                        display_name = f"{site_table_name} {r['game']} {r['limit']}"
                        stats_name = f"{site_table_name} {r['game']} {r['limit']} {r['size']}max"
                    elif r.get("name"):
                        display_name = f"{r['name']} {r['game']} {r['limit']}"
                        stats_name = f"{r['name']} {r['game']} {r['limit']} {r['size']}max"
                    else:
                        display_name = f"{r['game']} {r['limit']}"
                        stats_name = f"{r['game']} {r['limit']} {r['size']}max"

                if bots == p and live == 0:
                    prefix = "\u2705 " if use_icons else ""
                    table_lines.append(
                        f"{prefix}{display_name}: {total}/{cap} ({bots}) план: {p}"
                    )
                elif bots == p and live > 0:
                    # Ботов в норме, но есть живые игроки
                    prefix = "\u2705 " if use_icons else ""
                    table_lines.append(
                        f"{prefix}{display_name}: {total}/{cap} ({bots}) план: {p}{live_str}"
                    )
                elif bots < p:
                    # Если стол полный, есть живые игроки и ботов = план - живые - это норма
                    # (боты вышли, чтобы освободить места живым игрокам)
                    if total == cap and live > 0 and bots == p - live:
                        prefix = "\u2705 " if use_icons else ""
                        table_lines.append(
                            f"{prefix}{display_name}: {total}/{cap} ({bots}) план: {p}{live_str}"
                        )
                    else:
                        # Остальные случаи - реальная ошибка
                        prefix = "\u26a0️ " if use_icons else ""
                        table_lines.append(
                            f"{prefix}{display_name}: {total}/{cap} ({bots}) план: {p}{live_str}"
                        )
                        diff = p - bots
                        stat_prefix = "\u26a0️ " if use_icons else ""
                        issues.append(
                            f"{stat_prefix}{stats_name}: -{diff}{format_live_stat(live, use_icons)}"
                        )
                else:
                    # bots > p - лишние боты
                    prefix = "\U0001f53c " if use_icons else ""
                    table_lines.append(
                        f"{prefix}{display_name}: {total}/{cap} ({bots}) план: {p}{live_str}"
                    )
                    diff = bots - p
                    stat_prefix = "\U0001f53c " if use_icons else ""
                    issues.append(
                        f"{stat_prefix}{stats_name}: +{diff} {plural_ru(diff, ('лишний бот', 'лишних бота', 'лишних ботов'))}{format_live_stat(live, use_icons)}"
                    )
                continue

            chosen = pop_best(inactive_by[key], p)
            if chosen:
                all_used_tables.add(id(chosen))
                bots = int(chosen.get("bots") or 0)
                cap = int(chosen.get("cap") or r["size"])
                total_missing = max(0, p - bots)

                # Формируем имя для неактивных столов
                if site == "ebpoker":
                    # EBPoker: то что в таблице
                    if r.get("name"):
                        display_name = f"{r['name']} {r['game']} {r['limit']}"
                        stats_name = f"{r['name']} {r['game']} {r['limit']} {r['size']}max"
                    else:
                        display_name = f"{r['game']} {r['limit']}"
                        stats_name = f"{r['game']} {r['limit']} {r['size']}max"
                else:
                    # FishPoker: название с сайта + тип + лимит
                    site_table_name = chosen.get("name", "")
                    if site_table_name:
                        display_name = f"{site_table_name} {r['game']} {r['limit']}"
                        stats_name = f"{site_table_name} {r['game']} {r['limit']} {r['size']}max"
                    elif r.get("name"):
                        display_name = f"{r['name']} {r['game']} {r['limit']}"
                        stats_name = f"{r['name']} {r['game']} {r['limit']} {r['size']}max"
                    else:
                        display_name = f"{r['game']} {r['limit']}"
                        stats_name = f"{r['game']} {r['limit']} {r['size']}max"

                prefix = "\u26a0️ " if use_icons else ""
                table_lines.append(
                    f"{prefix}{display_name}: {chosen['total']}/{cap} ({bots}) план: {p} (неактивный)"
                )
                stat_prefix = "\u26a0️ " if use_icons else ""
                issues.append(
                    f"{stat_prefix}{stats_name}: -{total_missing} (неактивный)"
                )
                continue

            count = table_counts[key]
            # Для отсутствующих столов используем название из расписания
            if r.get("name"):
                display_name = f"{r['name']} {r['game']} {r['limit']}"
                stats_name = f"{r['name']} {r['game']} {r['limit']} {r['size']}max"
            else:
                display_name = f"{r['game']} {r['limit']}"
                stats_name = f"{r['game']} {r['limit']} {r['size']}max"

            prefix = "\u274c " if use_icons else ""
            if count > 1:
                table_lines.append(
                    f"{prefix}{stats_name} — нет {count} {plural_ru(count, ('стола', 'столов', 'столов'))} (план: {p})"
                )
            else:
                table_lines.append(
                    f"{prefix}{display_name} — нет стола (план: {p})"
                )
            stat_prefix = "\u274c " if use_icons else ""
            issues.append(f"{stat_prefix}{stats_name}: -{p}")

        lines.extend(table_lines)
        if issues:
            lines.append("")
            lines.append("Статистика по лимитам:")
            lines.extend(issues)
        else:
            lines.append("")
            norm_prefix = "\u2705 " if use_icons else ""
            lines.append(f"{norm_prefix}Посадка в норме")
        lines.append("")
        lines.append(
            f"Итого ботов: {total_fact_bots}/{total_plan} (на {hour_print:02d}:00)"
        )
        grand_plan += total_plan
        grand_fact += total_fact_bots
        parts.append("\n".join(lines))

    global_extras = []
    prefix = "\u274c " if use_icons else ""
    for key, rest in active_by.items():
        for t in rest:
            if id(t) not in all_used_tables:
                global_extras.append(
                    f"{prefix}{key[0]} {key[1]} {key[2]}max — лишний стол"
                )
                grand_fact += int(t.get("bots") or 0)
                all_used_tables.add(id(t))

    for key, rest in inactive_by.items():
        for t in rest:
            if id(t) not in all_used_tables:
                global_extras.append(
                    f"{prefix}{key[0]} {key[1]} {key[2]}max — лишний неактивный"
                )
                all_used_tables.add(id(t))

    if global_extras:
        extra_section = [""]
        extra_section.extend(global_extras)
        parts.append("\n".join(extra_section))

    if len(blocks) > 1 or global_extras:
        parts.append(
            f"Общее количество ботов: {grand_fact}/{grand_plan} (на {blocks[0][1]:02d}:00)"
        )

    return REPORT_DIVIDER.join(parts) if parts else f"\u274c [{source_name}] нет данных"

# ====================== Multi-user Runner ======================

class MultiUserRunner:
    def __init__(self):
        self.tz_out = os.getenv("TZ", "Europe/Moscow")
        # Клиенты для каждого пользователя: {user_id: {site: SiteClient}}
        self.user_clients: Dict[int, Dict[str, SiteClient]] = {}

    def _get_or_create_client(
        self, user_id: int, site: str, login: str, password: str, auth_state_file: Optional[str] = None
    ) -> SiteClient:
        if user_id not in self.user_clients:
            self.user_clients[user_id] = {}

        if site not in self.user_clients[user_id]:
            self.user_clients[user_id][site] = SiteClient(
                site, login, password, auth_state_file
            )

        return self.user_clients[user_id][site]

    async def snapshot_source(self, user_id: int, source: dict) -> str:
        """Snapshot one source"""
        user = db.get_user(user_id)
        if not user:
            return "\u274c Пользователь не найден"

        site = source["site"].lower()
        uid = source["unique_id"]
        auth_state = source.get("auth_state_file")
        sheet_url = source.get("sheet_url")

        # Получить креды пользователя
        if site == "clubgg":
            login = user.get("gg_login") or os.getenv("GG_LOGIN", "")
            password = user.get("gg_password") or os.getenv("GG_PASSWORD", "")
        elif site == "fishpoker":
            login = user.get("fish_login") or os.getenv("FISH_LOGIN", "")
            password = user.get("fish_password") or os.getenv("FISH_PASSWORD", "")
        else:  # ebpoker
            login = user.get("ebp_login") or os.getenv("EBP_LOGIN", "")
            password = user.get("ebp_password") or os.getenv("EBP_PASSWORD", "")

        if not login or not password:
            return f"\u274c [{source['name']}] Не указаны логин/пароль для {site}"

        try:
            # Собираем все расписания пользователя для данного сайта
            all_sources = db.get_user_sources(user_id, enabled_only=True)
            all_sheet_urls_for_site = [
                s["sheet_url"] for s in all_sources
                if s["site"].lower() == site and s.get("sheet_url")
            ]

            client = self._get_or_create_client(user_id, site, login, password, auth_state)

            # Собираем нужные типы игр из расписаний
            needed_game_types = set()
            for sheet_url in all_sheet_urls_for_site:
                types = await client._get_game_types_from_schedule(to_csv_export(sheet_url))
                needed_game_types.update(types)

            if needed_game_types:
                print(f"🎯 Ищу {len(needed_game_types)} типов: {', '.join(sorted(needed_game_types))}")

            # Проверяем нужно ли обновлять страницу (кэш)
            should_refresh = concurrency_manager.should_refresh_page(user_id, site)

            # Гарантируем что страница инициализирована
            if client.page is None or client.page.is_closed():
                print(f"🔄 Страница закрыта. Инициализирую для {site}")
                await client.ensure(source["base_url"], sheet_url, all_sheet_urls_for_site)
                concurrency_manager.mark_page_refreshed(user_id, site)
            elif should_refresh:
                print(f"🔄 Обновляю страницу для {site} (кэш истек)")
                await client.refresh_page()
                await client.page.wait_for_load_state("domcontentloaded", timeout=10000)
                await client._open_tables_panel_until_ready()
                concurrency_manager.mark_page_refreshed(user_id, site)
            else:
                print(f"✓ Использую кэшированную страницу для {site}")

            # Используем ConcurrencyManager для парсинга
            task = await concurrency_manager.get_or_create_scrape_task(source["base_url"], uid)
            scraped = await concurrency_manager.execute_scrape(
                task,
                lambda: client.scrape(source["base_url"])
            )

            # Фильтруем результаты по нужным типам игр
            if needed_game_types and site in ("ebpoker", "fishpoker"):
                filtered_scraped = [
                    table for table in scraped
                    if table.get("game") in needed_game_types
                ]
                print(f"📊 Отфильтровано: {len(scraped)} → {len(filtered_scraped)} столов")
                scraped = filtered_scraped

            use_icons = bool(user.get("use_icons", 1))

            if site == "clubgg":
                return build_report_clubgg(
                    source["name"], source["sheet_url"], scraped, uid, self.tz_out, use_icons
                )
            else:
                return build_report_diamond(
                    source["name"], source["sheet_url"], scraped, uid, self.tz_out, use_icons, site
                )
        except Exception as e:
            return f"\u274c [{source['name']}] ошибка: {e}"

    async def snapshot_user_sources(self, user_id: int) -> List[Tuple[str, str, str, int]]:
        """Snapshot all user sources

        Returns:
            List of tuples (source_name, report_text, site_type, source_id)
        """
        sources = db.get_user_sources(user_id, enabled_only=True)
        if not sources:
            return []

        reports = []
        for source in sources:
            try:
                report = await self.snapshot_source(user_id, source)
                reports.append((source["name"], report, source["site"], source["id"]))
            except Exception as e:
                reports.append((source["name"], f"\u274c [{source['name']}] ошибка: {e}", source["site"], source["id"]))

        return reports

    async def refresh_user_clients(self, user_id: int) -> List[str]:
        """Refresh all user browsers"""
        msgs = []
        if user_id in self.user_clients:
            for site, client in self.user_clients[user_id].items():
                try:
                    await client.refresh_page()
                    msgs.append(f"\u2705 {site} обновлён")
                except Exception as e:
                    msgs.append(f"\u26a0️ {site}: {e}")
        return msgs if msgs else ["\u26a0️ Нет открытых браузеров"]

    async def close_site_client(self, user_id: int, site: str):
        """Close browser for specific site"""
        if user_id in self.user_clients and site in self.user_clients[user_id]:
            await self.user_clients[user_id][site].close()
            del self.user_clients[user_id][site]
            # Если это был последний браузер пользователя, удаляем запись
            if not self.user_clients[user_id]:
                del self.user_clients[user_id]

    async def close_user_clients(self, user_id: int):
        """Close all user browsers"""
        if user_id in self.user_clients:
            for client in self.user_clients[user_id].values():
                await client.close()
            del self.user_clients[user_id]

    async def close_all(self):
        """Close all browsers"""
        for user_id in list(self.user_clients.keys()):
            await self.close_user_clients(user_id)

runner = MultiUserRunner()

# Глобальная переменная для application (нужна для cancel_user_job в callbacks)
app_instance = None

# ====================== Telegram Handlers ======================

WAITING_SITE, WAITING_UID, WAITING_SHEET, WAITING_NAME, WAITING_CHANGE_SOURCE, WAITING_NEW_TABLE = range(6)

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Welcome message"""
    user = update.effective_user
    db.create_user(user.id, user.username, user.first_name)

    welcome_text = f"""\U0001f3b0 <b>Добро пожаловать в Poker Monitor Bot!</b>

Привет, {user.first_name}! \U0001f44b

<b>Что умеет этот бот:</b>
• Мониторит столы на покерных сайтах
• Парсит расписание из Google Sheets
• Отправляет отчёты по вашему расписанию
• Поддерживает ClubGG, FishPoker, EBPoker

<b>Быстрый старт:</b>
1️⃣ Настройте первый источник: /setup
2️⃣ Или добавьте вручную: /add
3️⃣ Проверьте результат: /check

<b>Полезные команды:</b>
/setup - Пошаговая настройка (рекомендуется!)
/help - Полная справка по командам
/list - Ваши источники
/check - Проверить столы сейчас
/settings - Ваши настройки

<b>Нужна помощь?</b>
Нажмите /tutorial для подробного гайда!

Готовы начать? Нажмите кнопку ниже! \U0001f447"""

    keyboard = [
        [InlineKeyboardButton("\U0001f680 Быстрая настройка", callback_data="quick_setup")],
        [InlineKeyboardButton("\U0001f4d6 Подробный гайд", callback_data="tutorial")],
        [InlineKeyboardButton("\u2699️ Настройки", callback_data="user_settings")],
    ]

    await update.message.reply_text(
        welcome_text,
        parse_mode='HTML',
        reply_markup=InlineKeyboardMarkup(keyboard)
    )

async def cmd_tutorial(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Tutorial"""
    tutorial_text = """\U0001f4da <b>ПОДРОБНЫЙ ГАЙД ПО НАСТРОЙКЕ</b>

<b>Как работает парсер:</b>

1️⃣ <b>Google Sheets</b>
   Создайте таблицу с расписанием ботов:
   - Первая колонка: название столов/лимиты
   - Остальные колонки: часы (0, 1, 2... 23)
   - В ячейках: количество ботов на этот час

   Пример:
   | Стол      | 0 | 1 | 2 | 3 |
   |-----------|---|---|---|---|
   | NLH 100   | 5 | 3 | 2 | 0 |
   | PLO 50    | 2 | 2 | 2 | 1 |

2️⃣ <b>Получите ссылку на таблицу</b>
   Сделайте таблицу доступной по ссылке

3️⃣ <b>Узнайте UID вашего аккаунта</b>
   Зайдите на сайт покер-рума, найдите свой
   уникальный идентификатор (обычно в профиле)

4️⃣ <b>Добавьте источник в бота:</b>
   /setup - пошаговая настройка (рекомендуется)
   /add &lt;site&gt; &lt;uid&gt; &lt;sheet_url&gt; &lt;name&gt; - вручную

<b>Поддерживаемые сайты:</b>
• clubgg - ClubGG Poker
• fishpoker - FishPoker
• ebpoker - EB Poker / Diamond

<b>🆕 РАБОТА В ГРУППАХ:</b>
1. Добавьте бота в группу
2. В личке добавьте свои источники
3. В группе введите /setgroup - источники привязаны!
4. Теперь все в группе видят ваши источники
5. Каждый может управлять любым источником

<b>Настройка интервалов:</b>
• /interval 30 - для ВСЕХ источников
• /interval 1 15 - для источника #1 (15 минут)

<b>Отвязка от группы:</b>
/setgroup disable - источники вернутся в личку

Готовы добавить первый источник?
Используйте /setup для пошаговой настройки!"""

    if update.callback_query:
        await update.callback_query.message.reply_text(tutorial_text, parse_mode='HTML')
    else:
        await update.message.reply_text(tutorial_text, parse_mode='HTML')

async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Help message"""
    help_text = """<b>\U0001f4cb СПРАВКА ПО КОМАНДАМ</b>

<b>\U0001f3af Основные:</b>
/start - Главное меню
/tutorial - Подробный гайд
/help - Эта справка

<b>\U0001f527 Настройка источников:</b>
/setup - Пошаговая настройка
/add &lt;site&gt; &lt;uid&gt; &lt;url&gt; &lt;name&gt; - Добавить источник
/list - Список ваших источников
/del &lt;id&gt; - Удалить источник
/toggle &lt;id или название&gt; - Вкл/выкл источник

<b>\U0001f4ca Проверка:</b>
/check - Проверить все источники
/check &lt;id или название&gt; - Проверить конкретный

<b>\u2699️ Настройки интервалов:</b>
/interval - Показать текущие интервалы
/interval &lt;минуты&gt; - Установить для ВСЕХ источников
/interval &lt;id&gt; &lt;минуты&gt; - Установить для конкретного

<b>\U0001f465 Работа в группах:</b>
/setgroup - Привязать источники к группе
/setgroup disable - Отвязать от группы
В группе все участники видят и управляют источниками!

<b>\U0001f504 Управление:</b>
/refresh - Обновить браузеры
/stop_parsing - Остановить парсинг
/icons - Переключить иконки/текст

<b>Примеры:</b>

Добавить ClubGG:
/add clubgg vader.ClubGG https://docs... Мой ClubGG

Интервал 30 мин для всех:
/interval 30

Интервал 15 мин для источника #1:
/interval 1 15

Проверить источник #2:
/check 2"""

    keyboard = [
        [InlineKeyboardButton("\U0001f680 Начать настройку", callback_data="quick_setup")],
        [InlineKeyboardButton("\U0001f4d6 Подробный гайд", callback_data="tutorial")],
    ]

    await update.message.reply_text(
        help_text,
        parse_mode='HTML',
        reply_markup=InlineKeyboardMarkup(keyboard)
    )

async def cmd_list(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """List sources - группо-осознанная версия"""
    chat_type = update.effective_chat.type
    chat_id = update.effective_chat.id
    user_id = get_effective_user_id(update)

    # Определяем источники: из группы или из личного кабинета
    if chat_type in ['group', 'supergroup']:
        sources = db.get_group_sources(chat_id)
        header = "📋 ИСТОЧНИКИ ГРУППЫ:"
    else:
        sources = db.get_user_sources(user_id)
        header = "📋 ВАШИ ИСТОЧНИКИ:"

    if not sources:
        if chat_type in ['group', 'supergroup']:
            text = """\U0001f4ed <b>В этой группе пока нет источников</b>

Добавьте первый источник:
• /setgroup - Привязать свои источники к группе
• /add - Добавить новый источник в группу"""
        else:
            text = """\U0001f4ed <b>У вас пока нет источников</b>

Добавьте первый источник:
• /setup - Пошаговая настройка
• /add - Добавить вручную
• /tutorial - Подробный гайд"""

        keyboard = [
            [InlineKeyboardButton("\U0001f680 Начать настройку", callback_data="quick_setup")],
        ]
        await update.message.reply_text(text, parse_mode='HTML',
                                       reply_markup=InlineKeyboardMarkup(keyboard))
        return

    text = f"<b>{header}</b>\n\n"

    for s in sources:
        status = "\u2705" if s['enabled'] else "\u23f8"
        interval = s.get('interval_minutes', 15)
        owner_id = s.get('user_id')
        owner_name = "Unknown"

        # Получаем имя владельца
        if owner_id:
            owner = db.get_user(owner_id)
            if owner:
                # Пробуем: username → first_name → ID
                owner_name = owner.get('username') or owner.get('first_name') or str(owner_id)
            else:
                owner_name = f"User {owner_id}"

        text += f"{status} <b>#{s['id']}</b> {s['name']}\n"
        text += f"   • Сайт: {s['site']}\n"
        text += f"   • Интервал: {interval} мин\n"
        text += f"   • UID: <code>{s['unique_id']}</code>\n"

        if chat_type in ['group', 'supergroup']:
            text += f"   • Владелец: {owner_name}\n"

        text += "\n"

    text += "<b>Управление:</b>\n"
    text += "/toggle &lt;id&gt; - Вкл/выкл\n"
    text += "/interval &lt;id&gt; &lt;мин&gt; - Установить интервал\n"
    text += "/del &lt;id&gt; - Удалить\n"
    text += "/check &lt;id&gt; - Проверить конкретный"

    keyboard = [
        [InlineKeyboardButton("\u2795 Добавить", callback_data="quick_setup")],
        [InlineKeyboardButton("\u2705 Проверить все", callback_data="check_all")],
    ]

    await update.message.reply_text(text, parse_mode='HTML',
                                   reply_markup=InlineKeyboardMarkup(keyboard))

async def cmd_settings(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """User settings"""
    user_id = get_effective_user_id(update)  # В группе = MAIN_USER_ID, в личке = ID отправителя
    user = db.get_user(user_id)

    if not user:
        await update.message.reply_text("Ошибка: пользователь не найден")
        return

    icon_status = "\U0001f465 Иконками" if user['use_icons'] else "\U0001f4dd Текстом"

    text = f"""<b>\u2699️ ВАШИ НАСТРОЙКИ</b>

<b>Интервал проверки:</b> {user['interval_min']} минут
<b>Отображение живых игроков:</b> {icon_status}

<b>Изменить настройки:</b>
/interval &lt;минуты&gt; - Интервал (1-1440)
/icons - Переключить отображение

<b>Активных источников:</b> {len(db.get_user_sources(user_id, enabled_only=True))}
<b>Всего источников:</b> {len(db.get_user_sources(user_id))}"""

    keyboard = [
        [InlineKeyboardButton("\U0001f504 Интервал", callback_data="change_interval")],
        [InlineKeyboardButton(f"\U0001f3a8 {icon_status}", callback_data="toggle_icons")],
        [InlineKeyboardButton("\U0001f4cb Мои источники", callback_data="list_sources")],
    ]

    if update.callback_query:
        await update.callback_query.message.reply_text(text, parse_mode='HTML',
                                       reply_markup=InlineKeyboardMarkup(keyboard))
    else:
        await update.message.reply_text(text, parse_mode='HTML',
                                       reply_markup=InlineKeyboardMarkup(keyboard))

async def on_site_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle site selection buttons for ConversationHandler"""
    query = update.callback_query
    await query.answer()

    if query.data.startswith("site_"):
        site = query.data.replace("site_", "")
        context.user_data['setup_site'] = site

        site_names = {
            'clubgg': 'ClubGG',
            'fishpoker': 'FishPoker',
            'ebpoker': 'EBPoker/Diamond'
        }

        text = f"""<b>\U0001f680 МАСТЕР НАСТРОЙКИ</b>

Выбран сайт: <b>{site_names[site]}</b> \u2705

Шаг 2 из 4: Введите UID

Отправьте ваш уникальный идентификатор (UID) на сайте {site_names[site]}.

<i>Пример: vader.ClubGG_AID_3132</i>

Отмена: /cancel"""

        await query.edit_message_text(text, parse_mode='HTML')
        return WAITING_UID

async def on_change_table_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle change_table button - show user's sources"""
    query = update.callback_query
    await query.answer()

    user_id = get_effective_user_id(update)
    sources = db.get_user_sources(user_id)

    if not sources:
        await query.edit_message_text(
            "\U0001f4ed У вас нет источников для изменения.\n\n"
            "Сначала добавьте источник через /setup",
            parse_mode='HTML'
        )
        return ConversationHandler.END

    # Create buttons for each source
    keyboard = []
    for source in sources:
        site_emoji = {
            'clubgg': '\U0001f3b2',
            'fishpoker': '\U0001f41f',
            'ebpoker': '\U0001f48e'
        }.get(source['site'], '\U0001f3b2')

        keyboard.append([
            InlineKeyboardButton(
                f"{site_emoji} {source['name']} (ID: {source['id']})",
                callback_data=f"change_source_{source['id']}"
            )
        ])

    keyboard.append([InlineKeyboardButton("\u274c Отмена", callback_data="cancel_setup")])

    text = """<b>\U0001f4dd ИЗМЕНИТЬ ТАБЛИЦУ</b>

Выберите источник, для которого хотите обновить ссылку на расписание:"""

    await query.edit_message_text(
        text,
        parse_mode='HTML',
        reply_markup=InlineKeyboardMarkup(keyboard)
    )
    return WAITING_CHANGE_SOURCE

async def on_source_select_for_table_change(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle source selection for table change"""
    query = update.callback_query
    await query.answer()

    if query.data.startswith("change_source_"):
        source_id = int(query.data.replace("change_source_", ""))
        context.user_data['change_table_source_id'] = source_id

        # Get source info
        user_id = get_effective_user_id(update)
        sources = db.get_user_sources(user_id)
        source = next((s for s in sources if s['id'] == source_id), None)

        if not source:
            await query.edit_message_text("\u274c Источник не найден")
            return ConversationHandler.END

        text = f"""<b>\U0001f4dd ИЗМЕНИТЬ ТАБЛИЦУ</b>

Источник: <b>{source['name']}</b>
Текущая таблица: <code>{source['sheet_url']}</code>

Отправьте новую ссылку на Google Таблицу с расписанием.

<i>Пример: https://docs.google.com/spreadsheets/d/...</i>

Отмена: /cancel"""

        await query.edit_message_text(text, parse_mode='HTML')
        return WAITING_NEW_TABLE

async def on_new_table_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle new table URL input"""
    new_table_url = update.message.text.strip()
    source_id = context.user_data.get('change_table_source_id')

    if not source_id:
        await update.message.reply_text("\u274c Ошибка: источник не выбран")
        return ConversationHandler.END

    # Validate URL
    if not new_table_url.startswith('http'):
        await update.message.reply_text(
            "\u274c Неверный формат ссылки. Ссылка должна начинаться с http:// или https://\n\n"
            "Попробуйте еще раз или /cancel для отмены"
        )
        return WAITING_NEW_TABLE

    # Update source in database
    user_id = get_effective_user_id(update)
    sources = db.get_user_sources(user_id)
    source = next((s for s in sources if s['id'] == source_id), None)

    if not source:
        await update.message.reply_text("\u274c Источник не найден")
        return ConversationHandler.END

    # Update sheet_url
    with db.get_connection() as conn:
        conn.execute(
            "UPDATE sources SET sheet_url = ? WHERE id = ?",
            (new_table_url, source_id)
        )

    await update.message.reply_text(
        f"""\u2705 <b>Таблица обновлена!</b>

Источник: <b>{source['name']}</b>
Новая таблица: <code>{new_table_url}</code>

Изменения вступят в силу при следующей проверке.""",
        parse_mode='HTML'
    )

    # Clear context
    context.user_data.pop('change_table_source_id', None)

    return ConversationHandler.END

async def start_setup(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Setup wizard start"""
    keyboard = [
        [InlineKeyboardButton("\U0001f3b2 ClubGG", callback_data="site_clubgg")],
        [InlineKeyboardButton("\U0001f41f FishPoker", callback_data="site_fishpoker")],
        [InlineKeyboardButton("\U0001f48e EBPoker/Diamond", callback_data="site_ebpoker")],
        [InlineKeyboardButton("\U0001f4dd Изменить таблицу", callback_data="change_table")],
        [InlineKeyboardButton("\u274c Отмена", callback_data="cancel_setup")],
    ]

    text = """<b>\U0001f680 МАСТЕР НАСТРОЙКИ</b>

Шаг 1 из 4: Выберите покер-рум

Какой сайт вы хотите добавить?

Или выберите "Изменить таблицу" для обновления расписания существующего источника."""

    query = update.callback_query
    if query:
        await query.answer()
        await query.edit_message_text(text, parse_mode='HTML',
                                     reply_markup=InlineKeyboardMarkup(keyboard))
    else:
        await update.message.reply_text(text, parse_mode='HTML',
                                       reply_markup=InlineKeyboardMarkup(keyboard))

    return WAITING_SITE

# ====================== Helper Functions ======================

def get_effective_user_id(update: Update) -> int:
    """
    Определить эффективный ID пользователя для команды.

    В группах: всегда используем MAIN_USER_ID (основной пользователь)
    В личных сообщениях: используем ID отправителя команды

    Args:
        update: Telegram Update object

    Returns:
        ID пользователя, чьи источники нужно использовать
    """
    # Определяем тип чата
    if update.callback_query:
        # Для callback (кнопок) берем чат из сообщения
        chat_type = update.callback_query.message.chat.type
    else:
        # Для обычных сообщений
        chat_type = update.effective_chat.type

    # В группах и супергруппах используем основного пользователя
    if chat_type in ['group', 'supergroup']:
        return MAIN_USER_ID

    # В личке используем ID отправителя
    return update.effective_user.id

# ====================== Commands ======================

async def cmd_check(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Check sources - группо-осознанная версия"""
    chat_id = update.effective_chat.id
    chat_type = update.effective_chat.type
    user_id = get_effective_user_id(update)

    # Определяем источники: из группы или из личного кабинета
    if chat_type in ['group', 'supergroup']:
        # В группе проверяем источники всей группы
        sources = db.get_group_sources(chat_id, enabled_only=True)
        is_group = True
    else:
        # В личке проверяем источники пользователя
        sources = db.get_user_sources(user_id, enabled_only=True)
        is_group = False

    if not sources:
        await update.message.reply_text(
            "\U0001f4ed Нет активных источников.\n\n"
            "В группе: используйте /setgroup чтобы добавить источники\n"
            "В личке: используйте /setup чтобы добавить источники"
        )
        return

    # Активируем автоматический парсинг для пользователя (делаем это СРАЗУ)
    db.set_parsing_active(user_id, True)

    # Создаём job если его еще нет (первый запуск)
    if context.application and context.application.job_queue:
        job_name = f"auto_check_{user_id}"
        existing_jobs = context.application.job_queue.get_jobs_by_name(job_name)
        if not existing_jobs:
            schedule_user_job(context.application, user_id)

    # Проверка конкретного источника по ID, названию или сайту
    if context.args:
        query = " ".join(context.args).lower()
        matched_sources = []

        # Сначала пробуем найти по ID (если query - это число)
        try:
            source_id = int(query)
            for s in sources:
                if s['id'] == source_id:
                    matched_sources.append(s)
                    break
        except ValueError:
            pass  # Не число, ищем дальше

        # Если не нашли по ID, пробуем найти по сайту
        if not matched_sources:
            for s in sources:
                if s['site'].lower() == query:
                    matched_sources.append(s)

        # Если не нашли по сайту, ищем по названию
        if not matched_sources:
            for s in sources:
                if query in s['name'].lower():
                    matched_sources.append(s)

        if not matched_sources:
            await update.message.reply_text(
                f"\u274c Не найдено источников с ID, названием или сайтом '{query}'\n\n"
                f"Используйте /list чтобы посмотреть все источники"
            )
            return

        # Проверяем найденные источники
        await update.message.reply_text(
            f"\U0001f504 Найдено {len(matched_sources)} {plural_ru(len(matched_sources), ('источник', 'источника', 'источников'))}. Проверяю..."
        )

        for source in matched_sources:
            try:
                # Получаем владельца источника для проверки
                owner_id = source.get('user_id', user_id)
                report = await runner.snapshot_source(owner_id, source)
                chunks = list(chunk_text(report))
                for i, chunk in enumerate(chunks):
                    # Добавляем кнопку только к последнему чанку
                    keyboard = None
                    if i == len(chunks) - 1:
                        keyboard = InlineKeyboardMarkup([
                            [InlineKeyboardButton(
                                f"\U0001f504 Проверить {source['name']}",
                                callback_data=f"refresh_source_{source['id']}"
                            )]
                        ])
                    await update.message.reply_text(chunk, reply_markup=keyboard)
            except Exception as e:
                await update.message.reply_text(
                    f"\u274c Ошибка при проверке {source['name']}: {e}"
                )
        return

    # Проверка всех источников
    await update.message.reply_text(
        f"\U0001f504 Проверяю {len(sources)} {plural_ru(len(sources), ('источник', 'источника', 'источников'))}..."
    )

    # Для группы проверяем все источники этой группы
    # Для лички проверяем все источники пользователя
    if is_group:
        # В группе нужно проверить все источники разных пользователей
        for source in sources:
            try:
                owner_id = source.get('user_id', user_id)
                report = await runner.snapshot_source(owner_id, source)
                chunks = list(chunk_text(report))
                for chunk in chunks:
                    await update.message.reply_text(chunk)
            except Exception as e:
                await update.message.reply_text(
                    f"\u274c Ошибка при проверке {source['name']}: {e}"
                )
    else:
        # В личке используем текущее поведение
        reports = await runner.snapshot_user_sources(user_id)
        for source_name, report_text, site_type, source_id in reports:
            for chunk in chunk_text(report_text):
                await update.message.reply_text(chunk)

async def cmd_refresh(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Refresh browsers"""
    user_id = get_effective_user_id(update)  # В группе = MAIN_USER_ID, в личке = ID отправителя
    try:
        msgs = await runner.refresh_user_clients(user_id)
        response = "\n".join(msgs)
        response += (
            "\n\n💡 <b>Рекомендации по использованию:</b>\n"
            "• Рекомендуется обновлять источники не чаще 1 раза в час\n"
            "• Слишком частые обновления (каждые 5-10 минут) не имеют смысла"
        )
        await update.message.reply_text(response, parse_mode='HTML')
    except Exception as e:
        await update.message.reply_text(f"\u274c Ошибка: {e}")

async def cmd_stop_parsing(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Stop all parsing and close all browsers for user"""
    user_id = get_effective_user_id(update)  # В группе = MAIN_USER_ID, в личке = ID отправителя
    try:
        # Деактивируем автоматический парсинг
        db.set_parsing_active(user_id, False)

        # Отменяем задачу автопроверки
        cancel_user_job(context.application, user_id)

        await runner.close_user_clients(user_id)
        await update.message.reply_text(
            "🛑 Все браузеры закрыты.\n"
            "Парсинг остановлен для всех ваших источников.\n\n"
            "Используйте /check для возобновления работы."
        )
        print(f"[OK] Parsing stopped for user {user_id}")
    except Exception as e:
        await update.message.reply_text(f"\u274c Ошибка при остановке парсинга: {e}")

async def cmd_add(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Add source manually"""
    if len(context.args) < 4:
        await update.message.reply_text(
            "Использование:\n"
            "/add <site> <uid> <sheet_url> <name>\n\n"
            "Пример:\n"
            "/add clubgg vader.ClubGG_AID_3132 https://docs.google.com/... Мой ClubGG"
        )
        return

    user_id = get_effective_user_id(update)  # В группе = MAIN_USER_ID, в личке = ID отправителя
    site = context.args[0].lower()
    uid = context.args[1]
    sheet_url = context.args[2]
    name = " ".join(context.args[3:])

    if site not in ("clubgg", "fishpoker", "ebpoker"):
        await update.message.reply_text(
            "\u274c Неизвестный сайт. Доступно: clubgg, fishpoker, ebpoker"
        )
        return

    # Определяем параметры сайта
    if site == "clubgg":
        base_url = "https://clubgg.hammerfell-bs.com/"
        mode = "schedule_by_table"
    elif site == "fishpoker":
        base_url = "https://fishpoker.hammerfell-bs.com/"
        mode = "list_by_limits"
    else:  # ebpoker
        base_url = "https://eb-poker.hammerfell-bs.com/"
        mode = "list_by_limits"

    auth_state_file = f"_auth_state_{site}_{user_id}.json"

    try:
        db.add_source(user_id, name, site, base_url, uid, to_csv_export(sheet_url), mode, auth_state_file)

        text = f"""\u2705 <b>Источник добавлен!</b>

<b>Параметры:</b>
• Название: {name}
• Сайт: {site}
• UID: <code>{uid}</code>

Используйте /check для проверки!"""

        keyboard = [
            [InlineKeyboardButton("\u2705 Проверить сейчас", callback_data="check_all")],
            [InlineKeyboardButton("\U0001f4cb Мои источники", callback_data="list_sources")],
        ]

        await update.message.reply_text(text, parse_mode='HTML',
                                       reply_markup=InlineKeyboardMarkup(keyboard))
    except Exception as e:
        await update.message.reply_text(f"\u274c Ошибка при добавлении: {e}")

async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Button handler"""
    query = update.callback_query
    await query.answer()

    if query.data == "quick_setup":
        return await start_setup(update, context)

    elif query.data == "tutorial":
        await cmd_tutorial(update, context)

    elif query.data == "user_settings":
        await cmd_settings(update, context)

    elif query.data == "list_sources":
        # Показываем список источников
        user_id = get_effective_user_id(update)  # В группе = MAIN_USER_ID, в личке = ID отправителя
        sources = db.get_user_sources(user_id)

        if not sources:
            text = """\U0001f4ed <b>У вас пока нет источников</b>

Добавьте первый источник:
• /setup - Пошаговая настройка
• /add - Добавить вручную
• /tutorial - Подробный гайд"""

            keyboard = [
                [InlineKeyboardButton("\U0001f680 Начать настройку", callback_data="quick_setup")],
            ]
            await query.message.reply_text(text, parse_mode='HTML',
                                           reply_markup=InlineKeyboardMarkup(keyboard))
            return

        text = "<b>\U0001f4cb ВАШИ ИСТОЧНИКИ:</b>\n\n"

        for s in sources:
            status = "\u2705" if s['enabled'] else "\u274c"
            text += f"{status} <b>#{s['id']}</b> {s['name']}\n"
            text += f"   • Сайт: {s['site']}\n"
            text += f"   • UID: <code>{s['unique_id']}</code>\n\n"

        text += "\n<b>Управление:</b>\n"
        text += "/toggle &lt;id&gt; - Вкл/выкл\n"
        text += "/del &lt;id&gt; - Удалить\n"
        text += "/check - Проверить все\n"
        text += "/check &lt;название&gt; - Проверить конкретный"

        keyboard = [
            [InlineKeyboardButton("\u2795 Добавить ещё", callback_data="quick_setup")],
            [InlineKeyboardButton("\u2705 Проверить все", callback_data="check_all")],
        ]

        await query.message.reply_text(text, parse_mode='HTML',
                                       reply_markup=InlineKeyboardMarkup(keyboard))

    elif query.data == "toggle_icons":
        user_id = get_effective_user_id(update)  # В группе = MAIN_USER_ID, в личке = ID отправителя
        new_val = db.toggle_icons(user_id)
        status = "\U0001f465 иконками" if new_val else "\U0001f4dd текстом"
        await query.message.reply_text(f"\u2705 Теперь живые игроки показываются {status}")

    elif query.data == "check_all":
        chat_type = update.effective_chat.type
        chat_id = update.effective_chat.id
        user_id = get_effective_user_id(update)

        # Группо-осознанная логика
        if chat_type in ['group', 'supergroup']:
            sources = db.get_group_sources(chat_id, enabled_only=True)
            is_group = True
        else:
            sources = db.get_user_sources(user_id, enabled_only=True)
            is_group = False

        if not sources:
            await query.message.reply_text("\U0001f4ed Нет активных источников")
            return

        await query.message.reply_text(f"\U0001f504 Проверяю {len(sources)} {plural_ru(len(sources), ('источник', 'источника', 'источников'))}...")

        # Для группы проверяем все источники группы
        if is_group:
            for source in sources:
                try:
                    owner_id = source.get('user_id', user_id)
                    report = await runner.snapshot_source(owner_id, source)
                    chunks = list(chunk_text(report))
                    for chunk in chunks:
                        await query.message.reply_text(chunk)
                except Exception as e:
                    await query.message.reply_text(f"\u274c Ошибка при проверке {source['name']}: {e}")
        else:
            # В личке используем текущее поведение
            reports = await runner.snapshot_user_sources(user_id)
            for source_name, report_text, site_type, source_id in reports:
                for chunk in chunk_text(report_text):
                    await query.message.reply_text(chunk)

    elif query.data.startswith("refresh_source_"):
        source_id = int(query.data.replace("refresh_source_", ""))
        user_id = get_effective_user_id(update)  # В группе = MAIN_USER_ID, в личке = ID отправителя
        source = db.get_source_by_id(source_id)

        if not source or source['user_id'] != user_id:
            await query.message.reply_text(f"\u274c Источник не найден")
            return

        await query.message.reply_text(f"\U0001f504 Обновляю {source['name']}...")
        report = await runner.snapshot_source(user_id, source)

        chunks = list(chunk_text(report))
        for i, chunk in enumerate(chunks):
            # Добавляем кнопку только к последнему чанку
            keyboard = None
            if i == len(chunks) - 1:
                keyboard = InlineKeyboardMarkup([
                    [InlineKeyboardButton(f"\U0001f504 Проверить {source['name']}",
                                        callback_data=f"refresh_source_{source_id}")]
                ])
            await query.message.reply_text(chunk, reply_markup=keyboard)

    # site_ и cancel_setup теперь обрабатываются в ConversationHandler

    elif query.data.startswith("toggle_"):
        source_id = int(query.data.replace("toggle_", ""))
        user_id = get_effective_user_id(update)  # В группе = MAIN_USER_ID, в личке = ID отправителя
        source = db.get_source_by_id(source_id)

        if not source or source['user_id'] != user_id:
            await query.message.reply_text("\u274c Источник не найден")
            return

        db.toggle_source(user_id, source_id)
        new_status = "включён \u2705" if not source['enabled'] else "выключен \u274c"

        # Если выключен источник - проверяем нужно ли закрывать браузер
        if source['enabled']:  # Источник был включен, теперь выключается
            # Проверяем есть ли другие активные источники с тем же сайтом
            remaining_sources = db.get_user_sources(user_id, enabled_only=True)
            other_sources_same_site = [s for s in remaining_sources if s['site'] == source['site']]

            # Закрываем браузер только если нет других активных источников с этим сайтом
            browser_closed = False
            if not other_sources_same_site:
                await runner.close_site_client(user_id, source['site'])
                browser_closed = True

            # Если выключен последний активный источник - деактивируем парсинг
            if not remaining_sources:
                db.set_parsing_active(user_id, False)
                if app_instance:
                    cancel_user_job(app_instance, user_id)
                msg = f"\u2705 Источник '{source['name']}' {new_status}\n"
                if browser_closed:
                    msg += f"\U0001f512 Браузер для сайта {source['site']} закрыт\n"
                msg += "\u26a0\ufe0f Все источники выключены. Автоматический парсинг остановлен."
                await query.message.reply_text(msg)
                return
            else:
                msg = f"\u2705 Источник '{source['name']}' {new_status}"
                if browser_closed:
                    msg += f"\n\U0001f512 Браузер для сайта {source['site']} закрыт"
                else:
                    msg += f"\n\U0001f4cc Браузер для сайта {source['site']} остается открытым (есть другие активные источники)"
                await query.message.reply_text(msg)
                return

        # Если источник был выключен и теперь включается
        if not source['enabled']:  # Источник был выключен, теперь включается
            await query.message.reply_text(
                f"\u2705 Источник '{source['name']}' {new_status}\n\n"
                f"\U0001f4a1 Для запуска автоматической проверки введите:\n"
                f"/check {source['name']}"
            )
        else:
            await query.message.reply_text(f"\u2705 Источник '{source['name']}' {new_status}")

async def on_uid_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """UID input"""
    uid = update.message.text.strip()
    context.user_data['setup_uid'] = uid

    site = context.user_data.get('setup_site', 'clubgg')
    site_names = {
        'clubgg': 'ClubGG',
        'fishpoker': 'FishPoker',
        'ebpoker': 'EBPoker/Diamond'
    }

    text = f"""<b>\U0001f680 МАСТЕР НАСТРОЙКИ</b>

UID сохранён: <code>{uid}</code> \u2705

Шаг 3 из 4: Отправьте ссылку на Google Sheets

Вставьте ссылку на вашу таблицу с расписанием.

<i>Пример: https://docs.google.com/spreadsheets/d/...</i>

Отмена: /cancel"""

    await update.message.reply_text(text, parse_mode='HTML')
    return WAITING_SHEET

async def on_sheet_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Sheet URL input"""
    sheet_url = update.message.text.strip()
    context.user_data['setup_sheet'] = sheet_url

    text = """<b>\U0001f680 МАСТЕР НАСТРОЙКИ</b>

Ссылка на таблицу сохранена \u2705

Шаг 4 из 4: Введите название

Придумайте короткое название для этого источника.

<i>Пример: Мой ClubGG, Diamond основной, и т.д.</i>

Отмена: /cancel"""

    await update.message.reply_text(text, parse_mode='HTML')
    return WAITING_NAME

async def on_name_input(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Name input - finish setup"""
    name = update.message.text.strip()
    user_id = get_effective_user_id(update)  # В группе = MAIN_USER_ID, в личке = ID отправителя

    site = context.user_data.get('setup_site')
    uid = context.user_data.get('setup_uid')
    sheet_url = context.user_data.get('setup_sheet')

    # Определяем параметры сайта
    if site == "clubgg":
        base_url = "https://clubgg.hammerfell-bs.com/"
        mode = "schedule_by_table"
    elif site == "fishpoker":
        base_url = "https://fishpoker.hammerfell-bs.com/"
        mode = "list_by_limits"
    else:  # ebpoker
        base_url = "https://eb-poker.hammerfell-bs.com/"
        mode = "list_by_limits"

    auth_state_file = f"_auth_state_{site}_{user_id}.json"

    try:
        db.add_source(user_id, name, site, base_url, uid, to_csv_export(sheet_url), mode, auth_state_file)

        text = f"""<b>\u2705 НАСТРОЙКА ЗАВЕРШЕНА!</b>

Источник <b>{name}</b> успешно добавлен!

<b>Параметры:</b>
• Сайт: {site}
• UID: <code>{uid}</code>
• Название: {name}

<b>Что дальше?</b>
• /check - Проверить сейчас
• /list - Список источников
• /settings - Настроить интервал

Бот автоматически начнёт проверки!"""

        keyboard = [
            [InlineKeyboardButton("\u2705 Проверить сейчас", callback_data="check_all")],
            [InlineKeyboardButton("\u2795 Добавить ещё", callback_data="quick_setup")],
            [InlineKeyboardButton("\u2699️ Настройки", callback_data="user_settings")],
        ]

        await update.message.reply_text(text, parse_mode='HTML',
                                       reply_markup=InlineKeyboardMarkup(keyboard))
    except Exception as e:
        await update.message.reply_text(f"\u274c Ошибка при добавлении: {e}")

    return ConversationHandler.END

async def cancel_setup(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Cancel setup"""
    if update.callback_query:
        # Вызвано через кнопку
        await update.callback_query.answer()
        await update.callback_query.edit_message_text("[X] Настройка отменена")
    else:
        # Вызвано через команду /cancel
        await update.message.reply_text("[X] Настройка отменена")
    return ConversationHandler.END

async def cmd_interval(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Change interval for sources"""
    chat_type = update.effective_chat.type
    chat_id = update.effective_chat.id
    user_id = get_effective_user_id(update)

    if not context.args:
        # Показываем текущие интервалы
        if chat_type in ['group', 'supergroup']:
            sources = db.get_group_sources(chat_id)
        else:
            sources = db.get_user_sources(user_id)

        if not sources:
            await update.message.reply_text("❌ Нет источников")
            return

        msg = "📋 Текущие интервалы:\n\n"
        for s in sources:
            interval = s.get('interval_minutes', 15)
            msg += f"• {s['name']} (ID {s['id']}): {interval} мин\n"

        msg += "\n📌 Использование:\n"
        msg += "/interval <минуты> - для всех\n"
        msg += "/interval <source_id> <минуты> - для конкретного"

        await update.message.reply_text(msg)
        return

    try:
        # Вариант 1: /interval <source_id> <minutes>
        if len(context.args) == 2:
            try:
                source_id = int(context.args[0])
                minutes = int(context.args[1])
            except ValueError:
                await update.message.reply_text(
                    "❌ Ошибка: укажите ID источника и минуты\n"
                    "Пример: /interval 1 30"
                )
                return

            source = db.get_source_by_id(source_id)
            if not source:
                await update.message.reply_text(f"❌ Источник #{source_id} не найден")
                return

            # Проверяем доступ (владелец или администратор группы)
            if chat_type not in ['group', 'supergroup'] and source['user_id'] != user_id:
                await update.message.reply_text("❌ Это не ваш источник")
                return

            if minutes < 1 or minutes > 1440:
                await update.message.reply_text(
                    "❌ Интервал должен быть от 1 до 1440 минут"
                )
                return

            db.set_source_interval(source_id, minutes)
            await update.message.reply_text(
                f"✅ Интервал для '{source['name']}' установлен: {minutes} мин"
            )

        # Вариант 2: /interval <minutes> (для всех)
        elif len(context.args) == 1:
            try:
                minutes = int(context.args[0])
            except ValueError:
                await update.message.reply_text(
                    "❌ Ошибка: укажите число минут\n"
                    "Пример: /interval 30"
                )
                return

            if minutes < 1 or minutes > 1440:
                await update.message.reply_text(
                    "❌ Интервал должен быть от 1 до 1440 минут"
                )
                return

            if chat_type in ['group', 'supergroup']:
                # В группе - для всех источников группы
                sources = db.get_group_sources(chat_id)
                count = 0
                for source in sources:
                    db.set_source_interval(source['id'], minutes)
                    count += 1

                await update.message.reply_text(
                    f"✅ Интервал для всех источников установлен: {minutes} мин\n"
                    f"({count} источников обновлено)"
                )
            else:
                # В личке - для всех источников пользователя
                sources = db.get_user_sources(user_id)
                count = 0
                for source in sources:
                    db.set_source_interval(source['id'], minutes)
                    count += 1

                await update.message.reply_text(
                    f"✅ Интервал для всех ваших источников установлен: {minutes} мин\n"
                    f"({count} источников обновлено)"
                )
        else:
            await update.message.reply_text(
                "❌ Неверный синтаксис\n"
                "Использование:\n"
                "/interval <минуты> - для всех\n"
                "/interval <source_id> <минуты> - для конкретного"
            )

    except Exception as e:
        await update.message.reply_text(f"❌ Ошибка: {e}")

async def cmd_setgroup(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Привязать источники пользователя к группе"""
    user_id = update.effective_user.id
    chat = update.effective_chat

    # Проверяем аргумент disable в любом чате - отвязываем свои источники
    if context.args and context.args[0].lower() == 'disable':
        # Отвязываем только источники ЭТОГО пользователя
        user_sources = db.get_user_sources(user_id)
        for source in user_sources:
            db.set_source_group(source["id"], None)

        await update.message.reply_text(
            "✅ Ваши источники отвязаны от группы.\n"
            "Они будут отправляться только в личные сообщения."
        )
        return

    # Если команда вызвана в группе, привязать источники
    if chat.type in ['group', 'supergroup']:
        group_chat_id = chat.id

        # Привязываем все источники пользователя к этой группе
        user_sources = db.get_user_sources(user_id)
        for source in user_sources:
            db.set_source_group(source["id"], group_chat_id)

        source_names = ", ".join([s["name"] for s in user_sources])

        await update.message.reply_text(
            f"✅ Ваши источники привязаны к этой группе!\n\n"
            f"Источники: {source_names or 'нет источников'}\n"
            f"ID группы: <code>{group_chat_id}</code>\n\n"
            f"Для отвязки используйте: /setgroup disable",
            parse_mode='HTML'
        )
        return

    # Если команда вызвана в личке
    if not context.args:
        user_sources = db.get_user_sources(user_id)

        if user_sources:
            group_id = user_sources[0].get("group_id")
            if group_id:
                source_names = ", ".join([s["name"] for s in user_sources if s.get("group_id") == group_id])
                await update.message.reply_text(
                    f"📍 <b>Ваши источники в группе:</b>\n\n"
                    f"ID группы: <code>{group_id}</code>\n"
                    f"Источники: {source_names}\n\n"
                    f"<b>Для отвязки:</b>\n"
                    f"/setgroup disable",
                    parse_mode='HTML'
                )
            else:
                await update.message.reply_text(
                    f"📍 <b>Ваши источники не привязаны к группе</b>\n\n"
                    f"<b>Чтобы привязать:</b>\n"
                    f"1. Добавьте бота в группу\n"
                    f"2. Вызовите /setgroup в той группе",
                    parse_mode='HTML'
                )
        else:
            await update.message.reply_text(
                "ℹ️ <b>У вас нет источников</b>\n\n"
                "Добавьте источник командой /add",
                parse_mode='HTML'
            )
        return

async def cmd_toggle(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Toggle source - группо-осознанная версия"""
    chat_type = update.effective_chat.type
    chat_id = update.effective_chat.id
    user_id = get_effective_user_id(update)

    # Определяем источники: из группы или из личного кабинета
    if chat_type in ['group', 'supergroup']:
        sources = db.get_group_sources(chat_id)
        in_group = True
    else:
        sources = db.get_user_sources(user_id)
        in_group = False

    if not sources:
        text = "\U0001f4ed Нет источников"
        if in_group:
            text += " в этой группе"
        else:
            text += ". Используйте /setup"
        await update.message.reply_text(text)
        return

    if not context.args:
        # Показываем список источников с кнопками для переключения
        text = "<b>\U0001f4cb Выберите источник для переключения:</b>\n\n"
        keyboard = []

        for s in sources:
            status = "\u2705" if s['enabled'] else "\u274c"
            text += f"{status} {s['name']} ({s['site']})\n"

            button_text = f"{'\u2705' if s['enabled'] else '\u274c'} {s['name']}"
            keyboard.append([InlineKeyboardButton(button_text, callback_data=f"toggle_{s['id']}")])

        await update.message.reply_text(text, parse_mode='HTML',
                                       reply_markup=InlineKeyboardMarkup(keyboard))
        return

    query = " ".join(context.args)

    # Пробуем найти по ID
    try:
        source_id = int(query)
        source = db.get_source_by_id(source_id)
        if not source:
            await update.message.reply_text(f"❌ Источник #{source_id} не найден")
            return

        # Проверяем доступ
        if not in_group and source['user_id'] != user_id:
            await update.message.reply_text("❌ Это не ваш источник")
            return

        # Переключаем источник
        owner_id = source['user_id']
        db.toggle_source(owner_id, source_id)
        new_status = "включён \u2705" if not source['enabled'] else "выключен \u274c"
        await update.message.reply_text(f"✅ Источник '{source['name']}' {new_status}")
        return
    except ValueError:
        pass

    # Ищем по названию
    query_lower = query.lower()
    matched = [s for s in sources if query_lower in s['name'].lower()]

    if not matched:
        await update.message.reply_text(
            f"❌ Источник '{query}' не найден\n\nИспользуйте /list чтобы посмотреть все источники"
        )
        return

    if len(matched) > 1:
        text = f"\u2753 Найдено несколько источников с '{query}':\n\n"
        for s in matched:
            status = "\u2705" if s['enabled'] else "\u274c"
            text += f"{status} #{s['id']} {s['name']}\n"
        text += f"\nУточните командой: /toggle <id>"
        await update.message.reply_text(text)
        return

    # Нашли один источник - переключаем
    source = matched[0]
    owner_id = source['user_id']
    db.toggle_source(owner_id, source['id'])
    new_status = "включён \u2705" if not source['enabled'] else "выключен \u274c"

    # Если выключен источник - проверяем нужно ли закрывать браузер
    if source['enabled']:  # Источник был включен, теперь выключается
        # Проверяем есть ли другие активные источники с тем же сайтом
        remaining_sources = db.get_user_sources(user_id, enabled_only=True)
        other_sources_same_site = [s for s in remaining_sources if s['site'] == source['site']]

        # Закрываем браузер только если нет других активных источников с этим сайтом
        browser_closed = False
        if not other_sources_same_site:
            await runner.close_site_client(user_id, source['site'])
            browser_closed = True

        # Если выключен последний активный источник - деактивируем парсинг
        if not remaining_sources:
            db.set_parsing_active(user_id, False)
            if app_instance:
                cancel_user_job(app_instance, user_id)
            msg = f"\u2705 Источник '{source['name']}' {new_status}\n"
            if browser_closed:
                msg += f"\U0001f512 Браузер для сайта {source['site']} закрыт\n"
            msg += "\u26a0\ufe0f Все источники выключены. Автоматический парсинг остановлен."
            await update.message.reply_text(msg)
            return
        else:
            msg = f"\u2705 Источник '{source['name']}' {new_status}"
            if browser_closed:
                msg += f"\n\U0001f512 Браузер для сайта {source['site']} закрыт"
            else:
                msg += f"\n\U0001f4cc Браузер для сайта {source['site']} остается открытым (есть другие активные источники)"
            await update.message.reply_text(msg)
            return

    # Если источник был выключен и теперь включается
    if not source['enabled']:  # Источник был выключен, теперь включается
        await update.message.reply_text(
            f"\u2705 Источник '{source['name']}' {new_status}\n\n"
            f"\U0001f4a1 Для запуска автоматической проверки введите:\n"
            f"/check {source['name']}"
        )
    else:
        await update.message.reply_text(f"\u2705 Источник '{source['name']}' {new_status}")

async def cmd_del(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Delete source - группо-осознанная версия"""
    chat_type = update.effective_chat.type
    chat_id = update.effective_chat.id
    user_id = get_effective_user_id(update)

    if not context.args:
        await update.message.reply_text("Использование: /del <id>")
        return

    try:
        source_id = int(context.args[0])
        source = db.get_source_by_id(source_id)

        if not source:
            await update.message.reply_text(f"❌ Источник #{source_id} не найден")
            return

        # Проверяем доступ
        if chat_type not in ['group', 'supergroup'] and source['user_id'] != user_id:
            await update.message.reply_text("❌ Это не ваш источник")
            return

        # Удаляем источник
        owner_id = source['user_id']
        if db.remove_source(owner_id, source_id):
            # Проверяем остались ли активные источники
            remaining_sources = db.get_user_sources(owner_id, enabled_only=True)
            if not remaining_sources:
                db.set_parsing_active(owner_id, False)
                if app_instance:
                    cancel_user_job(app_instance, owner_id)

            await update.message.reply_text(f"✅ Источник #{source_id} '{source['name']}' удалён")
        else:
            await update.message.reply_text(f"❌ Ошибка при удалении источника")

    except ValueError:
        await update.message.reply_text("❌ Ошибка: укажите корректный ID")
    except Exception as e:
        await update.message.reply_text(f"❌ Ошибка: {e}")

async def cmd_icons(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Toggle icons"""
    chat_type = update.effective_chat.type
    chat_id = update.effective_chat.id
    user_id = get_effective_user_id(update)

    # В группе УСТАНАВЛИВАЕМ одинаковое значение для ВСЕХ пользователей
    if chat_type in ['group', 'supergroup']:
        # Получаем все источники группы
        group_sources = db.get_group_sources(chat_id)

        if not group_sources:
            await update.message.reply_text("В группе нет источников")
            return

        # Находим всех уникальных владельцев
        unique_owners = set(source['user_id'] for source in group_sources)

        # Проверяем текущее состояние иконок у всех владельцев
        current_states = []
        for owner_id in unique_owners:
            user = db.get_user(owner_id)
            if user:
                current_states.append(user.get('use_icons', True))

        # Определяем новое значение:
        # Если хотя бы у одного выключено - включаем ВСЕМ
        # Если у всех включено - выключаем ВСЕМ
        any_disabled = False in current_states
        new_value = True if any_disabled else False

        # Устанавливаем ОДИНАКОВОЕ значение для всех владельцев
        for owner_id in unique_owners:
            db.set_icons(owner_id, new_value)

        status = "👥 Иконки включены" if new_value else "📝 Иконки выключены (текстовый режим)"
        await update.message.reply_text(f"✅ {status}\n\nПрименено для {len(unique_owners)} пользователей в группе")
    else:
        # В личке переключаем только для текущего пользователя
        new_val = db.toggle_icons(user_id)
        status = "👥 Иконки включены" if new_val else "📝 Иконки выключены (текстовый режим)"
        await update.message.reply_text(f"✅ {status}")

# ====================== Автоматические проверки ======================

async def auto_check_user(context: ContextTypes.DEFAULT_TYPE):
    """Auto check job для конкретного пользователя с учётом индивидуальных интервалов"""
    from datetime import datetime, timedelta

    user_id = context.job.data  # ID пользователя передается через job.data

    try:
        # Проверяем активен ли парсинг для данного пользователя
        if not db.is_parsing_active(user_id):
            print(f"[SKIP] Parsing inactive for user {user_id}")
            return

        user = db.get_user(user_id)
        if not user:
            return

        # Получаем все источники пользователя
        user_sources = db.get_user_sources(user_id, enabled_only=True)
        if not user_sources:
            return

        # Собираем все источники: личные + из групп
        all_sources = []
        checked_groups = set()

        for source in user_sources:
            group_id = source.get('group_id')

            if group_id and group_id not in checked_groups:
                # Этот источник привязан к группе - получаем ВСЕ источники этой группы
                group_sources = db.get_group_sources(group_id, enabled_only=True)
                all_sources.extend(group_sources)
                checked_groups.add(group_id)
            elif not group_id:
                # Личный источник
                all_sources.append(source)

        if not all_sources:
            return

        # Проверяем каждый источник согласно его интервалу
        for source in all_sources:
            source_id = source['id']
            interval_minutes = source.get('interval_minutes') or 15
            last_checked = db.get_source_last_checked(source_id)

            # Определяем нужно ли проверять этот источник
            should_check = False
            if last_checked is None:
                # Никогда не проверялся
                should_check = True
            else:
                # Проверяем прошло ли достаточно времени
                time_since_check = datetime.now() - last_checked
                if time_since_check >= timedelta(minutes=interval_minutes):
                    should_check = True

            if not should_check:
                continue

            # Фиксируем время начала проверки СРАЗУ, чтобы избежать смещения интервала
            db.set_source_last_checked(source_id)

            # Определяем куда отправлять этот источник
            if source.get('group_id'):
                # Источник привязан к группе
                target_chat_id = source['group_id']
                print(f"   [SEND] {source['name']} -> group {target_chat_id}")
            else:
                # Источник отправляется в личку пользователя
                target_chat_id = user_id
                print(f"   [SEND] {source['name']} -> private chat")

            try:
                # Проверяем источник (используем РЕАЛЬНОГО владельца источника!)
                owner_id = source.get('user_id', user_id)
                report = await runner.snapshot_source(owner_id, source)

                # Отправляем отчёт
                for chunk in chunk_text(report):
                    try:
                        await context.bot.send_message(
                            chat_id=target_chat_id,
                            text=chunk
                        )
                    except Exception as e:
                        print(f"Ошибка отправки для источника {source['name']}: {e}")

                print(f"   [OK] {source['name']} checked and sent")

            except Exception as e:
                print(f"   [ERROR] Failed to check {source['name']}: {e}")

    except Exception as e:
        print(f"Ошибка в auto_check_user для user {user_id}: {e}")


def schedule_user_job(application, user_id: int):
    """Создать или обновить задачу автопроверки для пользователя

    Теперь с индивидуальными интервалами для каждого источника!
    Job запускается каждую минуту, а auto_check_user сам решает какие источники проверять.
    """
    if not application or not application.job_queue:
        print(f"[WARNING] JobQueue not available. Install: pip install python-telegram-bot[job-queue]")
        return

    job_name = f"auto_check_{user_id}"

    # Удаляем старую задачу если она есть
    current_jobs = application.job_queue.get_jobs_by_name(job_name)
    for job in current_jobs:
        job.schedule_removal()

    # Создаем новую задачу которая запускается каждую минуту
    # auto_check_user сам проверит какие источники пора проверять
    application.job_queue.run_repeating(
        auto_check_user,
        interval=dt.timedelta(minutes=1),  # Проверяем каждую минуту
        first=dt.timedelta(minutes=1),
        data=user_id,
        name=job_name
    )
    print(f"[OK] Scheduled auto-check for user {user_id} (every 1 minute)")


def cancel_user_job(application, user_id: int):
    """Отменить задачу автопроверки для пользователя"""
    if not application or not application.job_queue:
        print(f"[WARNING] JobQueue not available")
        return

    job_name = f"auto_check_{user_id}"
    current_jobs = application.job_queue.get_jobs_by_name(job_name)
    for job in current_jobs:
        job.schedule_removal()
    print(f"[OK] Auto-check cancelled for user {user_id}")


async def send_startup_notification(application):
    """Send startup notification to all users"""
    users = db.get_all_users()

    if not users:
        print("Нет зарегистрированных пользователей для уведомления")
        return

    startup_message = (
        "🤖 Бот запущен и готов к работе!\n\n"
        "📋 Для начала работы запустите свою первую проверку командой /check\n\n"
        "💡 После запуска парсинг будет работать до остановки бота или команды /stop_parsing\n\n"
        "Используйте /help для просмотра всех команд"
    )

    for user_id in users:
        try:
            await application.bot.send_message(
                chat_id=user_id,
                text=startup_message
            )
            print(f"[OK] Notification sent to user {user_id}")
        except Exception as e:
            print(f"[ERROR] Failed to send notification to user {user_id}: {e}")


async def send_shutdown_notification(application):
    """Send shutdown notification to all users and cleanup resources"""
    # Закрываем все браузеры корректно перед shutdown
    try:
        print("Closing all browsers...")
        await runner.close_all()
        print("[OK] All browsers closed")
    except Exception as e:
        print(f"[WARNING] Error closing browsers: {e}")

    # Отключаем отправку уведомлений при shutdown, т.к. это вызывает ошибки HTTPXRequest
    # когда бот уже завершает работу и соединение закрывается
    print("Бот остановлен. Уведомления пользователям не отправляются при shutdown.")


# ====================== Main ======================

def build_app():
    global app_instance

    token = os.getenv("TG_TOKEN")
    if not token:
        print("\u274c TG_TOKEN не найден в .env")
        sys.exit(1)

    app = ApplicationBuilder().token(token).build()
    app_instance = app  # Сохраняем в глобальной переменной

    # Conversation handler для мастера настройки
    setup_handler = ConversationHandler(
        entry_points=[
            CommandHandler("setup", start_setup),
            CallbackQueryHandler(start_setup, pattern="^quick_setup$"),
        ],
        states={
            WAITING_SITE: [
                CallbackQueryHandler(on_site_button, pattern="^site_"),
                CallbackQueryHandler(on_change_table_button, pattern="^change_table$"),
            ],
            WAITING_UID: [MessageHandler(filters.TEXT & ~filters.COMMAND, on_uid_input)],
            WAITING_SHEET: [MessageHandler(filters.TEXT & ~filters.COMMAND, on_sheet_input)],
            WAITING_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, on_name_input)],
            WAITING_CHANGE_SOURCE: [CallbackQueryHandler(on_source_select_for_table_change, pattern="^change_source_")],
            WAITING_NEW_TABLE: [MessageHandler(filters.TEXT & ~filters.COMMAND, on_new_table_input)],
        },
        fallbacks=[
            CommandHandler("cancel", cancel_setup),
            CallbackQueryHandler(cancel_setup, pattern="^cancel_setup$"),
        ],
    )

    app.add_handler(setup_handler)
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("help", cmd_help))
    app.add_handler(CommandHandler("tutorial", cmd_tutorial))
    app.add_handler(CommandHandler("list", cmd_list))
    app.add_handler(CommandHandler("settings", cmd_settings))
    app.add_handler(CommandHandler("interval", cmd_interval))
    app.add_handler(CommandHandler("setgroup", cmd_setgroup))
    app.add_handler(CommandHandler("toggle", cmd_toggle))
    app.add_handler(CommandHandler("del", cmd_del))
    app.add_handler(CommandHandler("icons", cmd_icons))
    app.add_handler(CommandHandler("check", cmd_check))
    app.add_handler(CommandHandler("refresh", cmd_refresh))
    app.add_handler(CommandHandler("stop_parsing", cmd_stop_parsing))
    app.add_handler(CommandHandler("add", cmd_add))
    app.add_handler(CallbackQueryHandler(on_button))

    # Регистрируем error handler для сетевых ошибок
    async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
        """Log errors and handle network issues gracefully"""
        import traceback
        from telegram.error import NetworkError, TimedOut

        error = context.error

        # Логируем сетевые ошибки молча (часто случаются, не критичны)
        if isinstance(error, (NetworkError, TimedOut)):
            # Сетевая ошибка - бот переподключится автоматически
            return

        # Для остальных ошибок выводим предупреждение
        print(f"[WARNING] Exception while handling an update:")
        print(f"Error: {error}")

        # Для остальных ошибок выводим полный traceback
        print("".join(traceback.format_exception(None, error, error.__traceback__)))

    app.add_error_handler(error_handler)

    # Проверка доступности JobQueue
    if not app.job_queue:
        print("Warning: JobQueue not available. Install with: pip install python-telegram-bot[job-queue]")
    else:
        print("[OK] JobQueue ready. Individual tasks are created with /check")

    # Post-init callback для отправки уведомления о запуске
    app.post_init = send_startup_notification

    # Post-shutdown callback для отправки уведомления об остановке
    app.post_shutdown = send_shutdown_notification

    return app

def main():
    try:
        print("Многопользовательский Poker Monitor Bot v7.0")
        print("=" * 50)

        app = build_app()

        print("Бот запущен и готов к работе!")
        print("База данных инициализирована")
        print("[OK] Индивидуальные интервалы для каждого пользователя")
        print("[OK] ConcurrencyManager активирован")
        print("[OK] Динамическое управление типами игр")
        print("\nОжидание пользователей...")

        app.run_polling(close_loop=False)
    except KeyboardInterrupt:
        print("\n\n[STOP] Бот остановлен пользователем (Ctrl+C)")
        print("Все задачи завершены.")
    except UnicodeEncodeError:
        print("Multi-user Poker Monitor Bot v7.0")
        print("=" * 50)
        app = build_app()
        print("Bot started successfully!")
        print("Database initialized")
        print("Individual intervals for each user")
        print("ConcurrencyManager active")
        print("Dynamic game types management enabled")
        print("\nWaiting for users...")
        try:
            app.run_polling(close_loop=False)
        except KeyboardInterrupt:
            print("\n\n[STOP] Bot stopped by user (Ctrl+C)")
            print("All tasks completed.")

if __name__ == "__main__":
    main()
