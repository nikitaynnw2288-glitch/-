import asyncio, base64, hashlib, io, json, logging, random, re, socket, sqlite3, string, time as _time
from contextlib import contextmanager
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Optional
from urllib.parse import quote

import exifread, httpx, phonenumbers, whois21
from PIL import Image
from PIL.ExifTags import TAGS, GPSTAGS
from phonenumbers import geocoder, carrier, timezone, number_type, PhoneNumberType
from geopy.geocoders import Nominatim

from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandStart, CommandObject
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (Message, CallbackQuery, BufferedInputFile,
    ReplyKeyboardMarkup, KeyboardButton, InlineKeyboardMarkup, InlineKeyboardButton)
from pydantic_settings import BaseSettings, SettingsConfigDict


class Settings(BaseSettings):
    model_config = SettingsConfigDict(env_file=".env", env_file_encoding="utf-8")
    BOT_TOKEN: str
    OWNER_ID: int = 0
    ADMIN_IDS: str = ""
    RATE_LIMIT_PER_HOUR: int = 10
    HTTP_TIMEOUT: int = 15
    REF_BONUS: int = 5
    GEMINI_KEY: str = ""
    HIBP_KEY: str = ""
    GDRIVE_SA_JSON: str = ""
    GDRIVE_FOLDER_ID: str = ""

    @property
    def initial_admins(self) -> set:
        ids = {int(x) for x in self.ADMIN_IDS.split(",") if x.strip().isdigit()}
        if self.OWNER_ID: ids.add(self.OWNER_ID)
        return ids

    @property
    def db_path(self) -> Path:
        return Path("/data/osint.db") if Path("/data").exists() else Path(__file__).parent / "osint.db"

    @property
    def bases_dir(self) -> Path:
        p = Path("/data/bases") if Path("/data").exists() else Path(__file__).parent / "bases"
        p.mkdir(parents=True, exist_ok=True)
        return p


settings = Settings()
DEFAULT_HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36", "Accept-Language": "en-US,en;q=0.9,ru;q=0.8"}


@contextmanager
def db():
    conn = sqlite3.connect(settings.db_path, timeout=30, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA busy_timeout=30000")
    try:
        yield conn; conn.commit()
    finally:
        conn.close()


def init_db():
    with db() as c:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS users (user_id INTEGER PRIMARY KEY, username TEXT, full_name TEXT,
            first_seen INTEGER, last_seen INTEGER, total_scans INTEGER DEFAULT 0,
            is_banned INTEGER DEFAULT 0, rate_limit INTEGER DEFAULT NULL,
            ref_code TEXT UNIQUE, ref_by INTEGER DEFAULT NULL,
            ref_count INTEGER DEFAULT 0, bonus_scans INTEGER DEFAULT 0);
        CREATE TABLE IF NOT EXISTS scans (id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER,
            target TEXT, target_type TEXT, findings_count INTEGER, created_at INTEGER);
        CREATE INDEX IF NOT EXISTS idx_scans_ut ON scans(user_id, created_at);
        CREATE TABLE IF NOT EXISTS admins (user_id INTEGER PRIMARY KEY, role TEXT DEFAULT 'admin',
            granted_by INTEGER, granted_at INTEGER);
        CREATE TABLE IF NOT EXISTS logs (id INTEGER PRIMARY KEY AUTOINCREMENT, level TEXT DEFAULT 'info',
            event TEXT, user_id INTEGER, details TEXT, created_at INTEGER);
        CREATE INDEX IF NOT EXISTS idx_logs_time ON logs(created_at DESC);
        CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);
        CREATE TABLE IF NOT EXISTS bases (id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE,
            gdrive_id TEXT, size INTEGER, rows INTEGER DEFAULT 0, fields TEXT, format TEXT,
            indexed_at INTEGER, status TEXT DEFAULT 'pending');
        CREATE TABLE IF NOT EXISTS base_rows (id INTEGER PRIMARY KEY AUTOINCREMENT,
            base_id INTEGER, row_num INTEGER, data TEXT);
        CREATE INDEX IF NOT EXISTS idx_br_base ON base_rows(base_id, row_num);
        CREATE TABLE IF NOT EXISTS base_index (id INTEGER PRIMARY KEY AUTOINCREMENT,
            base_id INTEGER, field TEXT, value TEXT, row_id INTEGER);
        CREATE INDEX IF NOT EXISTS idx_bi_field ON base_index(field, value);
        """)
    with db() as c:
        if not c.execute("SELECT 1 FROM meta WHERE key='bootstrapped'").fetchone():
            now = int(_time.time())
            for aid in settings.initial_admins:
                role = "owner" if aid == settings.OWNER_ID else "admin"
                c.execute("INSERT OR IGNORE INTO admins VALUES (?,?,?,?)", (aid, role, aid, now))
            c.execute("INSERT INTO meta VALUES ('bootstrapped', ?)", (str(now),))


def log(event, user_id=None, details="", level="info", conn=None):
    sql = "INSERT INTO logs(level,event,user_id,details,created_at) VALUES (?,?,?,?,?)"
    args = (level, event, user_id, details[:2000], int(_time.time()))
    if conn is not None: conn.execute(sql, args)
    else:
        with db() as c: c.execute(sql, args)


def _gen_ref_code(n=8): return "".join(random.choices(string.ascii_uppercase + string.digits, k=n))


def _unique_ref_code(c):
    for _ in range(20):
        code = _gen_ref_code()
        if not c.execute("SELECT 1 FROM users WHERE ref_code=?", (code,)).fetchone(): return code
    return _gen_ref_code(12)


def ensure_user(uid, uname=None, full_name=None, ref_code=None):
    now = int(_time.time())
    with db() as c:
        if c.execute("SELECT 1 FROM users WHERE user_id=?", (uid,)).fetchone():
            c.execute("UPDATE users SET username=?, full_name=?, last_seen=? WHERE user_id=?",
                      (uname, full_name, now, uid))
        else:
            my_code = _unique_ref_code(c)
            referrer_id = None
            if ref_code:
                row = c.execute("SELECT user_id FROM users WHERE ref_code=?", (ref_code.upper(),)).fetchone()
                if row and row["user_id"] != uid: referrer_id = row["user_id"]
            c.execute("INSERT INTO users (user_id,username,full_name,first_seen,last_seen,ref_code,ref_by,ref_count,bonus_scans) VALUES (?,?,?,?,?,?,?,0,0)",
                      (uid, uname, full_name, now, now, my_code, referrer_id))
            log("user_registered", uid, f"@{uname} ref_by={referrer_id}", conn=c)
            if referrer_id:
                c.execute("UPDATE users SET ref_count=ref_count+1, bonus_scans=bonus_scans+? WHERE user_id=?",
                          (settings.REF_BONUS, referrer_id))
                log("ref_bonus", referrer_id, f"+{settings.REF_BONUS} за реферала {uid}", conn=c)


def get_ref_info(uid):
    with db() as c:
        r = c.execute("SELECT ref_code,ref_count,bonus_scans,ref_by FROM users WHERE user_id=?", (uid,)).fetchone()
        return dict(r) if r else None


def top_referrers(limit=10):
    with db() as c:
        return [dict(r) for r in c.execute("SELECT user_id,username,ref_count,bonus_scans FROM users WHERE ref_count>0 ORDER BY ref_count DESC LIMIT ?", (limit,)).fetchall()]


def get_logs(limit=30, level=None):
    q, args = "SELECT * FROM logs WHERE 1=1", []
    if level: q += " AND level=?"; args.append(level)
    q += " ORDER BY id DESC LIMIT ?"; args.append(limit)
    with db() as c: return [dict(r) for r in c.execute(q, args).fetchall()]


def find_user(query):
    q = query.strip().lstrip("@")
    with db() as c:
        if q.isdigit(): r = c.execute("SELECT * FROM users WHERE user_id=?", (int(q),)).fetchone()
        else: r = c.execute("SELECT * FROM users WHERE username=?", (q,)).fetchone()
        return dict(r) if r else None


def count_scans_last_hour(uid):
    with db() as c:
        return c.execute("SELECT COUNT(*) c FROM scans WHERE user_id=? AND created_at>?", (uid, int(_time.time()) - 3600)).fetchone()["c"]


def effective_limit(uid):
    base = get_rate_limit(uid)
    with db() as c:
        r = c.execute("SELECT bonus_scans FROM users WHERE user_id=?", (uid,)).fetchone()
        bonus = r["bonus_scans"] if r else 0
    return 0 if base == 0 else base + bonus


def log_scan(uid, target, ttype, n):
    with db() as c:
        c.execute("INSERT INTO scans(user_id,target,target_type,findings_count,created_at) VALUES (?,?,?,?,?)",
                  (uid, target, ttype, n, int(_time.time())))
        c.execute("UPDATE users SET total_scans=total_scans+1 WHERE user_id=?", (uid,))
        log("scan", uid, f"{target[:50]} ({ttype}) findings={n}", conn=c)


def user_stats(uid):
    with db() as c:
        r = c.execute("SELECT * FROM users WHERE user_id=?", (uid,)).fetchone()
        return dict(r) if r else {"total_scans": 0, "first_seen": None}


def global_stats():
    with db() as c:
        return {
            "users": c.execute("SELECT COUNT(*) c FROM users").fetchone()["c"],
            "scans": c.execute("SELECT COUNT(*) c FROM scans").fetchone()["c"],
            "day": c.execute("SELECT COUNT(*) c FROM scans WHERE created_at>strftime('%s','now')-86400").fetchone()["c"],
            "banned": c.execute("SELECT COUNT(*) c FROM users WHERE is_banned=1").fetchone()["c"],
            "admins": c.execute("SELECT COUNT(*) c FROM admins").fetchone()["c"],
            "refs": c.execute("SELECT COALESCE(SUM(ref_count),0) c FROM users").fetchone()["c"],
            "bases": c.execute("SELECT COUNT(*) c FROM bases").fetchone()["c"],
        }


def top_users(limit=10):
    with db() as c:
        return [dict(r) for r in c.execute("SELECT user_id,username,total_scans FROM users ORDER BY total_scans DESC LIMIT ?", (limit,)).fetchall()]


def all_user_ids(only_active=True):
    q = "SELECT user_id FROM users" + (" WHERE is_banned=0" if only_active else "")
    with db() as c: return [r["user_id"] for r in c.execute(q).fetchall()]


def set_ban(uid, banned, by):
    with db() as c:
        c.execute("UPDATE users SET is_banned=? WHERE user_id=?", (1 if banned else 0, uid))
        log("ban" if banned else "unban", uid, f"by {by}", level="warning", conn=c)


def is_banned(uid):
    with db() as c:
        r = c.execute("SELECT is_banned FROM users WHERE user_id=?", (uid,)).fetchone()
        return bool(r and r["is_banned"])


def set_rate_limit(uid, limit, by):
    with db() as c:
        c.execute("UPDATE users SET rate_limit=? WHERE user_id=?", (limit, uid))
        log("set_rate_limit", uid, f"limit={limit} by {by}", conn=c)


def get_rate_limit(uid):
    with db() as c:
        r = c.execute("SELECT rate_limit FROM users WHERE user_id=?", (uid,)).fetchone()
        return (r["rate_limit"] if r and r["rate_limit"] is not None else settings.RATE_LIMIT_PER_HOUR)


def is_admin(uid):
    with db() as c: return c.execute("SELECT 1 FROM admins WHERE user_id=?", (uid,)).fetchone() is not None


def is_owner(uid):
    with db() as c:
        r = c.execute("SELECT role FROM admins WHERE user_id=?", (uid,)).fetchone()
        return bool(r and r["role"] == "owner")


def add_admin(uid, by, role="admin"):
    if is_admin(uid): return False
    with db() as c:
        c.execute("INSERT INTO admins VALUES (?,?,?,?)", (uid, role, by, int(_time.time())))
        log("admin_granted", uid, f"role={role} by {by}", level="warning", conn=c)
    return True


def remove_admin(uid):
    if is_owner(uid): return False
    with db() as c:
        cur = c.execute("DELETE FROM admins WHERE user_id=?", (uid,))
        if cur.rowcount:
            log("admin_revoked", uid, level="warning", conn=c); return True
    return False


def list_admins():
    with db() as c:
        return [dict(r) for r in c.execute("SELECT a.user_id,a.role,u.username FROM admins a LEFT JOIN users u ON u.user_id=a.user_id ORDER BY a.role DESC").fetchall()]


GDRIVE_SCOPES = ["https://www.googleapis.com/auth/drive.readonly"]


class GDrive:
    TOKEN_URL = "https://oauth2.googleapis.com/token"
    API = "https://www.googleapis.com/drive/v3"

    def __init__(self):
        self._token = None; self._token_exp = 0; self._sa = None

    @property
    def enabled(self): return bool(settings.GDRIVE_SA_JSON and settings.GDRIVE_FOLDER_ID)

    def _load_sa(self):
        if self._sa is None:
            try: self._sa = json.loads(settings.GDRIVE_SA_JSON)
            except Exception: self._sa = {}
        return self._sa

    def _jwt(self):
        sa = self._load_sa(); now = int(_time.time())
        header = {"alg": "RS256", "typ": "JWT"}
        claim = {"iss": sa["client_email"], "scope": " ".join(GDRIVE_SCOPES),
                 "aud": self.TOKEN_URL, "iat": now, "exp": now + 3600}
        def b64(d): return base64.urlsafe_b64encode(json.dumps(d, separators=(",", ":")).encode()).rstrip(b"=")
        unsigned = b64(header) + b"." + b64(claim)
        from cryptography.hazmat.primitives import hashes, serialization
        from cryptography.hazmat.primitives.asymmetric import padding
        key = serialization.load_pem_private_key(sa["private_key"].encode(), password=None)
        sig = key.sign(unsigned, padding.PKCS1v15(), hashes.SHA256())
        return (unsigned + b"." + base64.urlsafe_b64encode(sig).rstrip(b"=")).decode()

    async def _get_token(self):
        if self._token and _time.time() < self._token_exp - 60: return self._token
        if not self.enabled: return None
        try:
            jwt = self._jwt()
            async with httpx.AsyncClient(timeout=20) as c:
                r = await c.post(self.TOKEN_URL, data={"grant_type": "urn:ietf:params:oauth:grant-type:jwt-bearer", "assertion": jwt})
                if r.status_code != 200:
                    log("gdrive_auth", None, r.text[:300], level="error"); return None
                d = r.json(); self._token = d["access_token"]; self._token_exp = _time.time() + d.get("expires_in", 3600)
                return self._token
        except Exception as e:
            log("gdrive_auth", None, str(e), level="error"); return None

    async def list_files(self, folder_id=None):
        token = await self._get_token()
        if not token: return []
        fid = folder_id or settings.GDRIVE_FOLDER_ID
        try:
            async with httpx.AsyncClient(timeout=30) as c:
                r = await c.get(f"{self.API}/files", params={"q": f"'{fid}' in parents and trashed=false",
                    "fields": "files(id,name,size,mimeType,modifiedTime)", "pageSize": 1000},
                    headers={"Authorization": f"Bearer {token}"})
                if r.status_code != 200:
                    log("gdrive_list", None, r.text[:300], level="error"); return []
                return r.json().get("files", [])
        except Exception as e:
            log("gdrive_list", None, str(e), level="error"); return []

    async def download(self, file_id, dest_path):
        token = await self._get_token()
        if not token: return False
        try:
            async with httpx.AsyncClient(timeout=600) as c:
                async with c.stream("GET", f"{self.API}/files/{file_id}", params={"alt": "media"},
                                    headers={"Authorization": f"Bearer {token}"}) as r:
                    if r.status_code != 200: return False
                    with open(dest_path, "wb") as f:
                        async for chunk in r.aiter_bytes(chunk_size=1024 * 1024): f.write(chunk)
            return True
        except Exception as e:
            log("gdrive_download", None, str(e), level="error"); return False


gdrive = GDrive()
FIELD_PATTERNS = {
    "phone": re.compile(r"^\+?\d{10,15}$"),
    "email": re.compile(r"^[\w\.\-\+]+@[\w\-]+\.[\w\.\-]+$"),
    "fio": re.compile(r"^[А-ЯЁ][а-яё]+\s+[А-ЯЁ][а-яё]+", re.UNICODE),
    "date": re.compile(r"^\d{2}[\.\-/]\d{2}[\.\-/]\d{2,4}$"),
    "ip": re.compile(r"^(\d{1,3}\.){3}\d{1,3}$"),
}


def guess_field(v):
    v = v.strip()
    if not v: return "other"
    for f in ["phone", "email", "date", "ip", "fio"]:
        if FIELD_PATTERNS[f].match(v.replace(" ", "").replace("-", "") if f == "phone" else v): return f
    return "other"


def detect_delimiter(line):
    for d in [";", "|", "\t", ","]:
        if line.count(d) >= 1: return d
    return " "


def parse_sql_line(line):
    m = re.search(r"VALUES\s*\((.*)\)\s*;?\s*$", line, re.IGNORECASE)
    if not m: return None
    raw = m.group(1); values = []; buf = ""; in_str = False
    for i, ch in enumerate(raw):
        if ch == "'" and (i == 0 or raw[i-1] != "\\"): in_str = not in_str
        if ch == "," and not in_str: values.append(buf.strip().strip("'")); buf = ""
        else: buf += ch
    if buf: values.append(buf.strip().strip("'"))
    return values


def parse_line(line, fmt):
    if fmt == "sql":
        v = parse_sql_line(line)
        return v if v else []
    delim = detect_delimiter(line)
    return [x.strip().strip('"') for x in line.split(delim)]


@dataclass
class Finding:
    source: str; category: str; target: str; data: dict = field(default_factory=dict); confidence: float = 1.0


@dataclass
class ModuleResult:
    module_name: str; target: str; success: bool; findings: list = field(default_factory=list); error: str = None; duration_ms: int = 0


class BaseModule:
    name = "base"; accepts: set = set()
    async def run(self, target, client): raise NotImplementedError


class EmailModule(BaseModule):
    name = "email_check"; accepts = {"email"}
    SERVICES = [
        {"name": "Pinterest", "url": "https://www.pinterest.com/resource/EmailExistsResource/get/", "method": "GET",
         "params": {"source_url": "/", "data": '{"options":{"email":"{t}"}}'},
         "check": lambda r: r.status_code == 200 and '"exists": true' in r.text.lower()},
        {"name": "Adobe", "url": "https://auth.services.adobe.com/signin/v2/users/accounts", "method": "POST",
         "json": {"username": "{t}"}, "check": lambda r: r.status_code == 200 and "account" in r.text.lower()},
        {"name": "Spotify", "url": "https://www.spotify.com/api/signup/validate", "method": "POST",
         "json": {"email": "{t}", "validate": "1"}, "check": lambda r: r.status_code == 200 and "exists" in r.text.lower()},
    ]
    async def _one(self, client, svc, target):
        try:
            if svc["method"] == "POST":
                body = {k: (v.format(t=target) if isinstance(v, str) else v) for k, v in svc.get("json", {}).items()}
                r = await client.post(svc["url"], json=body)
            else:
                params = {k: (v.format(t=target) if isinstance(v, str) else v) for k, v in svc.get("params", {}).items()}
                r = await client.get(svc["url"], params=params)
            if svc["check"](r): return Finding(svc["name"], "email", target, {"registered": True}, 0.8)
        except Exception: return None
        return None
    async def run(self, target, client):
        t0 = _time.time()
        raw = await asyncio.gather(*[self._one(client, s, target) for s in self.SERVICES])
        return ModuleResult(self.name, target, True, [f for f in raw if f], duration_ms=int((_time.time() - t0) * 1000))


SITES = [
    ("GitHub", "https://github.com/{u}", "Not Found"),
    ("Reddit", "https://www.reddit.com/user/{u}", "page not found"),
    ("Telegram", "https://t.me/{u}", None),
    ("VK", "https://vk.com/{u}", None),
    ("Habr", "https://habr.com/ru/users/{u}/", "Страница не найдена"),
    ("Pikabu", "https://pikabu.ru/@{u}", None),
    ("TikTok", "https://www.tiktok.com/@{u}", "Couldn't find this account"),
]


class UsernameModule(BaseModule):
    name = "username_check"; accepts = {"username"}
    async def _one(self, client, site, u):
        name, tmpl, miss = site
        url = tmpl.format(u=u)
        try:
            r = await client.get(url)
            if r.status_code == 200 and not (miss and miss.lower() in r.text.lower()):
                return Finding(name, "username", u, {"url": url}, 0.75)
        except Exception: return None
        return None
    async def run(self, target, client):
        t0 = _time.time()
        raw = await asyncio.gather(*[self._one(client, s, target) for s in SITES])
        return ModuleResult(self.name, target, True, [f for f in raw if f], duration_ms=int((_time.time() - t0) * 1000))


PHONE_TYPES_RU = {
    PhoneNumberType.MOBILE: "📱 Мобильный", PhoneNumberType.FIXED_LINE: "☎️ Городской",
    PhoneNumberType.FIXED_LINE_OR_MOBILE: "📞 Фиксированный/мобильный",
    PhoneNumberType.TOLL_FREE: "🆓 Бесплатный (800)", PhoneNumberType.PREMIUM_RATE: "💰 Премиум",
    PhoneNumberType.VOIP: "🌐 VoIP", PhoneNumberType.PERSONAL_NUMBER: "👤 Персональный",
    PhoneNumberType.PAGER: "📟 Пейджер", PhoneNumberType.UAN: "🏢 UAN",
    PhoneNumberType.VOICEMAIL: "📼 Голосовая почта", PhoneNumberType.UNKNOWN: "❓ Неизвестно",
}


class PhoneModule(BaseModule):
    name = "phone_check"; accepts = {"phone"}
    @staticmethod
    def _normalize(raw):
        raw = raw.strip(); plus = raw.startswith("+")
        digits = "".join(c for c in raw if c.isdigit())
        return ("+" if plus else "") + digits
    @staticmethod
    def _links(e164):
        d = e164.lstrip("+")
        return {
            "WhatsApp": f"https://wa.me/{d}", "Telegram": f"https://t.me/+{d}",
            "Truecaller": f"https://www.truecaller.com/search/{d}",
            "Sync.me": f"https://sync.me/search/?number={d}",
            "Google": f"https://www.google.com/search?q={quote(e164)}",
            "Yandex": f"https://yandex.ru/search/?text={quote(e164)}",
        }
    async def run(self, target, client):
        t0 = _time.time()
        raw = self._normalize(target)
        parse_target = raw if raw.startswith("+") else "+" + raw
        try: num = phonenumbers.parse(parse_target, None)
        except phonenumbers.NumberParseException as e:
            return ModuleResult(self.name, target, False, error=f"Не распарсить: {e}", duration_ms=int((_time.time() - t0) * 1000))
        if not phonenumbers.is_possible_number(num):
            return ModuleResult(self.name, target, False, error="Номер невозможен", duration_ms=int((_time.time() - t0) * 1000))
        e164 = phonenumbers.format_number(num, phonenumbers.PhoneNumberFormat.E164)
        intl = phonenumbers.format_number(num, phonenumbers.PhoneNumberFormat.INTERNATIONAL)
        national = phonenumbers.format_number(num, phonenumbers.PhoneNumberFormat.NATIONAL)
        valid = phonenumbers.is_valid_number(num)
        tech = {
            "E.164": e164, "Международный": intl, "Национальный": national,
            "Код страны": f"+{num.country_code}",
            "Регион": geocoder.description_for_number(num, "ru") or "—",
            "Оператор": carrier.name_for_number(num, "ru") or "—",
            "Тип линии": PHONE_TYPES_RU.get(number_type(num), "❓"),
            "Валидный": "✅ да" if valid else "❌ нет",
        }
        tz = timezone.time_zones_for_number(num)
        if tz: tech["Часовые пояса"] = ", ".join(tz)
        findings = [
            Finding("Технические данные", "phone", e164, tech, 1.0 if valid else 0.4),
            Finding("Ссылки для проверки", "phone", e164, {"Ссылки": self._links(e164)}, 1.0),
        ]
        return ModuleResult(self.name, target, True, findings, duration_ms=int((_time.time() - t0) * 1000))


class TelegramModule(BaseModule):
    name = "telegram_check"; accepts = {"phone"}
    async def _check_number(self, phone, client):
        digits = phone.lstrip("+"); url = f"https://t.me/+{digits}"
        try:
            r = await client.get(url)
            if r.status_code != 200: return None
            html = r.text; result = {}
            for tag in ["og:title", "og:description", "og:image"]:
                m = re.search(rf'<meta property="{tag}" content="([^"]+)"', html)
                if m: result[tag] = m.group(1)
            if "og:title" not in result: return None
            return {"Статус": "✅ найден", "Имя": result.get("og:title", "—"),
                    "Био": result.get("og:description", "—"), "Фото": result.get("og:image", "—"),
                    "Ссылка": url}
        except Exception: return None
    async def run(self, target, client):
        t0 = _time.time()
        raw = PhoneModule._normalize(target); e164 = raw if raw.startswith("+") else "+" + raw
        findings = []
        info = await self._check_number(e164, client)
        if info: findings.append(Finding("Telegram", "telegram", e164, info, 0.9))
        else: findings.append(Finding("Telegram", "telegram", e164, {"Статус": "❌ не найден или скрыт"}, 0.5))
        return ModuleResult(self.name, target, True, findings, duration_ms=int((_time.time() - t0) * 1000))


TAG_RU = {"Make": "Производитель", "Model": "Модель устройства", "Software": "Софт",
    "DateTime": "Дата съёмки", "DateTimeOriginal": "Оригинальная дата",
    "ExposureTime": "Выдержка", "FNumber": "Диафрагма", "ISOSpeedRatings": "ISO",
    "FocalLength": "Фокусное расстояние", "Flash": "Вспышка", "LensModel": "Объектив",
    "Artist": "Автор", "Copyright": "Копирайт", "ImageDescription": "Описание"}

FLASH_RU = {0x0: "не сработала", 0x1: "сработала", 0x5: "сработала без возврата",
    0x7: "сработала с возвратом", 0x9: "принудительно", 0x10: "выключена",
    0x18: "авто, не сработала", 0x19: "авто, сработала"}


def _dms_to_deg(dms, ref):
    d, m, s = (float(x.num) / float(x.den) if hasattr(x, "num") else float(x) for x in dms)
    val = d + m / 60 + s / 3600
    return -val if ref in ("S", "W") else val


def _extract_gps(img):
    try:
        exif = img._getexif()
        if not exif: return None
        gps = {}
        for k, v in exif.items():
            if TAGS.get(k) == "GPSInfo":
                for gk, gv in v.items(): gps[GPSTAGS.get(gk, gk)] = gv
        if not gps: return None
        lat = _dms_to_deg(gps["GPSLatitude"], gps.get("GPSLatitudeRef", "N"))
        lon = _dms_to_deg(gps["GPSLongitude"], gps.get("GPSLongitudeRef", "E"))
        return lat, lon
    except Exception: return None


def _reverse_geocode(lat, lon):
    try:
        geo = Nominatim(user_agent="osint_bot")
        loc = geo.reverse(f"{lat}, {lon}", language="ru", timeout=5)
        return loc.address if loc else "не определён"
    except Exception: return "геокодер недоступен"


class MetadataModule(BaseModule):
    name = "metadata"
    @staticmethod
    def analyze(file_bytes, filename):
        findings = []; human = {}
        try:
            tags = exifread.process_file(io.BytesIO(file_bytes), details=False)
            for tag, val in tags.items():
                if tag in ("JPEGThumbnail", "TIFFThumbnail", "Filename", "EXIF MakerNote"): continue
                short = tag.split(" ", 1)[-1]; label = TAG_RU.get(short, short)
                sval = str(val).strip()
                if sval and len(sval) < 200: human[label] = sval
        except Exception: pass
        try:
            img = Image.open(io.BytesIO(file_bytes))
            human["Формат"] = img.format or "?"
            human["Размер"] = f"{img.width}×{img.height}"
            human["Цветовой режим"] = img.mode
            gps = _extract_gps(img)
            if gps:
                lat, lon = gps
                human["GPS координаты"] = f"{lat:.6f}, {lon:.6f}"
                human["Google Maps"] = f"https://maps.google.com/?q={lat},{lon}"
                human["Адрес (reverse)"] = _reverse_geocode(lat, lon)
            exif = img._getexif() or {}
            for k, v in exif.items():
                if TAGS.get(k) == "Flash": human["Вспышка"] = FLASH_RU.get(v, str(v))
        except Exception: pass
        if human: findings.append(Finding(f"Файл: {filename}", "metadata", filename, human, 1.0))
        warns = []
        if "GPS координаты" in human: warns.append("📍 GPS — место съёмки раскрыто")
        if "Модель устройства" in human:
            dev = f"{human.get('Производитель','')} {human.get('Модель устройства','')}".strip()
            warns.append(f"📷 Устройство: {dev}")
        if "Оригинальная дата" in human or "Дата съёмки" in human:
            warns.append(f"🕒 Дата: {human.get('Оригинальная дата') or human.get('Дата съёмки')}")
        if "Software" in human: warns.append(f"💻 Обработано в: {human['Software']}")
        if "Автор" in human: warns.append(f"✍️ Автор: {human['Автор']}")
        if warns: findings.append(Finding("Ключевые следы", "metadata", filename, {"Следы": "\n".join(warns)}, 1.0))
        return findings


class DomainModule(BaseModule):
    name = "domain_check"; accepts = set()
    @staticmethod
    async def _get_subdomains(domain):
        try:
            async with httpx.AsyncClient(timeout=30) as c:
                r = await c.get("https://crt.sh/", params={"q": f"%.{domain}", "output": "json"},
                                headers={"User-Agent": "osint-bot/1.0"})
                if r.status_code != 200: return []
                data = r.json(); subs = set()
                for entry in data:
                    for name in entry.get("name_value", "").split("\n"):
                        name = name.strip().lower()
                        if name.endswith(domain) and "*" not in name: subs.add(name)
                return sorted(subs)[:50]
        except Exception: return []
    @staticmethod
    def _get_ip(domain):
        try: return socket.gethostbyname(domain)
        except Exception: return None
    @classmethod
    async def run(cls, target, client):
        t0 = _time.time(); findings = []
        domain = target.strip().lower().replace("https://", "").replace("http://", "").split("/")[0]
        try:
            w = whois21.WHOIS(domain)
            if w.success:
                wd = w.whois_data or {}
                info = {"Домен": domain, "Регистратор": str(wd.get("registrar", "—")),
                        "Дата регистрации": str(wd.get("creation_date", "—"))[:19],
                        "Дата истечения": str(wd.get("expiration_date", "—"))[:19],
                        "NS": ", ".join(wd.get("name_servers", [])[:5]) if wd.get("name_servers") else "—"}
                findings.append(Finding("WHOIS", "domain", domain, info, 1.0))
        except Exception as e:
            findings.append(Finding("WHOIS", "domain", domain, {"error": str(e)}, 0.0))
        ip = cls._get_ip(domain)
        if ip: findings.append(Finding("IP", "domain", domain, {"IP": ip}, 0.9))
        subs = await cls._get_subdomains(domain)
        if subs: findings.append(Finding("Поддомены", "domain", domain,
            {"Найдено": str(len(subs)), "Список": "\n".join(subs[:20])}, 0.8))
        return ModuleResult(cls.name, target, True, findings, duration_ms=int((_time.time() - t0) * 1000))


TEXT_EMAIL_RE = re.compile(r"[\w\.\-\+]+@[\w\-]+\.[\w\.\-]+")
TEXT_PHONE_RE = re.compile(r"\+?\d[\d\s\-\(\)]{8,}\d")
TEXT_URL_RE = re.compile(r"https?://[^\s]+")
TEXT_MENTION_RE = re.compile(r"@[\w_]{3,32}")
TEXT_COORD_RE = re.compile(r"(-?\d{1,3}\.\d{3,})\s*[,;]\s*(-?\d{1,3}\.\d{3,})")


class TextModule(BaseModule):
    name = "text_analysis"; accepts = set()
    @classmethod
    async def run(cls, target, client):
        t0 = _time.time(); text = target
        emails = list(set(TEXT_EMAIL_RE.findall(text)))
        phones = list(set(TEXT_PHONE_RE.findall(text)))
        urls = list(set(TEXT_URL_RE.findall(text)))
        mentions = list(set(TEXT_MENTION_RE.findall(text)))
        coords = list(set(TEXT_COORD_RE.findall(text)))
        findings = []
        if emails: findings.append(Finding("Email", "text", target, {"Найдено": str(len(emails)), "Список": "\n".join(emails[:10])}, 0.9))
        if phones: findings.append(Finding("Телефоны", "text", target, {"Найдено": str(len(phones)), "Список": "\n".join(phones[:10])}, 0.8))
        if urls: findings.append(Finding("Ссылки", "text", target, {"Найдено": str(len(urls)), "Список": "\n".join(urls[:10])}, 0.9))
        if mentions: findings.append(Finding("Упоминания", "text", target, {"Найдено": str(len(mentions)), "Список": "\n".join(mentions[:10])}, 0.7))
        if coords: findings.append(Finding("Координаты", "text", target, {"Найдено": str(len(coords)), "Список": "\n".join(f"{a}, {b}" for a, b in coords)}, 0.9))
        return ModuleResult(cls.name, target, True, findings, duration_ms=int((_time.time() - t0) * 1000))


class GeoModule(BaseModule):
    name = "geo_search"; accepts = set()
    @staticmethod
    async def _nearby_pois(lat, lon, radius=500):
        query = f'[out:json][timeout:25];(node["amenity"](around:{radius},{lat},{lon});node["shop"](around:{radius},{lat},{lon});node["tourism"](around:{radius},{lat},{lon}););out body 30;'
        try:
            async with httpx.AsyncClient(timeout=30) as c:
                r = await c.post("https://overpass-api.de/api/interpreter", data=query)
                if r.status_code != 200: return []
                data = r.json(); pois = []
                for el in data.get("elements", [])[:20]:
                    tags = el.get("tags", {})
                    pois.append({"name": tags.get("name", "—"), "type": tags.get("amenity") or tags.get("shop") or tags.get("tourism", "—")})
                return pois
        except Exception: return []
    @classmethod
    async def run(cls, target, client):
        t0 = _time.time()
        m = re.match(r"^(-?\d{1,3}\.\d{3,})\s*[,;]\s*(-?\d{1,3}\.\d{3,})$", target.strip())
        if not m: return ModuleResult(cls.name, target, False, error="Нужны координаты вида '55.7558, 37.6173'")
        lat, lon = float(m.group(1)), float(m.group(2)); findings = []
        address = _reverse_geocode(lat, lon)
        findings.append(Finding("Адрес", "geo", target, {"Координаты": f"{lat}, {lon}", "Адрес": address, "Google Maps": f"https://maps.google.com/?q={lat},{lon}"}, 0.9))
        pois = await cls._nearby_pois(lat, lon)
        if pois:
            lines = [f"• {p['name']} ({p['type']})" for p in pois[:15]]
            findings.append(Finding("Ближайшие объекты", "geo", target, {"Найдено": str(len(pois)), "Список": "\n".join(lines)}, 0.8))
        return ModuleResult(cls.name, target, True, findings, duration_ms=int((_time.time() - t0) * 1000))


class GeoAIModule(BaseModule):
    name = "geo_ai"; accepts = set()
    GEMINI_URL = "https://generativelanguage.googleapis.com/v1beta/models/gemini-2.0-flash:generateContent"
    PROMPT = ('You are a geolocation expert. Analyze this photo and determine where it was taken. '
        'Look for: architecture style, signage/language, license plates, terrain, vegetation, sun position, '
        'landmarks, business names, currency, plugs, clothes. Return ONLY valid JSON, no markdown, with fields: '
        '{"country": "str", "city": "str or null", "confidence": 0.0-1.0, "reasoning": "short explanation in Russian", '
        '"google_maps_query": "str"}. If unsure, give your best guess with low confidence.')
    @staticmethod
    async def analyze(image_bytes, filename="photo.jpg"):
        if not settings.GEMINI_KEY: return None
        img_b64 = base64.b64encode(image_bytes).decode()
        payload = {"contents": [{"parts": [{"text": GeoAIModule.PROMPT},
            {"inline_data": {"mime_type": "image/jpeg", "data": img_b64}}]}],
            "generationConfig": {"temperature": 0.2, "maxOutputTokens": 600}}
        try:
            async with httpx.AsyncClient(timeout=60) as c:
                r = await c.post(f"{GeoAIModule.GEMINI_URL}?key={settings.GEMINI_KEY}", json=payload)
                if r.status_code != 200:
                    log("geo_ai_error", None, f"HTTP {r.status_code}: {r.text[:200]}", level="error"); return None
                data = r.json(); text = data["candidates"][0]["content"]["parts"][0]["text"]
            m = re.search(r"\{.*\}", text, re.DOTALL)
            if not m: return None
            info = json.loads(m.group(0))
            return Finding("🌍 AI-геолокация", "geo_ai", filename, {
                "Страна": info.get("country", "—"), "Город": info.get("city") or "—",
                "Уверенность": f"{int(info.get('confidence', 0) * 100)}%",
                "Почему": info.get("reasoning", "—"),
                "Google Maps": f"https://maps.google.com/?q={quote(str(info.get('google_maps_query', '')))}"},
                confidence=float(info.get("confidence", 0.5)))
        except Exception as e:
            log("geo_ai_error", None, str(e), level="error"); return None


class HIBPModule(BaseModule):
    name = "hibp_check"; accepts = {"email"}
    HIBP_BREACH_URL = "https://haveibeenpwned.com/api/v3/breachedaccount/{email}"
    PWNED_PASS_URL = "https://api.pwnedpasswords.com/range/{prefix}"
    @staticmethod
    def _check_password(password):
        sha1 = hashlib.sha1(password.encode("utf-8")).hexdigest().upper()
        prefix, suffix = sha1[:5], sha1[5:]
        try:
            r = httpx.get(f"HIBPModule.PWNED_PASS_URL.format(prefix=prefix)}", headers={"Add-Padding": "true"}, timeout=10)
            if r.status_code != 200: return 0
            for line in r.text.splitlines():
                parts = line.split(":")
                if len(parts) == 2 and parts[0] == suffix: return int(parts[1])
        except Exception: pass
        return 0
    async def _check_breaches(self, email, client):
        if not settings.HIBP_KEY: return []
        url = self.HIBP_BREACH_URL.format(email=quote(email))
        try:
            r = await client.get(url, headers={"hibp-api-key": settings.HIBP_KEY, "User-Agent": "osint-bot/1.0"})
            if r.status_code == 200: return r.json()
            elif r.status_code == 404: return []
        except Exception as e: log("hibp_error", None, str(e), level="error")
        return []
    async def run(self, target, client):
        t0 = _time.time(); findings = []
        if settings.HIBP_KEY:
            breaches = await self._check_breaches(target, client)
            if breaches:
                lines = [f"• <b>{b.get('Title', '?')}</b> ({b.get('Domain', '?')})\n  Дата: {b.get('BreachDate', '?')}\n  Утекло: {', '.join(b.get('DataClasses', [])[:5])}" for b in breaches[:10]]
                findings.append(Finding("HIBP утечки", "hibp", target, {"Найдено": str(len(breaches)), "Список": "\n".join(lines)}, 0.9))
            else:
                findings.append(Finding("HIBP утечки", "hibp", target, {"Статус": "✅ не найден в утечках"}, 0.7))
        else:
            findings.append(Finding("HIBP утечки", "hibp", target, {"Статус": "⚠️ HIBP_KEY не задан"}, 0.3))
        pw_count = self._check_password(target)
        if pw_count > 0:
            findings.append(Finding("Pwned Passwords", "hibp", target, {"Статус": f"⚠️ email встречается как пароль {pw_count} раз"}, 0.8))
        return ModuleResult(self.name, target, True, findings, duration_ms=int((_time.time() - t0) * 1000))


class IPModule(BaseModule):
    name = "ip_check"; accepts = set()
    IP_RE = re.compile(r"^(\d{1,3}\.){3}\d{1,3}$")
    @classmethod
    async def run(cls, target, client):
        t0 = _time.time(); ip = target.strip()
        if not cls.IP_RE.match(ip):
            return ModuleResult(cls.name, target, False, error="Неверный формат IP (нужен IPv4)")
        try:
            parts = [int(x) for x in ip.split(".")]
            if any(p < 0 or p > 255 for p in parts): raise ValueError
        except Exception:
            return ModuleResult(cls.name, target, False, error="Неверный IP")
        try:
            r = await client.get(f"http://ip-api.com/json/{ip}",
                params={"fields": "status,message,country,countryCode,regionName,city,zip,lat,lon,timezone,isp,org,as,proxy,hosting,query"})
            if r.status_code != 200: return ModuleResult(cls.name, target, False, error=f"HTTP {r.status_code}")
            data = r.json()
            if data.get("status") != "success":
                return ModuleResult(cls.name, target, False, error=data.get("message", "API error"))
            info = {"IP": data.get("query", ip), "Страна": data.get("country", "—"),
                "Код страны": data.get("countryCode", "—"), "Регион": data.get("regionName", "—"),
                "Город": data.get("city", "—"), "Индекс": data.get("zip", "—"),
                "Координаты": f"{data.get('lat')}, {data.get('lon')}",
                "Google Maps": f"https://maps.google.com/?q={data.get('lat')},{data.get('lon')}",
                "Часовой пояс": data.get("timezone", "—"), "Провайдер": data.get("isp", "—"),
                "Организация": data.get("org", "—"), "AS": data.get("as", "—"),
                "Прокси/VPN": "✅ да" if data.get("proxy") else "❌ нет",
                "Хостинг": "✅ да" if data.get("hosting") else "❌ нет"}
            return ModuleResult(cls.name, target, True, [Finding("IP-инфо", "ip", ip, info, 0.9)],
                                duration_ms=int((_time.time() - t0) * 1000))
        except Exception as e:
            return ModuleResult(cls.name, target, False, error=str(e), duration_ms=int((_time.time() - t0) * 1000))


async def upload_to_host(image_bytes, filename="img.jpg"):
    try:
        async with httpx.AsyncClient(timeout=30) as c:
            r = await c.post("https://catbox.moe/user/api.php", data={"reqtype": "fileupload"},
                             files={"fileToUpload": (filename, image_bytes)})
            if r.status_code == 200 and r.text.startswith("http"): return r.text.strip()
    except Exception: pass
    try:
        async with httpx.AsyncClient(timeout=30) as c:
            r = await c.post("https://0x0.st", files={"file": (filename, image_bytes)},
                             headers={"User-Agent": "osint-bot/1.0"})
            if r.status_code == 200 and r.text.startswith("http"): return r.text.strip()
    except Exception: pass
    return None


def build_search_links(image_url):
    q = quote(image_url, safe="")
    return {"Yandex (лица)": f"https://yandex.ru/images/search?rpt=imageview&url={q}",
            "Google Lens": f"https://lens.google.com/uploadbyurl?url={q}",
            "Bing Visual": f"https://www.bing.com/images/searchbyimage?cbir=sbi&imgurl={q}",
            "TinEye": f"https://tineye.com/search?url={q}"}
# ═══════════════════════ GDRIVE BASES MODULE ═══════════════════════


class BasesModule:
    """Модуль работы с базами на Google Drive: индексация + поиск."""

    @staticmethod
    def list_bases() -> list[dict]:
        with db() as c:
            return [dict(r) for r in c.execute(
                "SELECT id,name,gdrive_id,size,rows,fields,format,indexed_at,status FROM bases ORDER BY name"
            ).fetchall()]

    @staticmethod
    def get_base(base_id: int) -> dict | None:
        with db() as c:
            r = c.execute("SELECT * FROM bases WHERE id=?", (base_id,)).fetchone()
            return dict(r) if r else None

    @staticmethod
    def delete_base(base_id: int):
        with db() as c:
            c.execute("DELETE FROM base_rows WHERE base_id=?", (base_id,))
            c.execute("DELETE FROM base_index WHERE base_id=?", (base_id,))
            c.execute("DELETE FROM bases WHERE id=?", (base_id,))

    @staticmethod
    async def sync_from_gdrive() -> dict:
        """Читает список файлов с Google Drive, добавляет новые в bases."""
        if not gdrive.enabled:
            return {"ok": False, "error": "GDrive не настроен"}
        files = await gdrive.list_files()
        added = 0
        with db() as c:
            for f in files:
                name = f.get("name", "?")
                fid = f.get("id")
                size = int(f.get("size", 0) or 0)
                ext = name.rsplit(".", 1)[-1].lower() if "." in name else ""
                fmt = "sql" if ext == "sql" else ("csv" if ext == "csv" else "txt")
                row = c.execute("SELECT id FROM bases WHERE gdrive_id=?", (fid,)).fetchone()
                if not row:
                    c.execute("INSERT INTO bases (name,gdrive_id,size,format,status) VALUES (?,?,?,?,?)",
                              (name, fid, size, fmt, "pending"))
                    added += 1
                else:
                    c.execute("UPDATE bases SET name=?, size=?, format=? WHERE gdrive_id=?",
                              (name, size, fmt, fid))
        return {"ok": True, "added": added, "total": len(files)}

    @staticmethod
    async def index_base(base_id: int, progress_cb=None) -> dict:
        """Скачивает файл с GDrive, парсит, пишет индекс в SQLite."""
        base = BasesModule.get_base(base_id)
        if not base:
            return {"ok": False, "error": "База не найдена"}
        if base["status"] == "indexing":
            return {"ok": False, "error": "Уже индексируется"}

        with db() as c:
            c.execute("UPDATE bases SET status='indexing' WHERE id=?", (base_id,))
            c.execute("DELETE FROM base_rows WHERE base_id=?", (base_id,))
            c.execute("DELETE FROM base_index WHERE base_id=?", (base_id,))

        tmp = settings.bases_dir / f"tmp_{base_id}.bin"
        try:
            if progress_cb:
                await progress_cb("⬇️ Скачиваю файл с Google Drive…")
            ok = await gdrive.download(base["gdrive_id"], tmp)
            if not ok:
                with db() as c:
                    c.execute("UPDATE bases SET status='error' WHERE id=?", (base_id,))
                return {"ok": False, "error": "Не удалось скачать"}

            if progress_cb:
                await progress_cb("📖 Индексирую…")

            fmt = base["format"]
            rows_total = 0
            fields_found = {}
            batch_rows = []
            batch_idx = []

            # читаем потоково — по строкам, не грузим всё в память
            with open(tmp, "rb") as f:
                for raw in f:
                    try:
                        line = raw.decode("utf-8", errors="ignore").strip()
                    except Exception:
                        continue
                    if not line: continue
                    if fmt == "sql":
                        if "INSERT" not in line.upper(): continue
                        values = parse_sql_line(line)
                    elif fmt == "csv":
                        if rows_total == 0 and (";" in line or "," in line or "|" in line):
                            low = line.lower()
                            if any(k in low for k in ["фио", "fio", "тел", "phone", "email", "почт", "имя"]):
                                rows_total += 1
                                continue
                        values = [x.strip().strip('"') for x in line.split(detect_delimiter(line))]
                    else:
                        values = parse_line(line, "txt")

                    if not values: continue

                    data_json = json.dumps(values, ensure_ascii=False)
                    batch_rows.append((base_id, rows_total, data_json))
                    for i, v in enumerate(values):
                        field = guess_field(str(v))
                        if field != "other" and len(str(v)) >= 3:
                            fields_found[field] = fields_found.get(field, 0) + 1
                    rows_total += 1

                    if len(batch_rows) >= 500:
                        with db() as c:
                            c.executemany("INSERT INTO base_rows (base_id,row_num,data) VALUES (?,?,?)", batch_rows)
                            ids = c.execute("SELECT last_insert_rowid() as lid").fetchone()
                        # индекс по последнему батчу
                        with db() as c:
                            last_id = c.execute("SELECT MAX(id) FROM base_rows WHERE base_id=?", (base_id,)).fetchone()[0]
                            start_id = last_id - len(batch_rows) + 1
                            for i, br in enumerate(batch_rows):
                                row_id = start_id + i
                                for v in json.loads(br[2]):
                                    fld = guess_field(str(v))
                                    if fld != "other" and len(str(v)) >= 3:
                                        batch_idx.append((base_id, fld, str(v).strip(), row_id))
                            c.executemany("INSERT INTO base_index (base_id,field,value,row_id) VALUES (?,?,?,?)", batch_idx)
                        batch_rows = []
                        batch_idx = []

                # остаток
                if batch_rows:
                    with db() as c:
                        c.executemany("INSERT INTO base_rows (base_id,row_num,data) VALUES (?,?,?)", batch_rows)
                        last_id = c.execute("SELECT MAX(id) FROM base_rows WHERE base_id=?", (base_id,)).fetchone()[0]
                        start_id = last_id - len(batch_rows) + 1
                        for i, br in enumerate(batch_rows):
                            row_id = start_id + i
                            for v in json.loads(br[2]):
                                fld = guess_field(str(v))
                                if fld != "other" and len(str(v)) >= 3:
                                    batch_idx.append((base_id, fld, str(v).strip(), row_id))
                        c.executemany("INSERT INTO base_index (base_id,field,value,row_id) VALUES (?,?,?,?)", batch_idx)

            top_fields = sorted(fields_found.items(), key=lambda x: -x[1])[:10]
            fields_str = ", ".join(f"{k}({v})" for k, v in top_fields)
            with db() as c:
                c.execute("UPDATE bases SET rows=?, fields=?, indexed_at=?, status='ready' WHERE id=?",
                          (rows_total, fields_str, int(_time.time()), base_id))
            log("base_indexed", None, f"base={base['name']} rows={rows_total}")
            return {"ok": True, "rows": rows_total, "fields": fields_str}
        except Exception as e:
            log("base_index_error", None, str(e), level="error")
            with db() as c:
                c.execute("UPDATE bases SET status='error' WHERE id=?", (base_id,))
            return {"ok": False, "error": str(e)}
        finally:
            if tmp.exists():
                try: tmp.unlink()
                except Exception: pass

    @staticmethod
    def search(base_id: int, query: str, field: str = None, limit: int = 50) -> list[dict]:
        """Поиск по индексу базы. field=None → по всем полям."""
        q = query.strip().lower()
        if not q: return []
        with db() as c:
            if field:
                rows = c.execute("""SELECT DISTINCT br.id, br.row_num, br.data
                    FROM base_index bi JOIN base_rows br ON br.id = bi.row_id
                    WHERE bi.base_id=? AND bi.field=? AND LOWER(bi.value) LIKE ?
                    ORDER BY br.row_num LIMIT ?""",
                    (base_id, field, f"%{q}%", limit)).fetchall()
            else:
                rows = c.execute("""SELECT DISTINCT br.id, br.row_num, br.data
                    FROM base_index bi JOIN base_rows br ON br.id = bi.row_id
                    WHERE bi.base_id=? AND LOWER(bi.value) LIKE ?
                    ORDER BY br.row_num LIMIT ?""",
                    (base_id, f"%{q}%", limit)).fetchall()
            return [dict(r) for r in rows]

    @staticmethod
    def search_all(query: str, field: str = None, limit: int = 30) -> list[dict]:
        """Поиск по всем готовым базам."""
        q = query.strip().lower()
        if not q: return []
        results = []
        with db() as c:
            bases = c.execute("SELECT id,name FROM bases WHERE status='ready'").fetchall()
            for b in bases:
                if field:
                    rows = c.execute("""SELECT DISTINCT br.id, br.row_num, br.data
                        FROM base_index bi JOIN base_rows br ON br.id = bi.row_id
                        WHERE bi.base_id=? AND bi.field=? AND LOWER(bi.value) LIKE ?
                        ORDER BY br.row_num LIMIT ?""",
                        (b["id"], field, f"%{q}%", limit)).fetchall()
                else:
                    rows = c.execute("""SELECT DISTINCT br.id, br.row_num, br.data
                        FROM base_index bi JOIN base_rows br ON br.id = bi.row_id
                        WHERE bi.base_id=? AND LOWER(bi.value) LIKE ?
                        ORDER BY br.row_num LIMIT ?""",
                        (b["id"], f"%{q}%", limit)).fetchall()
                for r in rows:
                    results.append({"base": b["name"], "base_id": b["id"],
                                    "row_num": r["row_num"], "data": r["data"]})
                    if len(results) >= limit: return results
        return results


# ═══════════════════════ ORCHESTRATOR ═══════════════════════


EMAIL_RE = re.compile(r"^[\w\.\-\+]+@[\w\-]+\.[\w\.\-]+$")
PHONE_RE = re.compile(r"^\+?\d{10,15}$")
USERNAME_RE = re.compile(r"^[a-zA-Z0-9_\.]{3,32}$")
DOMAIN_RE = re.compile(r"^[a-z0-9\-]+\.[a-z]{2,}$")
GEO_RE = re.compile(r"^-?\d{1,3}\.\d{3,}\s*[,;]\s*-?\d{1,3}\.\d{3,}$")
IP_RE = re.compile(r"^(\d{1,3}\.){3}\d{1,3}$")


def detect_type(target):
    t = target.strip()
    if EMAIL_RE.match(t): return "email"
    if PHONE_RE.match(t.replace(" ", "").replace("-", "")): return "phone"
    if IP_RE.match(t): return "ip"
    if DOMAIN_RE.match(t.lower()): return "domain"
    if GEO_RE.match(t): return "geo"
    if USERNAME_RE.match(t): return "username"
    return "text"


TEXT_MODULES = [EmailModule(), UsernameModule(), PhoneModule(), TelegramModule(), HIBPModule()]


async def run_all(target, ttype):
    results = []
    async with httpx.AsyncClient(timeout=settings.HTTP_TIMEOUT, headers=DEFAULT_HEADERS,
                                 follow_redirects=True) as client:
        if ttype == "domain":
            results.append(await DomainModule.run(target, client))
        elif ttype == "geo":
            results.append(await GeoModule.run(target, client))
        elif ttype == "ip":
            results.append(await IPModule.run(target, client))
        elif ttype == "text":
            results.append(await TextModule.run(target, client))
        else:
            for m in TEXT_MODULES:
                if ttype in m.accepts:
                    try:
                        results.append(await m.run(target, client))
                    except Exception as e:
                        results.append(ModuleResult(m.name, target, False, error=str(e)))
    return results
# ═══════════════════════ UI ═══════════════════════

logging.basicConfig(level=logging.INFO)
router = Router()
_running = set()
_pending_photos = {}


def main_kb(uid=None):
    rows = [
        [KeyboardButton(text="🔍 Сканировать"), KeyboardButton(text="📷 По фото")],
        [KeyboardButton(text="🌐 Домен"), KeyboardButton(text="📍 IP")],
        [KeyboardButton(text="🗺 Гео"), KeyboardButton(text="📝 Текст")],
        [KeyboardButton(text="🗄 Базы"), KeyboardButton(text="👤 Профиль")],
        [KeyboardButton(text="🎁 Рефералы"), KeyboardButton(text="📊 Статистика")],
        [KeyboardButton(text="❓ Помощь")],
    ]
    if uid and is_admin(uid):
        rows.append([KeyboardButton(text="🛠 Админка")])
    return ReplyKeyboardMarkup(keyboard=rows, resize_keyboard=True,
                               input_field_placeholder="Кинь цель, текст, IP или координаты…")


def result_kb(target):
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔁 Повторить", callback_data=f"rescan:{target}"),
         InlineKeyboardButton(text="📄 Отчёт", callback_data=f"report:{target}")],
        [InlineKeyboardButton(text="🗑 Удалить", callback_data="delete")],
    ])


def phone_kb(links):
    items = list(links.items())
    rows = [[InlineKeyboardButton(text=f"🔗 {n}", url=u) for n, u in items[i:i+2]]
            for i in range(0, len(items), 2)]
    rows.append([InlineKeyboardButton(text="🗑 Удалить", callback_data="delete")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def photo_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🌍 Гео по фото (AI)", callback_data="img:geo_ai")],
        [InlineKeyboardButton(text="🔍 Найти в интернете", callback_data="img:search")],
        [InlineKeyboardButton(text="🗑 Удалить", callback_data="delete")],
    ])


def ref_kb(bot_username, ref_code):
    link = f"https://t.me/{bot_username}?start=ref_{ref_code}"
    share = f"https://t.me/share/url?url={quote(link)}&text={quote('Попробуй этого OSINT-бота 👇')}"
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📤 Поделиться", url=share)],
        [InlineKeyboardButton(text="🔁 Обновить", callback_data="ref:refresh")],
    ])


def bases_kb():
    bases = BasesModule.list_bases()
    rows = [[InlineKeyboardButton(text="🔄 Синхронизировать с Google Drive", callback_data="b:sync")]]
    for b in bases:
        icon = {"ready": "✅", "indexing": "⏳", "pending": "⏸", "error": "❌"}.get(b["status"], "•")
        size_mb = f"{b['size'] // 1024 // 1024} МБ" if b["size"] else "?"
        rows.append([InlineKeyboardButton(
            text=f"{icon} {b['name'][:35]} · {size_mb} · {b['rows']}",
            callback_data=f"b:info:{b['id']}")])
    rows.append([InlineKeyboardButton(text="🔍 Умный поиск", callback_data="b:search")])
    rows.append([InlineKeyboardButton(text="⬅️ Назад", callback_data="b:back")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def base_info_kb(base_id):
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📥 Индексировать", callback_data=f"b:index:{base_id}")],
        [InlineKeyboardButton(text="📱 По телефону", callback_data=f"b:search_field:{base_id}:phone"),
         InlineKeyboardButton(text="👤 По ФИО", callback_data=f"b:search_field:{base_id}:fio")],
        [InlineKeyboardButton(text="📧 По email", callback_data=f"b:search_field:{base_id}:email")],
        [InlineKeyboardButton(text="🔍 Поиск по базе", callback_data=f"b:search_base:{base_id}")],
        [InlineKeyboardButton(text="🗑 Удалить", callback_data=f"b:del:{base_id}")],
        [InlineKeyboardButton(text="⬅️ К базам", callback_data="b:menu")],
    ])


def admin_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📊 Статистика", callback_data="a:stats"),
         InlineKeyboardButton(text="📜 Логи", callback_data="a:logs")],
        [InlineKeyboardButton(text="👥 Админы", callback_data="a:admins"),
         InlineKeyboardButton(text="🏆 Топ", callback_data="a:top")],
        [InlineKeyboardButton(text="🎁 Топ рефереров", callback_data="a:topref")],
        [InlineKeyboardButton(text="📣 Рассылка", callback_data="a:broadcast")],
        [InlineKeyboardButton(text="🚫 Бан", callback_data="a:ban"),
         InlineKeyboardButton(text="✅ Разбан", callback_data="a:unban")],
        [InlineKeyboardButton(text="⚙️ Лимит", callback_data="a:limit")],
        [InlineKeyboardButton(text="🔍 Найти юзера", callback_data="a:find")],
    ])


def logs_filter_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🌐 Все", callback_data="a:logs:all"),
         InlineKeyboardButton(text="⚠️ Warn", callback_data="a:logs:warning")],
        [InlineKeyboardButton(text="❌ Error", callback_data="a:logs:error"),
         InlineKeyboardButton(text="ℹ️ Info", callback_data="a:logs:info")],
        [InlineKeyboardButton(text="⬅️ Назад", callback_data="a:back")],
    ])


# ═══════════════════════ FORMATTERS ═══════════════════════


def fmt_card(target, ttype, results):
    total = sum(len(r.findings) for r in results)
    duration = sum(r.duration_ms for r in results)
    short_target = target[:60] + ("…" if len(target) > 60 else "")
    lines = [f"🎯 <b>{short_target}</b>",
             f"┌ 🧩 <b>Тип:</b> {ttype}",
             f"├ 📊 <b>Находок:</b> {total}",
             f"└ ⏱ <b>Время:</b> {duration} мс", ""]
    for r in results:
        icon = "✅" if r.success else "❌"
        lines.append(f"{icon} <b>{r.module_name}</b>")
        if r.error: lines.append(f"  ⚠️ <i>{r.error}</i>")
        if not r.findings:
            lines.append("  <i>— ничего —</i>"); lines.append(""); continue
        for f in r.findings:
            if f.category == "metadata": continue
            if "url" in f.data and len(f.data) <= 2:
                lines.append(f"  • <a href='{f.data['url']}'>{f.source}</a>")
            elif "Список" in f.data:
                lines.append(f"  • <b>{f.source}</b> ({f.data.get('Найдено', '?')})")
                for item in f.data["Список"].split("\n")[:5]:
                    lines.append(f"      <code>{item[:60]}</code>")
            elif "Ссылки" in f.data:
                lines.append(f"  • <b>{f.source}</b> (кнопки внизу)")
            else:
                items = list(f.data.items())[:4]
                preview = " | ".join(f"{k}: {str(v)[:40]}" for k, v in items)
                lines.append(f"  • <b>{f.source}</b>")
                lines.append(f"      {preview}")
        lines.append("")
    return "\n".join(lines)


def fmt_phone(results):
    tech, links = {}, {}
    for r in results:
        for f in r.findings:
            if f.source == "Технические данные": tech = f.data
            elif f.source == "Ссылки для проверки": links = f.data.get("Ссылки", {})
    if not tech: return "❌ Не удалось обработать номер.", {}
    lines = ["📱 <b>Анализ номера</b>", "━━━━━━━━━━━━━━━━━━━━",
             f"<b>E.164:</b> <code>{tech.get('E.164','')}</code>",
             f"<b>Международный:</b> {tech.get('Международный','')}",
             f"<b>Национальный:</b> {tech.get('Национальный','')}", "",
             f"🌍 <b>Регион:</b> {tech.get('Регион','—')}",
             f"📡 <b>Оператор:</b> {tech.get('Оператор','—')}",
             f"🔌 <b>Тип линии:</b> {tech.get('Тип линии','—')}",
             f"✅ <b>Валидный:</b> {tech.get('Валидный','—')}"]
    if tech.get("Часовые пояса"): lines.append(f"🕒 <b>Часовые пояса:</b> {tech['Часовые пояса']}")
    lines += ["", "👇 <b>Проверь вручную:</b>"]
    return "\n".join(lines), links


def fmt_metadata(findings):
    if not findings: return "📷 <b>Метаданные</b>\n\nЧисто."
    lines = ["📷 <b>Метаданные файла</b>", "━━━━━━━━━━━━━━━━━━━━"]
    for f in findings:
        if f.source == "Ключевые следы":
            lines.append("\n⚠️ <b>Что важно:</b>")
            for w in f.data["Следы"].split("\n"): lines.append(w)
        else:
            lines.append(f"\n📁 <b>{f.source}</b>")
            for k, v in list(f.data.items())[:15]:
                if k == "Google Maps": lines.append(f"  ▪ {k}: <a href='{v}'>карта</a>")
                else: lines.append(f"  ▪ <b>{k}:</b> {str(v)[:80]}")
    return "\n".join(lines)


def fmt_ref(uid, bot_username, stats):
    link = f"https://t.me/{bot_username}?start=ref_{stats['ref_code']}"
    return ("🎁 <b>Реферальная система</b>\n━━━━━━━━━━━━━━━━━━━━\n\n"
            f"🔑 <b>Твой код:</b> <code>{stats['ref_code']}</code>\n"
            f"🔗 <b>Твоя ссылка:</b>\n<code>{link}</code>\n\n"
            f"👥 <b>Приглашено:</b> {stats['ref_count']}\n"
            f"⚡️ <b>Бонусных сканов:</b> {stats['bonus_scans']}\n\n"
            "📌 <i>За каждого друга — +5 сканов сверх лимита.</i>\nПоделись ссылкой 👇"), link


def fmt_bases_menu():
    bases = BasesModule.list_bases()
    if not bases:
        return ("🗄 <b>Базы данных</b>\n━━━━━━━━━━━━━━━━━━━━\n\n"
                "📭 Пока нет баз.\n\n"
                "Жми <b>🔄 Синхронизировать</b>, чтобы подтянуть файлы из Google Drive.")
    lines = ["🗄 <b>Базы данных</b>", "━━━━━━━━━━━━━━━━━━━━", ""]
    for b in bases:
        icon = {"ready": "✅", "indexing": "⏳", "pending": "⏸", "error": "❌"}.get(b["status"], "•")
        size_mb = f"{b['size'] // 1024 // 1024} МБ" if b["size"] else "?"
        lines.append(f"{icon} <b>{b['name']}</b>")
        lines.append(f"   📦 {size_mb} · 📊 {b['rows']} строк · {b['status']}")
        if b.get("fields"): lines.append(f"   🏷 {b['fields'][:100]}")
        lines.append("")
    return "\n".join(lines)


def fmt_base_info(base):
    icon = {"ready": "✅", "indexing": "⏳", "pending": "⏸", "error": "❌"}.get(base["status"], "•")
    size_mb = f"{base['size'] // 1024 // 1024} МБ" if base["size"] else "?"
    lines = [f"🗄 <b>{base['name']}</b>", "━━━━━━━━━━━━━━━━━━━━",
             f"{icon} <b>Статус:</b> {base['status']}",
             f"📦 <b>Размер:</b> {size_mb}",
             f"📊 <b>Строк:</b> {base['rows']}",
             f"🔧 <b>Формат:</b> {base.get('format', '?')}"]
    if base.get("fields"): lines.append(f"🏷 <b>Поля:</b> {base['fields'][:200]}")
    if base.get("indexed_at"):
        ts = datetime.fromtimestamp(base["indexed_at"]).strftime("%Y-%m-%d %H:%M")
        lines.append(f"🕒 <b>Индексировано:</b> {ts}")
    lines.append("\n👇 Что делать с базой?")
    return "\n".join(lines)


def fmt_search_results(results, query):
    if not results:
        return f"🔍 По запросу <code>{query}</code> ничего не найдено."
    lines = [f"🔍 <b>Найдено {len(results)}</b>", f"Запрос: <code>{query}</code>", "━━━━━━━━━━━━━━━━━━━━", ""]
    for r in results[:20]:
        try:
            vals = json.loads(r["data"])
        except Exception:
            vals = [r["data"]]
        lines.append(f"📁 <b>{r['base']}</b> · строка {r['row_num']}")
        for i, v in enumerate(vals[:10]):
            if str(v).strip():
                lines.append(f"  {i+1}. <code>{str(v)[:100]}</code>")
        lines.append("")
    if len(results) > 20:
        lines.append(f"<i>… и ещё {len(results) - 20}</i>")
    return "\n".join(lines)


# ═══════════════════════ SCAN ═══════════════════════


async def do_scan(msg, target):
    uid = msg.from_user.id
    if is_banned(uid):
        await msg.answer("🚫 Ты забанен."); return
    limit = effective_limit(uid)
    if limit > 0 and count_scans_last_hour(uid) >= limit:
        await msg.answer(f"⛔ Лимит {limit}/час.\n💡 Пригласи друзей через /ref — +5 сканов за каждого."); return
    if uid in _running:
        await msg.answer("⏳ Уже идёт скан."); return
    _running.add(uid)
    short = target[:80] + ("…" if len(target) > 80 else "")
    status = await msg.answer(f"🔎 <b>Сканирую…</b>\n<code>{short}</code>")
    try:
        ttype = detect_type(target)
        results = await run_all(target, ttype)
        if ttype == "phone":
            text, links = fmt_phone(results)
            kb = phone_kb(links) if links else result_kb(target)
            await status.edit_text(text, reply_markup=kb, disable_web_page_preview=True)
        else:
            text = fmt_card(target, ttype, results)
            await status.edit_text(text, reply_markup=result_kb(target), disable_web_page_preview=True)
        total = sum(len(r.findings) for r in results)
        log_scan(uid, target, ttype, total)
    except Exception as e:
        await status.edit_text(f"💥 Ошибка: <code>{e}</code>")
        log("scan_error", uid, str(e), level="error")
    finally:
        _running.discard(uid)


# ═══════════════════════ HANDLERS ═══════════════════════


@router.message(CommandStart(deep_link=True))
async def start_ref(m: Message, command: CommandObject):
    payload = command.args or ""
    ref_code = payload[4:].upper() if payload.startswith("ref_") else None
    ensure_user(m.from_user.id, m.from_user.username, m.from_user.full_name, ref_code)
    stats = get_ref_info(m.from_user.id) or {}
    text = ("🕵️ <b>OSINT Bot</b>\n\nЧто умею:\n"
            "▫️ Email / username / телефон — пробив\n"
            "▫️ Email утечки — HIBP\n▫️ IP — геолокация и провайдер\n"
            "▫️ Фото — метаданные + AI-гео + поиск\n▫️ Домен — WHOIS, IP, поддомены\n"
            "▫️ Координаты — адрес + что рядом\n▫️ Текст — email/телефоны/ссылки\n"
            "▫️ 🗄 Базы — поиск по загруженным базам\n\nПросто напиши цель 👇")
    if ref_code and stats.get("ref_by"):
        text = "✅ <b>Ты пришёл по приглашению!</b>\n\n" + text
    await m.answer(text, reply_markup=main_kb(m.from_user.id))


@router.message(CommandStart())
async def start(m: Message):
    ensure_user(m.from_user.id, m.from_user.username, m.from_user.full_name)
    await m.answer(
        "🕵️ <b>OSINT Bot</b>\n\nЧто умею:\n"
        "▫️ Email / username / телефон — пробив\n"
        "▫️ Email утечки — HIBP\n▫️ IP — геолокация и провайдер\n"
        "▫️ Фото — метаданные + AI-гео + поиск\n▫️ Домен — WHOIS, IP, поддомены\n"
        "▫️ Координаты — адрес + что рядом\n▫️ Текст — email/телефоны/ссылки\n"
        "▫️ 🗄 Базы — поиск по загруженным базам\n\nПросто напиши цель 👇",
        reply_markup=main_kb(m.from_user.id))


@router.message(Command("help"))
@router.message(F.text == "❓ Помощь")
async def help_cmd(m: Message):
    await m.answer(
        "📖 <b>Как пользоваться</b>\n\n"
        "▫️ Текст — email/ник/телефон/текст\n"
        "▫️ IP — например <code>8.8.8.8</code>\n"
        "▫️ Фото — метаданные + AI-гео + поиск\n"
        "▫️ <code>example.com</code> — WHOIS\n"
        "▫️ <code>55.7558, 37.6173</code> — гео\n"
        "▫️ 🗄 Базы — поиск по Google Drive базам\n\n"
        "Команды: /scan /ref /me /admin",
        reply_markup=main_kb(m.from_user.id))


@router.message(Command("ref"))
@router.message(F.text == "🎁 Рефералы")
async def ref_cmd(m: Message):
    ensure_user(m.from_user.id, m.from_user.username, m.from_user.full_name)
    stats = get_ref_info(m.from_user.id)
    if not stats:
        await m.answer("❌ Профиль не найден. Напиши /start."); return
    me = await m.bot.get_me()
    text, link = fmt_ref(m.from_user.id, me.username, stats)
    await m.answer(text, reply_markup=ref_kb(me.username, stats["ref_code"]), disable_web_page_preview=True)


@router.callback_query(F.data == "ref:refresh")
async def cb_ref_refresh(cb: CallbackQuery):
    stats = get_ref_info(cb.from_user.id)
    if not stats: return await cb.answer("Напиши /start", show_alert=True)
    me = await cb.bot.get_me()
    text, _ = fmt_ref(cb.from_user.id, me.username, stats)
    try:
        await cb.message.edit_text(text, reply_markup=ref_kb(me.username, stats["ref_code"]),
                                   disable_web_page_preview=True)
    except Exception: pass
    await cb.answer("Обновлено")


@router.message(F.text == "👤 Профиль")
@router.message(Command("me"))
async def me(m: Message):
    s = user_stats(m.from_user.id)
    ts = datetime.fromtimestamp(s["first_seen"]).strftime("%Y-%m-%d") if s.get("first_seen") else "—"
    lim = effective_limit(m.from_user.id)
    await m.answer(
        f"👤 <b>{m.from_user.full_name}</b>\n"
        f"🆔 <code>{m.from_user.id}</code>\n"
        f"📊 Сканов: <b>{s['total_scans']}</b>\n"
        f"⚙️ Лимит/час: <b>{lim or '∞'}</b>\n"
        f"👥 Рефералов: <b>{s.get('ref_count', 0)}</b>\n"
        f"⚡️ Бонус: <b>+{s.get('bonus_scans', 0)}</b>\n"
        f"📅 С нами с: {ts}",
        reply_markup=main_kb(m.from_user.id))


@router.message(F.text == "📊 Статистика")
async def my_stats(m: Message):
    s = user_stats(m.from_user.id)
    await m.answer(f"📊 Ты сделал <b>{s['total_scans']}</b> сканов.",
                   reply_markup=main_kb(m.from_user.id))


@router.message(F.text == "🔍 Сканировать")
async def kb_scan(m: Message):
    await m.answer("🔍 Кинь email, username, телефон или IP одним сообщением.")


@router.message(F.text == "📷 По фото")
async def kb_photo(m: Message):
    await m.answer("📷 Кинь фото — вытащу метаданные, сделаю AI-гео и дам ссылки для поиска.")


@router.message(F.text == "🌐 Домен")
async def kb_domain(m: Message):
    await m.answer("🌐 Пришли домен, например <code>example.com</code>")


@router.message(F.text == "📍 IP")
async def kb_ip(m: Message):
    await m.answer("📍 Пришли IP-адрес, например <code>8.8.8.8</code>")


@router.message(F.text == "🗺 Гео")
async def kb_geo(m: Message):
    await m.answer("🗺 Пришли координаты, например <code>55.7558, 37.6173</code>")


@router.message(F.text == "📝 Текст")
async def kb_text(m: Message):
    await m.answer("📝 Пришли текст — вытащу email, телефоны, ссылки, упоминания.")


@router.message(F.text == "🗄 Базы")
@router.message(Command("bases"))
async def kb_bases(m: Message):
    if not gdrive.enabled:
        await m.answer("⚠️ Google Drive не настроен. Добавь GDRIVE_SA_JSON и GDRIVE_FOLDER_ID в Railway.")
        return
    text = fmt_bases_menu()
    await m.answer(text, reply_markup=bases_kb(), disable_web_page_preview=True)


@router.callback_query(F.data == "b:menu")
async def cb_bases_menu(cb: CallbackQuery):
    text = fmt_bases_menu()
    try:
        await cb.message.edit_text(text, reply_markup=bases_kb(), disable_web_page_preview=True)
    except Exception: pass
    await cb.answer()


@router.callback_query(F.data == "b:back")
async def cb_bases_back(cb: CallbackQuery):
    try: await cb.message.delete()
    except Exception: pass
    await cb.answer()


@router.callback_query(F.data == "b:sync")
async def cb_bases_sync(cb: CallbackQuery):
    await cb.answer("Синхронизирую…")
    res = await BasesModule.sync_from_gdrive()
    if not res.get("ok"):
        await cb.message.edit_text(f"❌ {res.get('error', 'Ошибка')}")
        return
    text = fmt_bases_menu() + f"\n\n🔄 Добавлено новых: <b>{res['added']}</b> из {res['total']}"
    try:
        await cb.message.edit_text(text, reply_markup=bases_kb(), disable_web_page_preview=True)
    except Exception: pass


@router.callback_query(F.data.startswith("b:info:"))
async def cb_base_info(cb: CallbackQuery):
    bid = int(cb.data.split(":")[2])
    base = BasesModule.get_base(bid)
    if not base: return await cb.answer("Не найдена", show_alert=True)
    await cb.message.edit_text(fmt_base_info(base), reply_markup=base_info_kb(bid))
    await cb.answer()


@router.callback_query(F.data.startswith("b:index:"))
async def cb_base_index(cb: CallbackQuery):
    bid = int(cb.data.split(":")[2])
    await cb.answer("Индексация запущена")
    msg = cb.message

    async def progress(text):
        try: await msg.edit_text(text)
        except Exception: pass

    await progress("⏳ <b>Начинаю индексацию…</b>")
    res = await BasesModule.index_base(bid, progress_cb=progress)
    if res.get("ok"):
        await msg.edit_text(f"✅ <b>Индексация завершена</b>\n\n"
                            f"📊 Строк: <b>{res['rows']}</b>\n"
                            f"🏷 Поля: {res['fields']}",
                            reply_markup=base_info_kb(bid))
    else:
        await msg.edit_text(f"❌ Ошибка индексации: <code>{res.get('error')}</code>",
                            reply_markup=base_info_kb(bid))


@router.callback_query(F.data.startswith("b:del:"))
async def cb_base_del(cb: CallbackQuery):
    bid = int(cb.data.split(":")[2])
    BasesModule.delete_base(bid)
    await cb.answer("Удалено")
    text = fmt_bases_menu()
    await cb.message.edit_text(text, reply_markup=bases_kb(), disable_web_page_preview=True)


@router.callback_query(F.data == "b:search")
async def cb_base_search_all(cb: CallbackQuery, state: FSMContext):
    await state.set_state(BS.waiting_query)
    await state.update_data(mode="all", field=None, base_id=None)
    await cb.message.edit_text("🔍 <b>Умный поиск по всем базам</b>\n\n"
                               "Пришли запрос (телефон, ФИО, email, часть строки).")
    await cb.answer()


@router.callback_query(F.data.startswith("b:search_base:"))
async def cb_base_search_one(cb: CallbackQuery, state: FSMContext):
    bid = int(cb.data.split(":")[2])
    await state.set_state(BS.waiting_query)
    await state.update_data(mode="one", field=None, base_id=bid)
    await cb.message.edit_text("🔍 <b>Поиск по базе</b>\n\nПришли запрос.")
    await cb.answer()


@router.callback_query(F.data.startswith("b:search_field:"))
async def cb_base_search_field(cb: CallbackQuery, state: FSMContext):
    _, _, bid, field = cb.data.split(":")
    names = {"phone": "📱 телефону", "fio": "👤 ФИО", "email": "📧 email"}
    await state.set_state(BS.waiting_query)
    await state.update_data(mode="one", field=field, base_id=int(bid))
    await cb.message.edit_text(f"🔍 Поиск по <b>{names.get(field, field)}</b>\n\nПришли значение.")
    await cb.answer()


# ═══════════════════════ FALLBACK TEXT ═══════════════════════

BUTTON_TEXTS = {
    "🔍 Сканировать", "📷 По фото", "🌐 Домен", "📍 IP", "🗺 Гео", "📝 Текст",
    "🗄 Базы", "👤 Профиль", "🎁 Рефералы", "📊 Статистика", "❓ Помощь", "🛠 Админка",
}
class BS(StatesGroup):
    waiting_query = State()


@router.message(BS.waiting_query)
async def process_search_query(m: Message, state: FSMContext):
    data = await state.get_data()
    query = (m.text or "").strip()
    if not query:
        await m.answer("Пустой запрос.")
        return
    await state.clear()
    mode = data.get("mode", "all")
    field = data.get("field")
    bid = data.get("base_id")
    await m.answer(f"🔍 Ищу <code>{query}</code>…")
    if mode == "one" and bid:
        results = BasesModule.search(bid, query, field=field, limit=50)
        base = BasesModule.get_base(bid)
        bname = base["name"] if base else "?"
        for r in results:
            r["base"] = bname
    else:
        results = BasesModule.search_all(query, field=field, limit=30)
    text = fmt_search_results(results, query)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🗄 К базам", callback_data="b:menu")],
        [InlineKeyboardButton(text="🔍 Ещё поиск", callback_data="b:search")],
    ])
    await m.answer(text, reply_markup=kb, disable_web_page_preview=True)
    log("base_search", m.from_user.id, f"query={query[:50]} mode={mode} found={len(results)}")


@router.message(Command("scan"))
async def scan_cmd(m: Message):
    ensure_user(m.from_user.id, m.from_user.username, m.from_user.full_name)
    parts = m.text.split(maxsplit=1)
    if len(parts) < 2:
        await m.answer("Использование: <code>/scan цель</code>")
        return
    await do_scan(m, parts[1].strip())


@router.message(F.document | F.photo)
async def handle_file(m: Message):
    ensure_user(m.from_user.id, m.from_user.username, m.from_user.full_name)
    status = await m.answer("📷 <b>Читаю метаданные…</b>")
    try:
        if m.document:
            file_id, filename = m.document.file_id, m.document.file_name or "doc"
        else:
            file_id, filename = m.photo[-1].file_id, "photo.jpg"
        _pending_photos[m.from_user.id] = file_id
        file = await m.bot.get_file(file_id)
        buf = await m.bot.download_file(file.file_path)
        data = buf.read()
        findings = MetadataModule.analyze(data, filename)
        kb = photo_kb() if m.photo else result_kb(filename)
        await status.edit_text(fmt_metadata(findings), reply_markup=kb, disable_web_page_preview=True)
        log_scan(m.from_user.id, filename, "metadata", len(findings))
    except Exception as e:
        await status.edit_text(f"💥 Ошибка: <code>{e}</code>")
        log("file_error", m.from_user.id, str(e), level="error")


@router.callback_query(F.data == "img:geo_ai")
async def cb_geo_ai(cb: CallbackQuery):
    uid = cb.from_user.id
    file_id = _pending_photos.get(uid)
    if not file_id:
        await cb.answer("Кинь фото заново", show_alert=True)
        return
    if not settings.GEMINI_KEY:
        await cb.answer("Нужен GEMINI_KEY в Railway Variables", show_alert=True)
        return
    await cb.answer("Анализирую…")
    await cb.message.edit_reply_markup(reply_markup=None)
    status = await cb.message.answer("🧠 <b>AI анализирует фото…</b>\n<i>~5-10 секунд</i>")
    try:
        file = await cb.bot.get_file(file_id)
        buf = await cb.bot.download_file(file.file_path)
        finding = await GeoAIModule.analyze(buf.read(), "photo.jpg")
        if not finding:
            await status.edit_text("❌ Не удалось определить локацию.")
            return
        lines = ["🌍 <b>AI-геолокация</b>", "━━━━━━━━━━━━━━━━━━━━"]
        for k, v in finding.data.items():
            if k == "Google Maps":
                lines.append(f"  • {k}: <a href='{v}'>открыть на карте</a>")
            else:
                lines.append(f"  • <b>{k}:</b> {v}")
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🗑 Удалить", callback_data="delete")],
        ])
        await status.edit_text("\n".join(lines), reply_markup=kb, disable_web_page_preview=True)
        log("geo_ai", uid, finding.data.get("Страна", "?"))
    except Exception as e:
        await status.edit_text(f"💥 Ошибка: <code>{e}</code>")


@router.callback_query(F.data == "img:search")
async def cb_img_search(cb: CallbackQuery):
    uid = cb.from_user.id
    file_id = _pending_photos.get(uid)
    if not file_id:
        await cb.answer("Кинь фото заново", show_alert=True)
        return
    await cb.answer("Загружаю…")
    await cb.message.edit_reply_markup(reply_markup=None)
    status = await cb.message.answer("⏳ <b>Загружаю фото…</b>")
    try:
        file = await cb.bot.get_file(file_id)
        buf = await cb.bot.download_file(file.file_path)
        url = await upload_to_host(buf.read(), "photo.jpg")
        if not url:
            await status.edit_text("❌ Хостинг недоступен.")
            return
        links = build_search_links(url)
        buttons = [[InlineKeyboardButton(text=f"🔍 {n}", url=u)] for n, u in links.items()]
        buttons.append([InlineKeyboardButton(text="🗑 Удалить", callback_data="delete")])
        text = ("🖼 <b>Поиск по фото</b>\n━━━━━━━━━━━━━━━━━━━━\n"
                f"<b>Фото:</b> <a href=\"{url}\">ссылка</a>\n\n"
                "👇 Yandex — по лицам/СНГ, Google Lens — по объектам.")
        await status.edit_text(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons),
                               disable_web_page_preview=True)
        log("img_search", uid, url)
        _pending_photos.pop(uid, None)
    except Exception as e:
        await status.edit_text(f"💥 Ошибка: <code>{e}</code>")


@router.callback_query(F.data.startswith("rescan:"))
async def cb_rescan(cb: CallbackQuery):
    target = cb.data.split(":", 1)[1]
    await cb.answer()
    await do_scan(cb.message, target)


@router.callback_query(F.data.startswith("report:"))
async def cb_report(cb: CallbackQuery):
    target = cb.data.split(":", 1)[1]
    await cb.answer("Готовлю…")
    ttype = detect_type(target)
    results = await run_all(target, ttype)
    md = render_report(target, ttype, results)
    buf = BufferedInputFile(md.encode(), filename=f"report_{target[:20]}.md")
    await cb.message.answer_document(buf, caption="📄 Отчёт")


@router.callback_query(F.data == "delete")
async def cb_delete(cb: CallbackQuery):
    try: await cb.message.delete()
    except Exception: pass
    _pending_photos.pop(cb.from_user.id, None)
    await cb.answer("Удалено")


def render_report(target, ttype, results):
    total = sum(len(r.findings) for r in results)
    out = ["# OSINT Report", "",
           f"**Target:** `{target}`  ", f"**Type:** `{ttype}`  ",
           f"**Generated:** {datetime.utcnow().strftime('%Y-%m-%d %H:%M:%S')}Z  ",
           f"**Findings:** {total}", "", "---", ""]
    for r in results:
        out.append(f"## {r.module_name} {'✅' if r.success else '❌'}")
        out.append(f"_duration: {r.duration_ms} ms_")
        if r.error: out.append(f"> error: `{r.error}`")
        out.append("")
        if not r.findings:
            out.append("Ничего не найдено.\n"); continue
        for f in r.findings:
            out.append(f"- **{f.source}** (conf {f.confidence})")
            for k, v in f.data.items(): out.append(f"    - {k}: `{v}`")
        out.append("")
    return "\n".join(out)


# ═══════════════════════ ADMIN ═══════════════════════

class AS(StatesGroup):
    admin_user = State()
    ban_user = State()
    limit_user = State()
    broadcast = State()
    find_user = State()


@router.message(Command("admin"))
@router.message(F.text == "🛠 Админка")
async def cmd_admin(m: Message):
    if not is_admin(m.from_user.id): return
    role = "👑 owner" if is_owner(m.from_user.id) else "🛡 admin"
    await m.answer(f"🛠 <b>Админ-панель</b> ({role})\n\nВыбирай 👇", reply_markup=admin_kb())


@router.callback_query(F.data == "a:back")
async def cb_back(cb: CallbackQuery):
    if not is_admin(cb.from_user.id): return await cb.answer()
    await cb.message.edit_text("🛠 <b>Админ-панель</b>", reply_markup=admin_kb())
    await cb.answer()


@router.callback_query(F.data == "a:stats")
async def cb_stats(cb: CallbackQuery):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    g = global_stats()
    await cb.message.edit_text(
        f"📊 <b>Статистика</b>\n━━━━━━━━━━━━━━━━━━━━\n"
        f"👥 Юзеров: <b>{g['users']}</b>\n"
        f"🛡 Админов: <b>{g['admins']}</b>\n"
        f"🚫 Бан: <b>{g['banned']}</b>\n"
        f"🔎 Сканов: <b>{g['scans']}</b>\n"
        f"📅 За 24ч: <b>{g['day']}</b>\n"
        f"🎁 Рефералов: <b>{g['refs']}</b>\n"
        f"🗄 Баз: <b>{g['bases']}</b>",
        reply_markup=admin_kb())
    await cb.answer()


@router.callback_query(F.data == "a:topref")
async def cb_top_ref(cb: CallbackQuery):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    rows = top_referrers(10)
    lines = ["🎁 <b>Топ-10 рефереров</b>", "━━━━━━━━━━━━━━━━━━━━"]
    if not rows: lines.append("Пока никого.")
    for i, u in enumerate(rows, 1):
        un = f"@{u['username']}" if u["username"] else "—"
        lines.append(f"{i}. <code>{u['user_id']}</code> {un} — <b>{u['ref_count']}</b> реф. (⚡️{u['bonus_scans']})")
    await cb.message.edit_text("\n".join(lines), reply_markup=admin_kb())
    await cb.answer()


@router.callback_query(F.data == "a:logs")
async def cb_logs_menu(cb: CallbackQuery):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    await cb.message.edit_text("📜 <b>Логи</b> — фильтр:", reply_markup=logs_filter_kb())
    await cb.answer()


@router.callback_query(F.data.startswith("a:logs:"))
async def cb_logs_show(cb: CallbackQuery):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    level = cb.data.split(":")[2]
    level = None if level == "all" else level
    rows = get_logs(25, level)
    if not rows:
        await cb.message.edit_text("📜 Пусто.", reply_markup=admin_kb())
        return await cb.answer()
    lines = [f"📜 <b>Логи ({len(rows)})</b>", "━━━━━━━━━━━━━━━━━━━━"]
    for r in rows:
        ts = datetime.fromtimestamp(r["created_at"]).strftime("%m-%d %H:%M:%S")
        ic = {"info": "ℹ️", "warning": "⚠️", "error": "❌"}.get(r["level"], "•")
        uid = f" <code>{r['user_id']}</code>" if r["user_id"] else ""
        det = f" — {r['details'][:60]}" if r["details"] else ""
        lines.append(f"{ic} <code>{ts}</code> <b>{r['event']}</b>{uid}{det}")
    await cb.message.edit_text("\n".join(lines)[:4000], reply_markup=admin_kb())
    await cb.answer()


@router.callback_query(F.data == "a:top")
async def cb_top(cb: CallbackQuery):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    rows = top_users(10)
    lines = ["🏆 <b>Топ-10 юзеров</b>", "━━━━━━━━━━━━━━━━━━━━"]
    for i, u in enumerate(rows, 1):
        un = f"@{u['username']}" if u["username"] else "—"
        lines.append(f"{i}. <code>{u['user_id']}</code> {un} — <b>{u['total_scans']}</b>")
    await cb.message.edit_text("\n".join(lines) or "Пусто.", reply_markup=admin_kb())
    await cb.answer()


@router.callback_query(F.data == "a:admins")
async def cb_admins(cb: CallbackQuery):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    rows = list_admins()
    lines = ["👥 <b>Админы</b>", "━━━━━━━━━━━━━━━━━━━━"]
    for a in rows:
        role = "👑" if a["role"] == "owner" else "🛡"
        un = f"@{a['username']}" if a["username"] else "—"
        lines.append(f"{role} <code>{a['user_id']}</code> {un}")
    if is_owner(cb.from_user.id):
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="➕ Выдать", callback_data="a:add_admin"),
             InlineKeyboardButton(text="➖ Снять", callback_data="a:del_admin")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data="a:back")],
        ])
    else:
        kb = admin_kb()
    await cb.message.edit_text("\n".join(lines), reply_markup=kb)
    await cb.answer()


@router.callback_query(F.data == "a:add_admin")
async def cb_add_admin(cb: CallbackQuery, state: FSMContext):
    if not is_owner(cb.from_user.id): return await cb.answer("Только owner", show_alert=True)
    await state.set_state(AS.admin_user)
    await state.update_data(action="add")
    await cb.message.edit_text("➕ Пришли ID или @username будущего админа.")
    await cb.answer()


@router.callback_query(F.data == "a:del_admin")
async def cb_del_admin(cb: CallbackQuery, state: FSMContext):
    if not is_owner(cb.from_user.id): return await cb.answer("Только owner", show_alert=True)
    await state.set_state(AS.admin_user)
    await state.update_data(action="del")
    await cb.message.edit_text("➖ Пришли ID или @username для снятия.")
    await cb.answer()


@router.message(AS.admin_user)
async def process_admin_user(m: Message, state: FSMContext):
    if not is_owner(m.from_user.id): return
    data = await state.get_data()
    u = find_user(m.text.strip())
    await state.clear()
    if not u:
        await m.answer("❌ Не найден. Пусть напишет /start."); return
    if data.get("action") == "add":
        ok = add_admin(u["user_id"], m.from_user.id)
        if ok:
            await m.answer(f"✅ <code>{u['user_id']}</code> теперь админ.", reply_markup=admin_kb())
            try: await m.bot.send_message(u["user_id"], "🛡 Тебе выдана админка. /admin")
            except Exception: pass
        else:
            await m.answer("⚠️ Уже админ.", reply_markup=admin_kb())
    else:
        ok = remove_admin(u["user_id"])
        await m.answer("✅ Снят." if ok else "⚠️ Нельзя снять (owner).", reply_markup=admin_kb())


@router.callback_query(F.data == "a:ban")
async def cb_ban(cb: CallbackQuery, state: FSMContext):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    await state.set_state(AS.ban_user)
    await state.update_data(action="ban")
    await cb.message.edit_text("🚫 Пришли ID или @username для бана.")
    await cb.answer()


@router.callback_query(F.data == "a:unban")
async def cb_unban(cb: CallbackQuery, state: FSMContext):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    await state.set_state(AS.ban_user)
    await state.update_data(action="unban")
    await cb.message.edit_text("✅ Пришли ID или @username для разбана.")
    await cb.answer()


@router.message(AS.ban_user)
async def process_ban(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    data = await state.get_data()
    action = data.get("action", "ban")
    u = find_user(m.text.strip())
    await state.clear()
    if not u: await m.answer("❌ Не найден."); return
    if is_admin(u["user_id"]) and not is_owner(m.from_user.id):
        await m.answer("⚠️ Нельзя банить админа.", reply_markup=admin_kb()); return
    set_ban(u["user_id"], action == "ban", m.from_user.id)
    word = "забанен" if action == "ban" else "разбанен"
    await m.answer(f"✅ <code>{u['user_id']}</code> {word}.", reply_markup=admin_kb())


@router.callback_query(F.data == "a:limit")
async def cb_limit(cb: CallbackQuery, state: FSMContext):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    await state.set_state(AS.limit_user)
    await cb.message.edit_text("⚙️ Формат: <code>ID_or_@username лимит</code>\n"
                               "Пример: <code>123456789 50</code>\nЛимит 0 — без ограничений.")
    await cb.answer()


@router.message(AS.limit_user)
async def process_limit(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    parts = m.text.split()
    if len(parts) != 2 or not parts[1].isdigit():
        await m.answer("Формат: <code>ID лимит</code>"); return
    u = find_user(parts[0])
    if not u: await m.answer("❌ Не найден."); return
    limit = int(parts[1])
    set_rate_limit(u["user_id"], limit if limit > 0 else None, m.from_user.id)
    await state.clear()
    await m.answer(f"✅ Лимит: <b>{limit or '∞'}</b>/час", reply_markup=admin_kb())


@router.callback_query(F.data == "a:broadcast")
async def cb_broadcast(cb: CallbackQuery, state: FSMContext):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    await state.set_state(AS.broadcast)
    await cb.message.edit_text("📣 Пришли текст рассылки. /cancel — отмена.")
    await cb.answer()


@router.message(AS.broadcast)
async def process_broadcast(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    await state.clear()
    text = m.text or ""
    if not text: return
    ids = all_user_ids()
    sent = failed = 0
    await m.answer(f"📣 Рассылка на {len(ids)} юзеров…")
    for uid in ids:
        try:
            await m.bot.send_message(uid, text); sent += 1
        except Exception: failed += 1
    log("broadcast", m.from_user.id, f"sent={sent} failed={failed}", level="warning")
    await m.answer(f"✅ Готово.\nОтправлено: <b>{sent}</b>\nОшибок: <b>{failed}</b>",
                   reply_markup=admin_kb())


@router.callback_query(F.data == "a:find")
async def cb_find(cb: CallbackQuery, state: FSMContext):
    if not is_admin(cb.from_user.id): return await cb.answer("Нет доступа", show_alert=True)
    await state.set_state(AS.find_user)
    await cb.message.edit_text("🔍 Пришли ID или @username.")
    await cb.answer()


@router.message(AS.find_user)
async def process_find(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    u = find_user(m.text.strip())
    await state.clear()
    if not u:
        await m.answer("❌ Не найден.", reply_markup=admin_kb()); return
    ts1 = datetime.fromtimestamp(u["first_seen"]).strftime("%Y-%m-%d %H:%M")
    ts2 = datetime.fromtimestamp(u["last_seen"] or u["first_seen"]).strftime("%Y-%m-%d %H:%M")
    lim = u["rate_limit"] if u["rate_limit"] is not None else settings.RATE_LIMIT_PER_HOUR
    await m.answer(
        f"👤 <b>Юзер</b>\n━━━━━━━━━━━━━━━━━━━━\n"
        f"🆔 <code>{u['user_id']}</code>\n"
        f"🔗 @{u['username'] or '—'}\n"
        f"📛 {u['full_name'] or '—'}\n"
        f"🔎 Сканов: <b>{u['total_scans']}</b>\n"
        f"⚙️ Лимит/час: <b>{lim}</b>\n"
        f"👥 Рефералов: <b>{u.get('ref_count', 0)}</b>\n"
        f"⚡️ Бонус: <b>+{u.get('bonus_scans', 0)}</b>\n"
        f"🔑 Код: <code>{u.get('ref_code', '—')}</code>\n"
        f"🚫 Бан: <b>{'да' if u['is_banned'] else 'нет'}</b>\n"
        f"🛡 Админ: <b>{'да' if is_admin(u['user_id']) else 'нет'}</b>\n"
        f"📅 Первый: {ts1}\n🕒 Последний: {ts2}",
        reply_markup=admin_kb())


@router.message(Command("cancel"))
async def cmd_cancel(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id): return
    await state.clear()
    await m.answer("Отменено.", reply_markup=admin_kb())

# ═══════════════════════ FALLBACK TEXT SCAN (ВСЕГДА ПОСЛЕДНИЙ) ═══════════════════════


@router.message(F.text & ~F.text.startswith("/"))
async def text_scan(m: Message):
    if m.text.strip() in BUTTON_TEXTS:
        return
    ensure_user(m.from_user.id, m.from_user.username, m.from_user.full_name)
    await do_scan(m, m.text.strip())


# ═══════════════════════ MAIN ═══════════════════════


async def main():
    init_db()
    bot = Bot(settings.BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    await bot.delete_webhook(drop_pending_updates=True)
    log("bot_started", None, f"GDrive={'on' if gdrive.enabled else 'off'}")
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
