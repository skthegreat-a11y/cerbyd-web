# ============================================================
# CERBYD WEB
# By Cerbyd Inc.
#
# Main Backend
# Version 5.1.0
# Codename: Integrated Answer Search
#
# A classic Internet search engine / portal backend.
#
# Features:
#   - Web Search
#   - Smart Answers
#   - Wikipedia
#   - Dictionary
#   - Calculator
#   - Images
#   - News
#   - Shopping
#   - Directory
#   - Network Speed Test
#   - Network Ping
#   - Health / Status
#   - Fast HTTP sessions
#   - Short-term caching
#   - Parallel answer sources
#   - CORS
#   - SQLite Database
#   - Search History
#   - Favorites Storage
#   - Network History
#   - Persistent Settings
#   - Public Rate Limiting
#   - Security Headers
#   - GZip Compression
#   - Production PORT / Host Support
#   - Network Test Result Recording
#
# ============================================================

from fastapi import FastAPI, Query, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.middleware.gzip import GZipMiddleware
from fastapi.middleware.trustedhost import TrustedHostMiddleware
from fastapi.responses import FileResponse, JSONResponse, StreamingResponse

from pathlib import Path

from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock, local

import ast
import hashlib
import difflib
import email.utils
import hmac
import secrets
import html
import json
import math
import operator
import os
import re
import sqlite3
import time
from collections import defaultdict, deque
import urllib.parse
import uuid
import xml.etree.ElementTree as ET

import requests
import jwt
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from bs4 import BeautifulSoup


# ============================================================
# CERBYD APPLICATION INFORMATION
# ============================================================

APP_NAME = "Cerbyd Web"
APP_VERSION = "5.9.0"
APP_CODENAME = "Build 25 Final Release"
APP_COMPANY = "Cerbyd Inc."

BASE_DIR = Path(__file__).resolve().parent
INDEX_FILE = BASE_DIR / "index.html"
DATABASE_FILE = Path(os.getenv("CERBYD_DATABASE_FILE", str(BASE_DIR / "cerbyd.db"))).expanduser()

REQUEST_TIMEOUT = float(os.getenv("CERBYD_REQUEST_TIMEOUT", "4"))
CONNECT_TIMEOUT = float(os.getenv("CERBYD_CONNECT_TIMEOUT", "2.5"))
MAX_IMAGE_RESULTS = int(os.getenv("CERBYD_MAX_IMAGE_RESULTS", "60"))
MAX_WEB_RESULTS = int(os.getenv("CERBYD_MAX_WEB_RESULTS", "20"))

# Short cache prevents repeated searches from repeatedly
# hitting external services.
CACHE_TTL = int(os.getenv("CERBYD_CACHE_TTL", "90"))
CACHE_MAX_ITEMS = 250

# Number of background workers used by the Cerbyd engine.
CERBYD_WORKERS = int(os.getenv("CERBYD_WORKERS", "8"))

# Public-release controls. These require no extra Python packages.
RATE_LIMIT_WINDOW = int(os.getenv("CERBYD_RATE_WINDOW", "60"))
RATE_LIMIT_DEFAULT = int(os.getenv("CERBYD_RATE_LIMIT", "120"))
RATE_LIMIT_SEARCH = int(os.getenv("CERBYD_SEARCH_RATE_LIMIT", "30"))
RATE_LIMIT_NETWORK = int(os.getenv("CERBYD_NETWORK_RATE_LIMIT", "6"))
MAX_QUERY_LENGTH = int(os.getenv("CERBYD_MAX_QUERY_LENGTH", "500"))

# Optional Ollama-compatible local model endpoint. Leave CERBYD_AI_URL empty to use sourced answers.
CERBYD_AI_URL = os.getenv("CERBYD_AI_URL", "").strip()
CERBYD_AI_MODEL = os.getenv("CERBYD_AI_MODEL", "llama3.2:latest").strip()
CERBYD_AI_TIMEOUT = float(os.getenv("CERBYD_AI_TIMEOUT", "35"))

CORS_ORIGINS = [
    item.strip()
    for item in os.getenv("CERBYD_CORS_ORIGINS", "*").split(",")
    if item.strip()
]

ALLOWED_HOSTS = [
    item.strip()
    for item in os.getenv("CERBYD_ALLOWED_HOSTS", "*").split(",")
    if item.strip()
]


# ============================================================
# FAST CERBYD ENGINE
# ============================================================

_thread_local = local()

_cache = {}
_cache_lock = Lock()

CERBYD_EXECUTOR = ThreadPoolExecutor(
    max_workers=CERBYD_WORKERS,
    thread_name_prefix="CerbydWorker"
)


# ============================================================
# HTTP HEADERS
# ============================================================

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 "
        "(Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 "
        "(KHTML, like Gecko) "
        "CerbydWeb/5.9.0 "
        "Safari/537.36"
    ),
    "Accept-Language": "en-US,en;q=0.9",
}


# ============================================================
# NETWORK LEVELS
# ============================================================

NETWORK_LEVELS = [
    {
        "name": "Maruti Suzuki 800",
        "min_mbps": 0,
        "max_mbps": 1,
        "class": "Very Slow",
    },
    {
        "name": "Toyota Corolla",
        "min_mbps": 1,
        "max_mbps": 10,
        "class": "Slow",
    },
    {
        "name": "BMW M3",
        "min_mbps": 10,
        "max_mbps": 50,
        "class": "Good",
    },
    {
        "name": "Porsche 911 Turbo S",
        "min_mbps": 50,
        "max_mbps": 200,
        "class": "Fast",
    },
    {
        "name": "Bugatti Chiron Super Sport",
        "min_mbps": 200,
        # Keep this JSON-safe for public APIs instead of using Infinity.
        "max_mbps": 1_000_000_000,
        "class": "Extremely Fast",
    },
]



# ============================================================
# CERBYD DATABASE ENGINE
# ============================================================
#
# Cerbyd Web uses SQLite so the database works locally with
# no separate database server or additional database package.
#
# Database file:
#     cerbyd.db
#
# Tables:
#     searches
#     favorites
#     network_tests
#     settings
#     users
#
# ============================================================

DATABASE_SCHEMA = """
CREATE TABLE IF NOT EXISTS searches (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    query TEXT NOT NULL,
    search_type TEXT NOT NULL DEFAULT 'web',
    results_count INTEGER NOT NULL DEFAULT 0,
    response_ms REAL,
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_searches_created_at
ON searches(created_at);

CREATE INDEX IF NOT EXISTS idx_searches_query
ON searches(query);

CREATE TABLE IF NOT EXISTS favorites (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    title TEXT NOT NULL,
    url TEXT NOT NULL,
    description TEXT NOT NULL DEFAULT '',
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(url)
);

CREATE TABLE IF NOT EXISTS network_tests (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    speed_mbps REAL NOT NULL DEFAULT 0,
    latency_ms REAL,
    network_level TEXT NOT NULL DEFAULT '',
    network_class TEXT NOT NULL DEFAULT '',
    test_bytes INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_network_tests_created_at
ON network_tests(created_at);

CREATE TABLE IF NOT EXISTS settings (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL DEFAULT '',
    updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS users (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    username TEXT NOT NULL UNIQUE,
    email TEXT NOT NULL UNIQUE,
    password_hash TEXT NOT NULL,
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS auth_sessions (
    token_hash TEXT PRIMARY KEY,
    user_id INTEGER NOT NULL,
    expires_at INTEGER NOT NULL,
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
);

CREATE INDEX IF NOT EXISTS idx_auth_sessions_expires
ON auth_sessions(expires_at);

CREATE TABLE IF NOT EXISTS oauth_accounts (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    provider TEXT NOT NULL,
    subject TEXT NOT NULL,
    user_id INTEGER NOT NULL,
    provider_email TEXT NOT NULL DEFAULT '',
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(provider, subject),
    FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
);

CREATE INDEX IF NOT EXISTS idx_oauth_accounts_user
ON oauth_accounts(user_id);

CREATE TABLE IF NOT EXISTS oauth_states (
    state_hash TEXT PRIMARY KEY,
    provider TEXT NOT NULL,
    link_user_id INTEGER,
    expires_at INTEGER NOT NULL,
    created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_oauth_states_expires
ON oauth_states(expires_at);
"""


def get_db():
    """
    Opens a short-lived SQLite connection.

    SQLite is intentionally opened per operation instead of keeping
    one global connection alive. This is safer with FastAPI workers
    and avoids sharing a SQLite connection between threads.
    """
    connection = sqlite3.connect(
        DATABASE_FILE,
        timeout=10,
        check_same_thread=False
    )
    connection.row_factory = sqlite3.Row
    return connection


def init_database():
    """
    Creates the Cerbyd database and all required tables.
    Safe to run every time Cerbyd Web starts.
    """
    connection = get_db()
    try:
        connection.executescript(DATABASE_SCHEMA)
        connection.commit()
    finally:
        connection.close()


def database_execute(sql, parameters=(), fetch=False, many=False):
    """
    Small database helper used by Cerbyd's local APIs.
    """
    connection = get_db()

    try:
        cursor = connection.cursor()

        if many:
            cursor.executemany(sql, parameters)
        else:
            cursor.execute(sql, parameters)

        if fetch:
            rows = cursor.fetchall()
            return [dict(row) for row in rows]

        connection.commit()

        return cursor.lastrowid

    finally:
        connection.close()


def save_search_history(query, search_type, results_count, response_ms):
    """
    Stores a search event without allowing database failure to break
    the actual search engine.
    """
    try:
        database_execute(
            """
            INSERT INTO searches
                (query, search_type, results_count, response_ms)
            VALUES (?, ?, ?, ?)
            """,
            (
                query[:2000],
                search_type[:50],
                int(results_count),
                float(response_ms)
            )
        )
    except Exception as exc:
        print(f"[Cerbyd Database] Search history error: {exc}")


def save_network_test(
    speed_mbps,
    latency_ms,
    network_level,
    network_class,
    test_bytes
):
    """
    Stores a browser/server network measurement.
    """
    try:
        database_execute(
            """
            INSERT INTO network_tests
                (
                    speed_mbps,
                    latency_ms,
                    network_level,
                    network_class,
                    test_bytes
                )
            VALUES (?, ?, ?, ?, ?)
            """,
            (
                float(speed_mbps),
                float(latency_ms) if latency_ms is not None else None,
                str(network_level),
                str(network_class),
                int(test_bytes)
            )
        )
    except Exception as exc:
        print(f"[Cerbyd Database] Network history error: {exc}")


def database_count(table_name):
    """
    Returns counts for known internal tables only.
    """
    allowed = {
        "searches",
        "favorites",
        "network_tests",
        "settings",
        "users"
    }

    if table_name not in allowed:
        return 0

    try:
        rows = database_execute(
            f"SELECT COUNT(*) AS total FROM {table_name}",
            fetch=True
        )
        return int(rows[0]["total"]) if rows else 0
    except Exception:
        return 0



# ============================================================
# PUBLIC RELEASE RATE LIMITER
# ============================================================

_rate_lock = Lock()
_rate_buckets = defaultdict(deque)


def get_client_ip(request: Request):
    """Returns the socket peer address without trusting spoofed headers."""
    if request.client and request.client.host:
        return request.client.host
    return "unknown"


def rate_limit_for_path(path: str):
    if path in ("/api/auth/login", "/api/auth/register"):
        return 8
    if path in ("/api/search", "/api/answer"):
        return RATE_LIMIT_SEARCH
    if path == "/api/network-test":
        return RATE_LIMIT_NETWORK
    return RATE_LIMIT_DEFAULT


def allow_request(ip: str, path: str):
    """Small in-memory sliding-window limiter for public deployment."""
    now = time.monotonic()
    key = f"{ip}|{path}"
    limit = rate_limit_for_path(path)

    with _rate_lock:
        bucket = _rate_buckets[key]
        cutoff = now - RATE_LIMIT_WINDOW

        while bucket and bucket[0] <= cutoff:
            bucket.popleft()

        if len(bucket) >= limit:
            retry_after = max(1, int(RATE_LIMIT_WINDOW - (now - bucket[0])))
            return False, retry_after

        bucket.append(now)

        # Prevent an unbounded number of inactive client keys.
        if len(_rate_buckets) > 5000:
            stale = [
                k for k, values in _rate_buckets.items()
                if not values or values[-1] <= cutoff
            ]
            for stale_key in stale[:1000]:
                _rate_buckets.pop(stale_key, None)

    return True, 0


# ============================================================
# FASTAPI
# ============================================================

app = FastAPI(
    title=APP_NAME,
    version=APP_VERSION,
    description="Cerbyd Web search engine by Cerbyd Inc.",
)


# ============================================================
# CORS
# ============================================================

# A public search engine does not need credentialed wildcard CORS.
# By default the frontend and API are same-origin, while deployments
# can explicitly provide one or more allowed origins with
# CERBYD_CORS_ORIGINS.
app.add_middleware(
    CORSMiddleware,
    allow_origins=CORS_ORIGINS,
    allow_credentials=False,
    allow_methods=["GET", "POST", "DELETE", "OPTIONS"],
    allow_headers=["Content-Type", "Accept", "X-Requested-With"],
)

# Compression helps the HTML/JSON portal respond faster.
app.add_middleware(
    GZipMiddleware,
    minimum_size=1000,
)

# If a deployment supplies a host allow-list, it is enforced here.
# The default wildcard keeps local development and first deployment easy.
app.add_middleware(
    TrustedHostMiddleware,
    allowed_hosts=ALLOWED_HOSTS,
)


@app.middleware("http")
async def cerbyd_public_security(request: Request, call_next):
    """Rate-limit public APIs and attach safe response headers."""
    path = request.url.path

    if path.startswith("/api/") and path not in {
        "/api/network-info",
    }:
        allowed, retry_after = allow_request(
            get_client_ip(request),
            path,
        )

        if not allowed:
            return JSONResponse(
                status_code=429,
                content={
                    "success": False,
                    "error": "Too many requests. Please try again shortly.",
                    "retry_after_seconds": retry_after,
                    "service": APP_NAME,
                },
                headers={"Retry-After": str(retry_after)},
            )

    response = await call_next(request)

    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "SAMEORIGIN"
    response.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    response.headers["Permissions-Policy"] = "camera=(), microphone=(self), geolocation=()"
    response.headers["X-Cerbyd-Version"] = APP_VERSION

    if request.url.path.startswith("/api/"):
        response.headers["Cache-Control"] = "no-store"

    return response


# ============================================================
# CACHE ENGINE
# ============================================================

def cache_key(prefix, url, params=None):
    """
    Creates a stable cache key.
    """

    if params:
        encoded = urllib.parse.urlencode(
            sorted(params.items()),
            doseq=True
        )
    else:
        encoded = ""

    raw = f"{prefix}|{url}|{encoded}"

    return hashlib.sha256(
        raw.encode("utf-8")
    ).hexdigest()


def cache_get(key):
    """
    Gets a cached value if it has not expired.
    """

    now = time.time()

    with _cache_lock:

        item = _cache.get(key)

        if not item:
            return None

        timestamp, value = item

        if now - timestamp > CACHE_TTL:
            del _cache[key]
            return None

        return value


def cache_set(key, value):
    """
    Stores a value in the short-term Cerbyd cache.
    """

    now = time.time()

    with _cache_lock:

        if len(_cache) >= CACHE_MAX_ITEMS:

            oldest_key = min(
                _cache,
                key=lambda k: _cache[k][0]
            )

            _cache.pop(oldest_key, None)

        _cache[key] = (
            now,
            value
        )


def cache_clear():
    """
    Clears the Cerbyd cache.
    """

    with _cache_lock:
        _cache.clear()


# ============================================================
# REQUEST SESSION ENGINE
# ============================================================

def get_http_session():
    """
    Creates one requests.Session per worker thread.

    Reusing connections is considerably faster than creating
    a brand-new HTTP connection for every request.
    """

    session = getattr(
        _thread_local,
        "session",
        None
    )

    if session is None:

        session = requests.Session()
        session.headers.update(HEADERS)

        # Reuse pooled connections and retry transient upstream failures.
        # Keep retries small so failed providers do not make searches feel slow.
        retry = Retry(
            total=1,
            connect=1,
            read=0,
            backoff_factor=0.15,
            status_forcelist=(429, 500, 502, 503, 504),
            allowed_methods=frozenset(["GET"]),
            raise_on_status=False,
        )
        adapter = HTTPAdapter(
            pool_connections=24,
            pool_maxsize=24,
            max_retries=retry,
        )
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        _thread_local.session = session

    return session


# ============================================================
# NETWORK INFORMATION
# ============================================================

def get_network(query):
    """
    Legacy deterministic network detector.

    Kept for compatibility with older Cerbyd Web frontends.
    """

    if not query:
        return NETWORK_LEVELS[0]

    digest = hashlib.sha256(
        query.encode("utf-8")
    ).hexdigest()

    number = int(
        digest[:8],
        16
    )

    index = number % len(NETWORK_LEVELS)

    return NETWORK_LEVELS[index]


def get_network_from_speed(mbps):
    """
    Converts measured Mbps into Cerbyd's car/network system.
    """

    try:
        mbps = float(mbps)
    except Exception:
        mbps = 0

    for level in NETWORK_LEVELS:

        if (
            mbps >= level["min_mbps"]
            and mbps < level["max_mbps"]
        ):
            return level

    return NETWORK_LEVELS[-1]


# ============================================================
# NETWORK INFO API
# ============================================================

@app.get("/api/network-info")
def network_info():

    return {
        "success": True,
        "engine": APP_NAME,
        "version": APP_VERSION,
        "levels": NETWORK_LEVELS,
    }


# ============================================================
# NETWORK PING
# ============================================================

@app.get("/api/network-ping")
def network_ping():

    start = time.perf_counter()

    try:

        response = get_http_session().get(
            "https://www.google.com/generate_204",
            timeout=REQUEST_TIMEOUT,
            allow_redirects=False,
        )

        elapsed = (
            time.perf_counter() - start
        ) * 1000

        return {
            "success": True,
            "milliseconds": round(
                elapsed,
                2
            ),
            "status_code": response.status_code,
        }

    except Exception as exc:

        elapsed = (
            time.perf_counter() - start
        ) * 1000

        return {
            "success": False,
            "milliseconds": round(
                elapsed,
                2
            ),
            "error": str(exc),
        }


# ============================================================
# NETWORK SPEED TEST
# ============================================================

@app.get("/api/network-test")
def network_test(
    bytes: int = Query(
        default=5_000_000,
        ge=100_000,
        le=20_000_000
    ),
    cb: str = Query(
        default=""
    )
):

    size = int(bytes)

    # Generate deterministic but non-compressible-ish data.
    seed = hashlib.sha256(
        f"cerbyd-network-{size}".encode()
    ).digest()

    chunk_size = 64 * 1024

    def generate():

        remaining = size
        counter = 0

        while remaining > 0:

            current_size = min(
                chunk_size,
                remaining
            )

            block_seed = hashlib.sha256(
                seed +
                counter.to_bytes(
                    8,
                    "big"
                )
            ).digest()

            repeats = (
                current_size //
                len(block_seed)
            ) + 1

            block = (
                block_seed * repeats
            )[:current_size]

            yield block

            remaining -= current_size
            counter += 1

    return StreamingResponse(
        generate(),
        media_type="application/octet-stream",
        headers={
            "Cache-Control": (
                "no-store, no-cache, "
                "must-revalidate, max-age=0"
            ),
            "Pragma": "no-cache",
            "Expires": "0",
            "X-Cerbyd-Network-Test": "true",
            "X-Cerbyd-Test-Bytes": str(size),
        },
    )


# ============================================================
# NETWORK TEST RESULT RECORDING
# ============================================================

@app.post("/api/network-test-record")
def network_test_record(
    speed_mbps: float = Query(default=0, ge=0, le=100000),
    latency_ms: float | None = Query(default=None, ge=0, le=600000),
    test_bytes: int = Query(default=0, ge=0, le=20_000_000),
):
    """Stores the browser-measured speed without trusting server timing."""
    level = get_network_from_speed(speed_mbps)

    save_network_test(
        speed_mbps,
        latency_ms,
        level["name"],
        level["class"],
        test_bytes,
    )

    return {
        "success": True,
        "speed_mbps": round(float(speed_mbps), 2),
        "latency_ms": round(float(latency_ms), 2) if latency_ms is not None else None,
        "network": level,
    }



# ============================================================
# ACCOUNT AUTHENTICATION
# ============================================================

AUTH_SESSION_SECONDS = 60 * 60 * 24 * 30
AUTH_COOKIE_NAME = "cerbyd_session"


def _password_hash(password: str) -> str:
    """Hash passwords with scrypt and a unique random salt."""
    salt = secrets.token_bytes(16)
    digest = hashlib.scrypt(
        password.encode("utf-8"),
        salt=salt,
        n=2**14,
        r=8,
        p=1,
        dklen=32,
    )
    return "scrypt${}${}${}${}${}".format(
        2**14, 8, 1, salt.hex(), digest.hex()
    )


def _password_matches(password: str, encoded: str) -> bool:
    try:
        scheme, n, r, p, salt_hex, digest_hex = encoded.split("$", 5)
        if scheme != "scrypt":
            return False
        expected = bytes.fromhex(digest_hex)
        actual = hashlib.scrypt(
            password.encode("utf-8"),
            salt=bytes.fromhex(salt_hex),
            n=int(n),
            r=int(r),
            p=int(p),
            dklen=len(expected),
        )
        return hmac.compare_digest(actual, expected)
    except (ValueError, TypeError, MemoryError):
        return False


def _auth_user_public(row):
    if not row:
        return None
    return {
        "username": row["username"],
        "email": row["email"],
        "created_at": row["created_at"],
    }


def _auth_cookie_secure(request: Request) -> bool:
    # Uvicorn's proxy-header support should expose HTTPS in request.url.scheme.
    # The environment override is useful on managed platforms where the
    # reverse-proxy scheme is not forwarded to the application.
    return (
        request.url.scheme == "https"
        or os.getenv("CERBYD_COOKIE_SECURE", "").strip().lower() == "true"
    )


def _create_auth_session(user_id: int, request: Request):
    raw_token = secrets.token_urlsafe(32)
    token_hash = hashlib.sha256(raw_token.encode("utf-8")).hexdigest()
    expires_at = int(time.time()) + AUTH_SESSION_SECONDS
    connection = get_db()
    try:
        connection.execute(
            "DELETE FROM auth_sessions WHERE expires_at < ?",
            (int(time.time()),),
        )
        connection.execute(
            "INSERT INTO auth_sessions (token_hash, user_id, expires_at) VALUES (?, ?, ?)",
            (token_hash, user_id, expires_at),
        )
        connection.commit()
    finally:
        connection.close()

    response = JSONResponse({
        "success": True,
        "user": _auth_user_by_id(user_id),
    })
    response.set_cookie(
        key=AUTH_COOKIE_NAME,
        value=raw_token,
        max_age=AUTH_SESSION_SECONDS,
        httponly=True,
        secure=_auth_cookie_secure(request),
        samesite="lax",
        path="/",
    )
    return response


def _auth_user_by_id(user_id: int):
    rows = database_execute(
        "SELECT username, email, created_at FROM users WHERE id = ?",
        (user_id,),
        fetch=True,
    )
    return _auth_user_public(rows[0]) if rows else None


def _current_auth_user(request: Request):
    token = request.cookies.get(AUTH_COOKIE_NAME, "")
    if not token or len(token) > 200:
        return None
    token_hash = hashlib.sha256(token.encode("utf-8")).hexdigest()
    now = int(time.time())
    connection = get_db()
    try:
        row = connection.execute(
            """
            SELECT users.id, users.username, users.email, users.created_at
            FROM auth_sessions
            JOIN users ON users.id = auth_sessions.user_id
            WHERE auth_sessions.token_hash = ? AND auth_sessions.expires_at > ?
            """,
            (token_hash, now),
        ).fetchone()
        if row:
            return dict(row)
        connection.execute(
            "DELETE FROM auth_sessions WHERE token_hash = ? OR expires_at <= ?",
            (token_hash, now),
        )
        connection.commit()
        return None
    finally:
        connection.close()


@app.post("/api/auth/register")
async def api_auth_register(request: Request):
    try:
        payload = await request.json()
    except Exception:
        payload = {}

    if not isinstance(payload, dict):
        payload = {}

    username = str(payload.get("username", "")).strip()
    email = str(payload.get("email", "")).strip().lower()
    password = payload.get("password", "")

    if not re.fullmatch(r"[A-Za-z0-9_.-]{3,32}", username):
        return JSONResponse(status_code=400, content={
            "success": False,
            "error": "Username must be 3–32 characters and use letters, numbers, dots, underscores, or hyphens.",
        })
    if len(email) > 254 or not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email):
        return JSONResponse(status_code=400, content={
            "success": False, "error": "Enter a valid email address."
        })
    if not isinstance(password, str) or len(password) < 8 or len(password) > 128:
        return JSONResponse(status_code=400, content={
            "success": False, "error": "Password must be between 8 and 128 characters."
        })

    encoded_password = _password_hash(password)
    connection = get_db()
    try:
        cursor = connection.execute(
            "INSERT INTO users (username, email, password_hash) VALUES (?, ?, ?)",
            (username, email, encoded_password),
        )
        user_id = cursor.lastrowid
        connection.commit()
    except sqlite3.IntegrityError:
        connection.rollback()
        return JSONResponse(status_code=409, content={
            "success": False,
            "error": "That username or email is already registered. Try signing in instead.",
        })
    except Exception:
        connection.rollback()
        return JSONResponse(status_code=500, content={
            "success": False, "error": "Could not create your account right now."
        })
    finally:
        connection.close()

    return _create_auth_session(int(user_id), request)


@app.post("/api/auth/login")
async def api_auth_login(request: Request):
    try:
        payload = await request.json()
    except Exception:
        payload = {}

    if not isinstance(payload, dict):
        payload = {}

    email = str(payload.get("email", "")).strip().lower()
    password = payload.get("password", "")

    if not isinstance(password, str) or not email or len(password) > 128:
        return JSONResponse(status_code=400, content={
            "success": False, "error": "Enter your email address and password."
        })

    rows = database_execute(
        "SELECT id, username, email, password_hash, created_at FROM users WHERE email = ?",
        (email,),
        fetch=True,
    )
    row = rows[0] if rows else None

    # Do comparable password-hash work for unknown emails to reduce timing clues.
    if row:
        valid = _password_matches(password, row["password_hash"])
    else:
        _password_hash(password[:128] or "invalid-placeholder-password")
        valid = False

    if not valid:
        return JSONResponse(status_code=401, content={
            "success": False, "error": "Email or password is incorrect."
        })

    return _create_auth_session(int(row["id"]), request)


@app.get("/api/auth/me")
def api_auth_me(request: Request):
    user = _current_auth_user(request)
    if not user:
        return JSONResponse(status_code=401, content={
            "success": False, "error": "You are not signed in."
        })
    return {
        "success": True,
        "user": {
            "username": user["username"],
            "email": user["email"],
            "created_at": user["created_at"],
        },
    }


@app.post("/api/auth/logout")
def api_auth_logout(request: Request):
    token = request.cookies.get(AUTH_COOKIE_NAME, "")
    if token and len(token) <= 200:
        token_hash = hashlib.sha256(token.encode("utf-8")).hexdigest()
        database_execute(
            "DELETE FROM auth_sessions WHERE token_hash = ?",
            (token_hash,),
        )

    response = JSONResponse({"success": True, "message": "Signed out."})
    response.delete_cookie(
        key=AUTH_COOKIE_NAME,
        path="/",
        httponly=True,
        secure=_auth_cookie_secure(request),
        samesite="lax",
    )
    return response


# ============================================================
# OAUTH SIGN-IN (GOOGLE, MICROSOFT, APPLE)
# ============================================================

OAUTH_PROVIDERS = {"google", "microsoft", "apple"}
OAUTH_STATE_SECONDS = 600


def _oauth_public_url(request: Request) -> str:
    configured = os.getenv("CERBYD_PUBLIC_URL", "").strip().rstrip("/")
    return configured or str(request.base_url).rstrip("/")


def _oauth_redirect_uri(request: Request, provider: str) -> str:
    return _oauth_public_url(request) + f"/auth/{provider}/callback"


def _oauth_provider_ready(provider: str) -> bool:
    if provider == "google":
        return bool(os.getenv("GOOGLE_CLIENT_ID") and os.getenv("GOOGLE_CLIENT_SECRET"))
    if provider == "microsoft":
        return bool(os.getenv("MICROSOFT_CLIENT_ID") and os.getenv("MICROSOFT_CLIENT_SECRET"))
    if provider == "apple":
        return bool(os.getenv("APPLE_CLIENT_ID") and os.getenv("APPLE_TEAM_ID") and os.getenv("APPLE_KEY_ID") and os.getenv("APPLE_PRIVATE_KEY"))
    return False


def _oauth_error_page(message: str, status_code: int = 400):
    safe = html.escape(message)
    page = f"""<!doctype html><html lang=\"en\"><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><title>Cerbyd sign-in</title><body style=\"font:16px Arial,sans-serif;max-width:620px;margin:10vh auto;padding:24px;color:#222;background:#f5f5f5\"><main style=\"background:white;border:1px solid #bbb;padding:24px\"><h1 style=\"font-size:24px\">Cerbyd sign-in</h1><p>{safe}</p><p><a href=\"/\">Return to Cerbyd Web</a></p></main></body></html>"""
    from fastapi.responses import HTMLResponse
    return HTMLResponse(page, status_code=status_code)


def _oauth_provider_config(provider: str, request: Request):
    if provider == "google":
        return {
            "client_id": os.getenv("GOOGLE_CLIENT_ID", "").strip(),
            "client_secret": os.getenv("GOOGLE_CLIENT_SECRET", "").strip(),
            "authorize": "https://accounts.google.com/o/oauth2/v2/auth",
            "token": "https://oauth2.googleapis.com/token",
            "jwks": "https://www.googleapis.com/oauth2/v3/certs",
            "issuer": ["https://accounts.google.com", "accounts.google.com"],
            "scope": "openid email profile",
        }
    if provider == "microsoft":
        tenant = os.getenv("MICROSOFT_TENANT", "common").strip() or "common"
        metadata_url = f"https://login.microsoftonline.com/{urllib.parse.quote(tenant, safe='')}/v2.0/.well-known/openid-configuration"
        metadata_response = requests.get(metadata_url, timeout=10)
        metadata_response.raise_for_status()
        metadata = metadata_response.json()
        return {
            "client_id": os.getenv("MICROSOFT_CLIENT_ID", "").strip(),
            "client_secret": os.getenv("MICROSOFT_CLIENT_SECRET", "").strip(),
            "authorize": metadata["authorization_endpoint"],
            "token": metadata["token_endpoint"],
            "jwks": metadata["jwks_uri"],
            "issuer": metadata.get("issuer", ""),
            "scope": "openid email profile",
            "tenant": tenant,
        }
    if provider == "apple":
        return {
            "client_id": os.getenv("APPLE_CLIENT_ID", "").strip(),
            "client_secret": _apple_client_secret(),
            "authorize": "https://appleid.apple.com/auth/authorize",
            "token": "https://appleid.apple.com/auth/token",
            "jwks": "https://appleid.apple.com/auth/keys",
            "issuer": "https://appleid.apple.com",
            "scope": "name email",
        }
    raise ValueError("Unsupported sign-in provider.")


def _apple_client_secret() -> str:
    private_key = os.getenv("APPLE_PRIVATE_KEY", "").strip()
    if not private_key:
        raise ValueError("Apple private key is not configured.")
    if "-----BEGIN" not in private_key:
        import base64
        private_key = base64.b64decode(private_key).decode("utf-8")
    private_key = private_key.replace("\\n", "\n")
    now = int(time.time())
    return jwt.encode(
        {"iss": os.getenv("APPLE_TEAM_ID", "").strip(), "iat": now, "exp": now + 86400 * 150,
         "aud": "https://appleid.apple.com", "sub": os.getenv("APPLE_CLIENT_ID", "").strip()},
        private_key,
        algorithm="ES256",
        headers={"kid": os.getenv("APPLE_KEY_ID", "").strip()},
    )


def _oauth_store_state(state: str, provider: str, link_user_id=None):
    now = int(time.time())
    database_execute("DELETE FROM oauth_states WHERE expires_at <= ?", (now,))
    database_execute(
        "INSERT INTO oauth_states (state_hash, provider, link_user_id, expires_at) VALUES (?, ?, ?, ?)",
        (hashlib.sha256(state.encode()).hexdigest(), provider, link_user_id, now + OAUTH_STATE_SECONDS),
    )


def _oauth_consume_state(state: str, provider: str):
    if not state or len(state) > 300:
        return None
    digest = hashlib.sha256(state.encode()).hexdigest()
    connection = get_db()
    try:
        row = connection.execute(
            "SELECT provider, link_user_id, expires_at FROM oauth_states WHERE state_hash = ?",
            (digest,),
        ).fetchone()
        connection.execute("DELETE FROM oauth_states WHERE state_hash = ?", (digest,))
        connection.commit()
        if not row or row["provider"] != provider or int(row["expires_at"]) <= int(time.time()):
            return None
        return {"link_user_id": row["link_user_id"]}
    finally:
        connection.close()


def _oauth_token_claims(provider: str, id_token: str, config: dict):
    jwks_client = jwt.PyJWKClient(config["jwks"], timeout=10)
    signing_key = jwks_client.get_signing_key_from_jwt(id_token).key
    options = {"require": ["exp", "iat", "sub", "aud"], "verify_aud": True, "verify_iss": provider != "microsoft"}
    claims = jwt.decode(
        id_token, signing_key, algorithms=["RS256", "ES256"],
        audience=config["client_id"], issuer=config["issuer"] if provider != "microsoft" else None,
        options=options, leeway=60,
    )
    if provider == "microsoft":
        issuer = str(claims.get("iss", ""))
        tenant_id = str(claims.get("tid", ""))
        if not tenant_id or issuer != f"https://login.microsoftonline.com/{tenant_id}/v2.0":
            raise ValueError("Microsoft returned an invalid identity issuer.")
        if config.get("tenant") not in ("common", "organizations", "consumers", tenant_id):
            raise ValueError("This Microsoft account is outside the configured tenant.")
    if not claims.get("sub"):
        raise ValueError("The identity provider did not return a user identifier.")
    return claims


def _oauth_username(name: str, email: str) -> str:
    base = re.sub(r"[^A-Za-z0-9_.-]", "", (name or email.split("@")[0] or "cerbyduser"))[:24]
    if len(base) < 3:
        base = (base + "user")[:24]
    candidate = base
    for suffix in range(1, 10000):
        rows = database_execute("SELECT id FROM users WHERE username = ? COLLATE NOCASE", (candidate,), fetch=True)
        if not rows:
            return candidate
        candidate = f"{base[:25-len(str(suffix))]}{suffix}"
    return f"user{secrets.token_hex(6)}"


def _oauth_find_or_create_user(provider: str, claims: dict, link_user_id=None):
    subject = str(claims.get("sub", ""))
    email = str(claims.get("email") or claims.get("preferred_username") or "").strip().lower()
    verified = claims.get("email_verified", False)
    email_verified = verified is True or str(verified).lower() == "true"
    display_name = str(claims.get("name") or claims.get("given_name") or "").strip()
    if not email or len(email) > 254 or not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email):
        raise ValueError("The provider did not return a usable email address. Please use email-and-password sign-in or try another provider.")
    if provider in ("google", "apple") and not email_verified:
        raise ValueError("The provider did not verify this email address, so Cerbyd cannot use it for sign-in.")

    existing = database_execute("SELECT user_id FROM oauth_accounts WHERE provider = ? AND subject = ?", (provider, subject), fetch=True)
    if existing:
        user_id = int(existing[0]["user_id"])
        if link_user_id is not None and user_id != int(link_user_id):
            raise ValueError("This provider account is already connected to a different Cerbyd account.")
        return user_id

    if link_user_id is not None:
        user = database_execute("SELECT id FROM users WHERE id = ?", (int(link_user_id),), fetch=True)
        if not user:
            raise ValueError("The Cerbyd account to link no longer exists. Please sign in again.")
        database_execute(
            "INSERT INTO oauth_accounts (provider, subject, user_id, provider_email) VALUES (?, ?, ?, ?)",
            (provider, subject, int(link_user_id), email),
        )
        return int(link_user_id)

    existing_email = database_execute("SELECT id FROM users WHERE email = ? COLLATE NOCASE", (email,), fetch=True)
    if existing_email:
        raise ValueError("A Cerbyd account already uses this email. Sign in to that account first, then use its Connect sign-in provider option to link this account securely.")

    username = _oauth_username(display_name, email)
    # OAuth-only users have an empty password hash and cannot use password login until they set one.
    connection = get_db()
    try:
        cursor = connection.execute(
            "INSERT INTO users (username, email, password_hash) VALUES (?, ?, '')",
            (username, email),
        )
        user_id = int(cursor.lastrowid)
        connection.execute(
            "INSERT INTO oauth_accounts (provider, subject, user_id, provider_email) VALUES (?, ?, ?, ?)",
            (provider, subject, user_id, email),
        )
        connection.commit()
        return user_id
    except Exception:
        connection.rollback()
        raise
    finally:
        connection.close()


@app.get("/api/auth/providers")
def api_auth_providers():
    return {"success": True, "providers": {provider: _oauth_provider_ready(provider) for provider in sorted(OAUTH_PROVIDERS)}}


@app.get("/auth/{provider}/start")
def oauth_start(provider: str, request: Request):
    provider = provider.lower()
    if provider not in OAUTH_PROVIDERS:
        return _oauth_error_page("That sign-in provider is not supported.", 404)
    if not _oauth_provider_ready(provider):
        return _oauth_error_page(f"{provider.title()} sign-in is not configured yet. The site owner must add the provider credentials as environment variables and register this exact callback URL: {_oauth_redirect_uri(request, provider)}.", 503)
    try:
        config = _oauth_provider_config(provider, request)
        state = secrets.token_urlsafe(32)
        _oauth_store_state(state, provider)
        params = {
            "client_id": config["client_id"], "redirect_uri": _oauth_redirect_uri(request, provider),
            "response_type": "code", "scope": config["scope"], "state": state,
        }
        if provider == "google":
            params["prompt"] = "select_account"
        elif provider == "microsoft":
            params["response_mode"] = "query"
        elif provider == "apple":
            params["response_mode"] = "form_post"
        url = config["authorize"] + "?" + urllib.parse.urlencode(params)
        from fastapi.responses import RedirectResponse
        response = RedirectResponse(url, status_code=302)
        return response
    except Exception as exc:
        print(f"[Cerbyd OAuth] {provider} start failed: {exc}")
        return _oauth_error_page(f"Could not start {provider.title()} sign-in. Check the provider configuration and server logs.", 503)


@app.get("/auth/{provider}/link")
def oauth_link_start(provider: str, request: Request):
    provider = provider.lower()
    if provider not in OAUTH_PROVIDERS:
        return _oauth_error_page("That sign-in provider is not supported.", 404)
    current = _current_auth_user(request)
    if not current:
        from fastapi.responses import RedirectResponse
        return RedirectResponse("/?auth=login", status_code=302)
    if not _oauth_provider_ready(provider):
        return _oauth_error_page(f"{provider.title()} sign-in is not configured yet. Register this callback URL: {_oauth_redirect_uri(request, provider)}.", 503)
    try:
        config = _oauth_provider_config(provider, request)
        state = secrets.token_urlsafe(32)
        _oauth_store_state(state, provider, int(current["id"]))
        params = {"client_id": config["client_id"], "redirect_uri": _oauth_redirect_uri(request, provider), "response_type": "code", "scope": config["scope"], "state": state}
        if provider == "google": params["prompt"] = "select_account"
        if provider == "microsoft": params["response_mode"] = "query"
        if provider == "apple": params["response_mode"] = "form_post"
        from fastapi.responses import RedirectResponse
        return RedirectResponse(config["authorize"] + "?" + urllib.parse.urlencode(params), status_code=302)
    except Exception as exc:
        print(f"[Cerbyd OAuth] {provider} link start failed: {exc}")
        return _oauth_error_page(f"Could not start {provider.title()} account linking. Check the provider configuration.", 503)


async def _oauth_callback(provider: str, request: Request, code: str = "", state: str = "", error: str = ""):
    if error:
        return _oauth_error_page(f"The identity provider cancelled or rejected sign-in ({error[:120]}).", 400)
    state_info = _oauth_consume_state(state, provider)
    if not state_info:
        return _oauth_error_page("This sign-in request expired or could not be verified. Please return to Cerbyd and try again.", 400)
    if not _oauth_provider_ready(provider):
        return _oauth_error_page(f"{provider.title()} sign-in is not configured on this server.", 503)
    if not code or len(code) > 4096:
        return _oauth_error_page("The identity provider did not return a valid authorization code.", 400)
    try:
        config = _oauth_provider_config(provider, request)
        token_response = requests.post(config["token"], data={
            "grant_type": "authorization_code", "code": code,
            "redirect_uri": _oauth_redirect_uri(request, provider),
            "client_id": config["client_id"], "client_secret": config["client_secret"],
        }, headers={"Accept": "application/json"}, timeout=15)
        token_response.raise_for_status()
        token_data = token_response.json()
        id_token = token_data.get("id_token", "")
        if not id_token:
            raise ValueError("The provider did not return an identity token.")
        claims = _oauth_token_claims(provider, id_token, config)
        # Microsoft often uses preferred_username; Google/Apple include email in the ID token.
        if not claims.get("email") and provider == "microsoft":
            claims["email"] = claims.get("preferred_username", "")
        user_id = _oauth_find_or_create_user(provider, claims, state_info.get("link_user_id"))
        from fastapi.responses import RedirectResponse
        response = RedirectResponse("/", status_code=303)
        session_response = _create_auth_session(user_id, request)
        for key, value in session_response.headers.items():
            if key.lower() == "set-cookie":
                response.headers.append(key, value)
        return response
    except ValueError as exc:
        return _oauth_error_page(str(exc), 400)
    except requests.RequestException as exc:
        print(f"[Cerbyd OAuth] {provider} token exchange failed: {exc}")
        return _oauth_error_page(f"Could not verify the {provider.title()} sign-in response. Please try again.", 502)
    except Exception as exc:
        print(f"[Cerbyd OAuth] {provider} callback failed: {exc}")
        return _oauth_error_page(f"Could not complete {provider.title()} sign-in. Check the provider settings and try again.", 400)


@app.get("/auth/google/callback")
async def oauth_google_callback(request: Request, code: str = "", state: str = "", error: str = ""):
    return await _oauth_callback("google", request, code, state, error)


@app.get("/auth/microsoft/callback")
async def oauth_microsoft_callback(request: Request, code: str = "", state: str = "", error: str = ""):
    return await _oauth_callback("microsoft", request, code, state, error)


@app.get("/auth/apple/callback")
async def oauth_apple_callback(request: Request, code: str = "", state: str = "", error: str = ""):
    # Apple may use response_mode=form_post; FastAPI receives the form fields here.
    if request.method == "POST":
        try:
            form = await request.form()
            code = str(form.get("code", code))
            state = str(form.get("state", state))
            error = str(form.get("error", error))
        except Exception:
            pass
    return await _oauth_callback("apple", request, code, state, error)


@app.post("/auth/apple/callback")
async def oauth_apple_callback_post(request: Request):
    try:
        form = await request.form()
        code = str(form.get("code", ""))
        state = str(form.get("state", ""))
        error = str(form.get("error", ""))
    except Exception:
        code = state = error = ""
    return await _oauth_callback("apple", request, code, state, error)


# ============================================================
# SAFE URL HANDLING
# ============================================================

def clean_url(url):
    """
    Ensures a URL has a valid HTTP/HTTPS scheme.
    """

    if not url:
        return None

    url = url.strip()

    if not url:
        return None

    parsed = urllib.parse.urlparse(url)

    if parsed.scheme in (
        "http",
        "https"
    ):
        return url

    if (
        " " not in url
        and "." in url
    ):
        return "https://" + url

    return None


def safe_external_url(url):
    """
    Basic protection against malformed external URLs.
    """

    cleaned = clean_url(url)

    if not cleaned:
        return None

    try:

        parsed = urllib.parse.urlparse(
            cleaned
        )

        if parsed.scheme not in (
            "http",
            "https"
        ):
            return None

        if not parsed.netloc:
            return None

        return cleaned

    except Exception:

        return None


# ============================================================
# DATABASE API - SEARCH HISTORY
# ============================================================

@app.get("/api/history")
def api_history(
    limit: int = Query(default=50, ge=1, le=200)
):
    rows = database_execute(
        """
        SELECT
            id,
            query,
            search_type,
            results_count,
            response_ms,
            created_at
        FROM searches
        ORDER BY id DESC
        LIMIT ?
        """,
        (limit,),
        fetch=True
    )

    return {
        "success": True,
        "results": rows,
        "count": len(rows)
    }


@app.delete("/api/history")
def api_history_clear():
    database_execute("DELETE FROM searches")

    return {
        "success": True,
        "message": "Cerbyd search history cleared."
    }


@app.delete("/api/history/{history_id}")
def api_history_delete(history_id: int):
    database_execute(
        "DELETE FROM searches WHERE id = ?",
        (history_id,)
    )

    return {
        "success": True,
        "id": history_id
    }


# ============================================================
# DATABASE API - FAVORITES
# ============================================================

@app.get("/api/favorites")
def api_favorites(
    limit: int = Query(default=100, ge=1, le=500)
):
    rows = database_execute(
        """
        SELECT
            id,
            title,
            url,
            description,
            created_at
        FROM favorites
        ORDER BY id DESC
        LIMIT ?
        """,
        (limit,),
        fetch=True
    )

    return {
        "success": True,
        "results": rows,
        "count": len(rows)
    }


@app.post("/api/favorites")
def api_add_favorite(
    title: str = Query(default=""),
    url: str = Query(default=""),
    description: str = Query(default="")
):
    title = title.strip()[:500]
    url = safe_external_url(url)
    description = description.strip()[:2000]

    if not title or not url:
        return JSONResponse(
            status_code=400,
            content={
                "success": False,
                "error": "A title and valid URL are required."
            }
        )

    try:
        database_execute(
            """
            INSERT INTO favorites
                (title, url, description)
            VALUES (?, ?, ?)
            ON CONFLICT(url) DO UPDATE SET
                title = excluded.title,
                description = excluded.description
            """,
            (title, url, description)
        )

        rows = database_execute(
            """
            SELECT id, title, url, description, created_at
            FROM favorites
            WHERE url = ?
            """,
            (url,),
            fetch=True
        )

        return {
            "success": True,
            "favorite": rows[0] if rows else None
        }

    except Exception as exc:
        return JSONResponse(
            status_code=500,
            content={
                "success": False,
                "error": str(exc)
            }
        )


@app.delete("/api/favorites/{favorite_id}")
def api_delete_favorite(favorite_id: int):
    database_execute(
        "DELETE FROM favorites WHERE id = ?",
        (favorite_id,)
    )

    return {
        "success": True,
        "id": favorite_id
    }


@app.delete("/api/favorites")
def api_clear_favorites():
    database_execute("DELETE FROM favorites")

    return {
        "success": True,
        "message": "Cerbyd favorites cleared."
    }


# ============================================================
# DATABASE API - NETWORK HISTORY
# ============================================================

@app.get("/api/network-history")
def api_network_history(
    limit: int = Query(default=50, ge=1, le=200)
):
    rows = database_execute(
        """
        SELECT
            id,
            speed_mbps,
            latency_ms,
            network_level,
            network_class,
            test_bytes,
            created_at
        FROM network_tests
        ORDER BY id DESC
        LIMIT ?
        """,
        (limit,),
        fetch=True
    )

    return {
        "success": True,
        "results": rows,
        "count": len(rows)
    }


@app.delete("/api/network-history")
def api_network_history_clear():
    database_execute("DELETE FROM network_tests")

    return {
        "success": True,
        "message": "Cerbyd network history cleared."
    }


# ============================================================
# DATABASE API - SETTINGS
# ============================================================

@app.get("/api/settings")
def api_settings():
    rows = database_execute(
        """
        SELECT key, value, updated_at
        FROM settings
        ORDER BY key
        """,
        fetch=True
    )

    return {
        "success": True,
        "settings": {
            row["key"]: row["value"]
            for row in rows
        },
        "details": rows
    }


@app.get("/api/settings/{key}")
def api_get_setting(key: str):
    key = key.strip()[:100]

    rows = database_execute(
        """
        SELECT key, value, updated_at
        FROM settings
        WHERE key = ?
        """,
        (key,),
        fetch=True
    )

    if not rows:
        return {
            "success": True,
            "found": False,
            "key": key,
            "value": None
        }

    return {
        "success": True,
        "found": True,
        "setting": rows[0]
    }


@app.post("/api/settings")
def api_set_setting(
    key: str = Query(default=""),
    value: str = Query(default="")
):
    key = key.strip()[:100]
    value = value[:5000]

    if not key:
        return JSONResponse(
            status_code=400,
            content={
                "success": False,
                "error": "Setting key is required."
            }
        )

    database_execute(
        """
        INSERT INTO settings (key, value, updated_at)
        VALUES (?, ?, CURRENT_TIMESTAMP)
        ON CONFLICT(key) DO UPDATE SET
            value = excluded.value,
            updated_at = CURRENT_TIMESTAMP
        """,
        (key, value)
    )

    return {
        "success": True,
        "key": key,
        "value": value
    }


# ============================================================
# DATABASE API - DATABASE STATUS
# ============================================================

@app.get("/api/database")
def api_database():
    database_file_exists = DATABASE_FILE.exists()

    return {
        "success": True,
        "database": {
            "engine": "SQLite",
            "file": DATABASE_FILE.name,
            "path": DATABASE_FILE.name,
            "exists": database_file_exists
        },
        "tables": {
            "searches": database_count("searches"),
            "favorites": database_count("favorites"),
            "network_tests": database_count("network_tests"),
            "settings": database_count("settings"),
            "users": database_count("users")
        }
    }



# ============================================================
# HTTP TEXT REQUEST
# ============================================================

def request_text(
    url,
    params=None,
    timeout=REQUEST_TIMEOUT,
    cache_prefix="text"
):

    key = cache_key(
        cache_prefix,
        url,
        params
    )

    cached = cache_get(key)

    if cached is not None:
        return cached

    try:

        response = get_http_session().get(
            url,
            params=params,
            timeout=(min(CONNECT_TIMEOUT, timeout), timeout)
        )

        response.raise_for_status()

        value = response.text

        cache_set(
            key,
            value
        )

        return value

    except Exception:

        return None


# ============================================================
# HTTP JSON REQUEST
# ============================================================

def request_json(
    url,
    params=None,
    timeout=REQUEST_TIMEOUT,
    cache_prefix="json"
):

    key = cache_key(
        cache_prefix,
        url,
        params
    )

    cached = cache_get(key)

    if cached is not None:
        return cached

    try:

        response = get_http_session().get(
            url,
            params=params,
            timeout=(min(CONNECT_TIMEOUT, timeout), timeout)
        )

        response.raise_for_status()

        value = response.json()

        cache_set(
            key,
            value
        )

        return value

    except Exception:

        return None


# ============================================================
# DUCKDUCKGO WEB SEARCH
# ============================================================

def duckduckgo_search(query):

    url = (
        "https://html.duckduckgo.com/html/"
    )

    params = {
        "q": query
    }

    text = request_text(
        url,
        params=params,
        cache_prefix="ddg"
    )

    if not text:
        return []

    soup = BeautifulSoup(
        text,
        "html.parser"
    )

    results = []

    for result in soup.select(
        ".result"
    )[:10]:

        title_element = result.select_one(
            ".result__title"
        )

        link_element = result.select_one(
            ".result__a"
        )

        snippet_element = result.select_one(
            ".result__snippet"
        )

        if not link_element:
            continue

        title = (
            title_element.get_text(
                " ",
                strip=True
            )
            if title_element
            else link_element.get_text(
                " ",
                strip=True
            )
        )

        href = (
            link_element.get("href")
            or ""
        )

        snippet = (
            snippet_element.get_text(
                " ",
                strip=True
            )
            if snippet_element
            else ""
        )

        if not title:
            continue

        results.append(
            {
                "title": title,
                "url": href,
                "snippet": snippet,
            }
        )

    return results


# ============================================================
# BING WEB SEARCH FALLBACK
# ============================================================

def bing_search(query):

    url = (
        "https://www.bing.com/search"
    )

    params = {
        "q": query
    }

    text = request_text(
        url,
        params=params,
        cache_prefix="bing"
    )

    if not text:
        return []

    soup = BeautifulSoup(
        text,
        "html.parser"
    )

    results = []

    for item in soup.select(
        "li.b_algo"
    )[:10]:

        heading = item.select_one(
            "h2"
        )

        link = (
            heading.find("a")
            if heading
            else None
        )

        paragraph = item.select_one(
            ".b_caption p"
        )

        if not link:
            continue

        results.append(
            {
                "title": link.get_text(
                    " ",
                    strip=True
                ),
                "url": link.get(
                    "href",
                    ""
                ),
                "snippet": (
                    paragraph.get_text(
                        " ",
                        strip=True
                    )
                    if paragraph
                    else ""
                ),
            }
        )

    return results


# ============================================================
# CERBYD WEB SEARCH
# ============================================================

def _normalise_result_url(url):
    """Unwrap common search-engine redirect URLs and reject non-web links."""
    if not url:
        return ""
    url = html.unescape(str(url).strip())
    parsed = urllib.parse.urlparse(url)
    if parsed.hostname and ("duckduckgo.com" in parsed.hostname):
        values = urllib.parse.parse_qs(parsed.query)
        target = values.get("uddg", [None])[0]
        if target:
            url = urllib.parse.unquote(target)
    cleaned = safe_external_url(url)
    return cleaned or ""


def web_search(query):
    """Search multiple providers concurrently, merge and deduplicate results."""
    query = " ".join(str(query or "").split())[:MAX_QUERY_LENGTH]
    if not query:
        return []

    tasks = {
        CERBYD_EXECUTOR.submit(duckduckgo_search, query): "duckduckgo",
        CERBYD_EXECUTOR.submit(bing_search, query): "bing",
    }
    merged = []
    seen_urls = set()
    seen_titles = set()

    # Use whichever provider responds first; do not wait for a slow provider
    # once enough useful results have arrived.
    for future in as_completed(tasks):
        try:
            batch = future.result()
        except Exception:
            batch = []
        for item in batch or []:
            url = _normalise_result_url(item.get("url", ""))
            title = " ".join(str(item.get("title", "")).split())
            if not title or not url:
                continue
            title_key = re.sub(r"\W+", " ", title.lower()).strip()
            if url in seen_urls or (title_key and title_key in seen_titles):
                continue
            seen_urls.add(url)
            if title_key:
                seen_titles.add(title_key)
            merged.append({
                "title": title[:500],
                "url": url,
                "snippet": " ".join(str(item.get("snippet", "")).split())[:2000],
                "source": urllib.parse.urlparse(url).hostname or "Web",
            })
            if len(merged) >= MAX_WEB_RESULTS:
                break
        if len(merged) >= MAX_WEB_RESULTS:
            for pending in tasks:
                pending.cancel()
            break

    return merged[:MAX_WEB_RESULTS]


# ============================================================
# IMAGE SEARCH
# ============================================================

def image_search(query):
    """Return a larger set of image results with full image and thumbnail URLs."""
    query = " ".join(str(query or "").split())[:MAX_QUERY_LENGTH]
    if not query:
        return []

    url = "https://www.bing.com/images/search"
    text = request_text(
        url,
        params={"q": query, "form": "HDRSC2", "first": "1", "count": str(MAX_IMAGE_RESULTS)},
        cache_prefix="images-v2",
        timeout=REQUEST_TIMEOUT,
    )
    if not text:
        return []

    soup = BeautifulSoup(text, "html.parser")
    results, seen = [], set()

    # Bing's image result metadata usually carries both thumbnail and original URLs.
    for element in soup.select("a.iusc"):
        metadata = element.get("m")
        if not metadata:
            continue
        try:
            data = json.loads(html.unescape(metadata))
        except (ValueError, TypeError):
            continue

        image_url = data.get("murl") or data.get("turl")
        thumbnail = data.get("turl") or image_url
        page_url = data.get("purl") or ""
        title = data.get("t") or data.get("desc") or query
        if not image_url:
            continue
        image_url = _normalise_result_url(image_url)
        thumbnail = _normalise_result_url(thumbnail) or image_url
        page_url = _normalise_result_url(page_url)
        if not image_url or image_url in seen:
            continue
        seen.add(image_url)
        results.append({
            "title": BeautifulSoup(str(title), "html.parser").get_text(" ", strip=True)[:500],
            "image": image_url,
            "url": page_url,
            "thumbnail": thumbnail,
            "source": urllib.parse.urlparse(page_url or image_url).hostname or "Image source",
            "width": data.get("w"),
            "height": data.get("h"),
        })
        if len(results) >= MAX_IMAGE_RESULTS:
            break

    return results


# ============================================================
# GOOGLE NEWS RSS
# ============================================================

def news_search(query):

    encoded = urllib.parse.quote(
        query
    )

    url = (
        "https://news.google.com/rss/search?"
        f"q={encoded}&hl=en-IN&gl=IN&ceid=IN:en"
    )

    text = request_text(
        url,
        cache_prefix="news"
    )

    if not text:
        return []

    try:

        root = ET.fromstring(
            text
        )

    except Exception:

        return []

    results = []

    for item in root.findall(
        ".//item"
    )[:20]:

        title = (
            item.findtext(
                "title"
            )
            or ""
        )

        link = (
            item.findtext(
                "link"
            )
            or ""
        )

        pub_date = (
            item.findtext(
                "pubDate"
            )
            or ""
        )

        source = item.find(
            "source"
        )

        source_name = (
            source.text
            if source is not None
            else ""
        )

        image_url = ""
        for image_tag in (
            item.find("{http://search.yahoo.com/mrss/}thumbnail"),
            item.find("{http://search.yahoo.com/mrss/}content"),
            item.find("enclosure"),
        ):
            if image_tag is not None:
                candidate = image_tag.attrib.get("url", "").strip()
                if candidate.startswith(("https://", "http://")):
                    image_url = candidate
                    break

        results.append(
            {
                "title": title,
                "url": link,
                "date": pub_date,
                "source": source_name,
                "image": image_url,
            }
        )

    return results




# ============================================================
# LIVE HOMEPAGE NEWS FEED
# ============================================================

NEWS_FEED_QUERIES = {
    "india": ["latest India news"],
    "politics": ["latest India politics news", "latest political news"],
    "world": ["latest world news"],
    "sports": ["latest sports news"],
    "technology": ["latest technology news"],
    "business": ["latest business news"],
    "science": ["latest science news"],
    "health": ["latest health news"],
    "education": ["latest education news India"],
    "entertainment": ["latest entertainment news"],
}

def _news_date_key(article):
    """Convert RSS date strings into sortable timestamps; unknown dates sort last."""
    value = str(article.get("date", "") or "").strip()
    if not value:
        return 0.0
    try:
        parsed = email.utils.parsedate_to_datetime(value)
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=__import__("datetime").timezone.utc)
        return parsed.timestamp()
    except Exception:
        return 0.0


@app.get("/api/news/latest")
def api_latest_news(
    category: str = Query(default="all"),
    limit: int = Query(default=24, ge=1, le=50),
):
    """
    Homepage news endpoint. Aggregates recent Google News RSS results across
    news categories, deduplicates links, and sorts by publication date.
    RSS fetches use Cerbyd's existing short-term cache.
    """
    selected = (category or "all").strip().lower()
    if selected not in ("all", *NEWS_FEED_QUERIES.keys()):
        return JSONResponse(
            status_code=400,
            content={
                "success": False,
                "error": "Unknown news category.",
                "articles": [],
            },
        )

    if selected == "all":
        requested = list(NEWS_FEED_QUERIES.items())
    else:
        requested = [(selected, NEWS_FEED_QUERIES[selected])]

    futures = []
    for label, queries in requested:
        for query in queries:
            futures.append((label, CERBYD_EXECUTOR.submit(news_search, query)))

    combined = []
    for label, future in futures:
        try:
            results = future.result(timeout=max(8, REQUEST_TIMEOUT * 3))
        except Exception as exc:
            print(f"[Cerbyd News] {label} feed warning: {type(exc).__name__}")
            continue

        for item in results if isinstance(results, list) else []:
            if not isinstance(item, dict):
                continue
            title = str(item.get("title", "")).strip()
            url = str(item.get("url", "")).strip()
            if not title or not url:
                continue
            parsed_url = urllib.parse.urlparse(url)
            if parsed_url.scheme not in ("http", "https") or not parsed_url.netloc:
                continue
            combined.append({
                "title": title[:500],
                "url": url,
                "date": str(item.get("date", "") or ""),
                "source": str(item.get("source", "") or label.title())[:120],
                "category": label,
                "image": str(item.get("image", "") or ""),
            })

    seen = set()
    unique = []
    for article in sorted(combined, key=_news_date_key, reverse=True):
        key = article["url"].split("#", 1)[0]
        if key in seen:
            continue
        seen.add(key)
        unique.append(article)
        if len(unique) >= limit:
            break

    return {
        "success": True,
        "category": selected,
        "count": len(unique),
        "articles": unique,
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "engine": APP_NAME,
        "version": APP_VERSION,
    }

# ============================================================
# SHOPPING SEARCH
# ============================================================

def shopping_search(query):

    url = (
        "https://www.bing.com/shop"
    )

    params = {
        "q": query
    }

    text = request_text(
        url,
        params=params,
        cache_prefix="shopping"
    )

    if not text:
        return []

    soup = BeautifulSoup(
        text,
        "html.parser"
    )

    results = []

    selectors = [
        "li.br-ibe",
        ".br-item",
        ".slide",
    ]

    elements = []

    for selector in selectors:

        elements = soup.select(
            selector
        )

        if elements:
            break

    for element in elements[:20]:

        title_element = (
            element.select_one(
                ".br-pdItemName"
            )
            or
            element.select_one(
                "h3"
            )
        )

        price_element = (
            element.select_one(
                ".br-price"
            )
            or
            element.select_one(
                ".price"
            )
        )

        link_element = (
            element.select_one(
                "a"
            )
        )

        if not title_element:
            continue

        results.append(
            {
                "title": title_element.get_text(
                    " ",
                    strip=True
                ),
                "price": (
                    price_element.get_text(
                        " ",
                        strip=True
                    )
                    if price_element
                    else ""
                ),
                "url": (
                    link_element.get(
                        "href",
                        ""
                    )
                    if link_element
                    else ""
                ),
            }
        )

    return results


# ============================================================
# DIRECTORY
# ============================================================

DIRECTORY = [
    {
        "name": "Google",
        "url": "https://www.google.com",
        "category": "Search",
        "description": "Web search and online services.",
    },
    {
        "name": "YouTube",
        "url": "https://www.youtube.com",
        "category": "Video",
        "description": "Online video platform.",
    },
    {
        "name": "Wikipedia",
        "url": "https://www.wikipedia.org",
        "category": "Knowledge",
        "description": "Free online encyclopedia.",
    },
    {
        "name": "GitHub",
        "url": "https://github.com",
        "category": "Technology",
        "description": "Software development platform.",
    },
    {
        "name": "Reddit",
        "url": "https://www.reddit.com",
        "category": "Community",
        "description": "Online community and discussion platform.",
    },
    {
        "name": "Microsoft",
        "url": "https://www.microsoft.com",
        "category": "Technology",
        "description": "Technology company and software services.",
    },
    {
        "name": "Apple",
        "url": "https://www.apple.com",
        "category": "Technology",
        "description": "Technology company and consumer products.",
    },
]


@app.get("/api/directory")
def directory(
    q: str = Query(
        default=""
    )
):

    query = q.strip().lower()

    if not query:

        return {
            "success": True,
            "results": DIRECTORY,
        }

    results = []

    for item in DIRECTORY:

        combined = " ".join(
            [
                item["name"],
                item["category"],
                item["description"],
            ]
        ).lower()

        if query in combined:

            results.append(
                item
            )

    return {
        "success": True,
        "results": results,
    }


# ============================================================
# SAFE CALCULATOR
# ============================================================

_ALLOWED_BINARY = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.Div: operator.truediv,
    ast.Mod: operator.mod,
    ast.Pow: operator.pow,
    ast.FloorDiv: operator.floordiv,
}

_ALLOWED_UNARY = {
    ast.UAdd: operator.pos,
    ast.USub: operator.neg,
}


_ALLOWED_FUNCTIONS = {
    "sqrt": math.sqrt,
    "sin": math.sin,
    "cos": math.cos,
    "tan": math.tan,
    "log": math.log,
    "log10": math.log10,
    "abs": abs,
    "round": round,
}


def safe_calculate(expression):

    expression = expression.strip()

    if len(expression) > 300:
        raise ValueError(
            "Expression too long."
        )

    expression = expression.replace(
        "^",
        "**"
    )

    tree = ast.parse(
        expression,
        mode="eval"
    )

    def evaluate(node):

        if isinstance(
            node,
            ast.Expression
        ):
            return evaluate(
                node.body
            )

        if isinstance(
            node,
            ast.Constant
        ):

            if isinstance(
                node.value,
                (int, float)
            ):

                if not math.isfinite(
                    float(node.value)
                ):
                    raise ValueError(
                        "Invalid number."
                    )

                return node.value

            raise ValueError(
                "Invalid constant."
            )

        if isinstance(
            node,
            ast.BinOp
        ):

            operator_function = (
                _ALLOWED_BINARY.get(
                    type(node.op)
                )
            )

            if not operator_function:
                raise ValueError(
                    "Operator not allowed."
                )

            left = evaluate(
                node.left
            )

            right = evaluate(
                node.right
            )

            if (
                isinstance(
                    node.op,
                    ast.Pow
                )
                and abs(right) > 100
            ):
                raise ValueError(
                    "Exponent too large."
                )

            value = operator_function(
                left,
                right
            )

            if not math.isfinite(
                float(value)
            ):
                raise ValueError(
                    "Result is not finite."
                )

            return value

        if isinstance(
            node,
            ast.UnaryOp
        ):

            function = (
                _ALLOWED_UNARY.get(
                    type(node.op)
                )
            )

            if not function:
                raise ValueError(
                    "Unary operator not allowed."
                )

            return function(
                evaluate(
                    node.operand
                )
            )

        if isinstance(
            node,
            ast.Name
        ):

            if node.id == "pi":
                return math.pi

            if node.id == "e":
                return math.e

            raise ValueError(
                "Unknown constant."
            )

        if isinstance(
            node,
            ast.Call
        ):

            if not isinstance(
                node.func,
                ast.Name
            ):
                raise ValueError(
                    "Function not allowed."
                )

            function = _ALLOWED_FUNCTIONS.get(
                node.func.id
            )

            if not function:
                raise ValueError(
                    "Function not allowed."
                )

            arguments = [
                evaluate(arg)
                for arg in node.args
            ]

            return function(
                *arguments
            )

        raise ValueError(
            "Expression not allowed."
        )

    return evaluate(
        tree
    )


# ============================================================
# CALCULATOR DETECTION
# ============================================================

def extract_calculation(query):

    q = query.strip()

    lowered = q.lower()

    prefixes = [
        "calculate ",
        "calc ",
        "what is ",
        "what's ",
        "solve ",
    ]

    expression = q

    for prefix in prefixes:

        if lowered.startswith(prefix):

            expression = q[
                len(prefix):
            ]

            break

    allowed = re.fullmatch(
        r"[0-9a-zA-Z_+\-*/().%^,\s]+",
        expression
    )

    if not allowed:
        return None

    if not any(
        char.isdigit()
        for char in expression
    ):
        return None

    math_symbols = (
        "+",
        "-",
        "*",
        "/",
        "%",
        "^",
    )

    if not any(
        symbol in expression
        for symbol in math_symbols
    ) and not re.search(r"\b(?:sqrt|sin|cos|tan|log|log10|abs|round)\s*\(", expression):
        return None

    try:

        result = safe_calculate(
            expression
        )

        return {
            "expression": expression,
            "result": result,
        }

    except Exception:

        return None


# ============================================================
# DICTIONARY
# ============================================================

def dictionary_lookup(word):

    word = word.strip().lower()

    if not re.fullmatch(
        r"[a-zA-Z-]+",
        word
    ):
        return None

    url = (
        "https://api.dictionaryapi.dev/"
        f"api/v2/entries/en/{urllib.parse.quote(word)}"
    )

    data = request_json(
        url,
        timeout=REQUEST_TIMEOUT,
        cache_prefix="dictionary"
    )

    if not data or not isinstance(
        data,
        list
    ):
        return None

    first = data[0]

    phonetic = ""

    for item in data:

        if item.get("phonetic"):
            phonetic = item[
                "phonetic"
            ]
            break

    meanings = []

    for meaning in first.get(
        "meanings",
        []
    ):

        part_of_speech = (
            meaning.get(
                "partOfSpeech",
                ""
            )
        )

        definitions = []

        for definition in meaning.get(
            "definitions",
            []
        )[:5]:

            definitions.append(
                {
                    "definition": definition.get(
                        "definition",
                        ""
                    ),
                    "example": definition.get(
                        "example",
                        ""
                    ),
                }
            )

        if definitions:

            meanings.append(
                {
                    "part_of_speech": (
                        part_of_speech
                    ),
                    "definitions": definitions,
                }
            )

    return {
        "word": first.get(
            "word",
            word
        ),
        "phonetic": phonetic,
        "meanings": meanings,
    }


# ============================================================
# TOPIC EXTRACTION
# ============================================================

def extract_topic(query):

    q = query.strip()

    patterns = [
        r"^who is (.+)$",
        r"^who was (.+)$",
        r"^what is (.+)$",
        r"^what was (.+)$",
        r"^what are (.+)$",
        r"^tell me about (.+)$",
        r"^explain (.+)$",
        r"^where is (.+)$",
    ]

    for pattern in patterns:

        match = re.match(
            pattern,
            q,
            re.IGNORECASE
        )

        if match:

            topic = match.group(
                1
            ).strip()

            if topic:
                return topic

    return None


# ============================================================
# WIKIPEDIA SEARCH
# ============================================================

def wikipedia_search(query):

    url = (
        "https://en.wikipedia.org/w/api.php"
    )

    params = {
        "action": "query",
        "list": "search",
        "srsearch": query,
        "format": "json",
        "utf8": 1,
        "srlimit": 5,
    }

    data = request_json(
        url,
        params=params,
        cache_prefix="wikipedia-search"
    )

    if not data:
        return []

    results = []

    for item in data.get(
        "query",
        {}
    ).get(
        "search",
        []
    ):

        title = item.get(
            "title",
            ""
        )

        snippet = BeautifulSoup(
            item.get(
                "snippet",
                ""
            ),
            "html.parser"
        ).get_text(
            " ",
            strip=True
        )

        page_url = (
            "https://en.wikipedia.org/wiki/"
            + urllib.parse.quote(
                title.replace(
                    " ",
                    "_"
                )
            )
        )

        results.append(
            {
                "title": title,
                "snippet": snippet,
                "url": page_url,
            }
        )

    return results


# ============================================================
# WIKIPEDIA SUMMARY
# ============================================================

def wikipedia_summary(topic):

    encoded = urllib.parse.quote(
        topic.replace(
            " ",
            "_"
        ),
        safe=""
    )

    url = (
        "https://en.wikipedia.org/api/rest_v1/"
        f"page/summary/{encoded}"
    )

    data = request_json(
        url,
        cache_prefix="wikipedia-summary"
    )

    if not data:
        return None

    extract = data.get(
        "extract"
    )

    if not extract:
        return None

    return {
        "title": data.get(
            "title",
            topic
        ),
        "extract": extract,
        "url": (
            data.get(
                "content_urls",
                {}
            )
            .get(
                "desktop",
                {}
            )
            .get(
                "page",
                ""
            )
        ),
        "thumbnail": (
            data.get(
                "thumbnail",
                {}
            )
            .get(
                "source",
                ""
            )
        ),
    }


# ============================================================
# DUCKDUCKGO INSTANT ANSWER
# ============================================================

def duckduckgo_answer(query):

    url = (
        "https://api.duckduckgo.com/"
    )

    params = {
        "q": query,
        "format": "json",
        "no_html": 1,
        "skip_disambig": 1,
    }

    data = request_json(
        url,
        params=params,
        cache_prefix="ddg-answer"
    )

    if not data:
        return None

    abstract = data.get(
        "AbstractText"
    )

    if abstract:

        return {
            "title": data.get(
                "Heading",
                query
            ),
            "answer": abstract,
            "url": data.get(
                "AbstractURL",
                ""
            ),
            "source": "DuckDuckGo",
        }

    related = data.get(
        "RelatedTopics",
        []
    )

    for item in related:

        if not isinstance(
            item,
            dict
        ):
            continue

        text = item.get(
            "Text"
        )

        first_url = item.get(
            "FirstURL",
            ""
        )

        if text:

            return {
                "title": query,
                "answer": text,
                "url": first_url,
                "source": "DuckDuckGo",
            }

    return None


# ============================================================
# COMMON FACTS
# ============================================================

COMMON_FACTS = {

    "internet": (
        "The Internet is a global network of interconnected "
        "computer networks that communicate using standard "
        "Internet protocols."
    ),

    "computer": (
        "A computer is an electronic machine that processes "
        "data according to instructions called programs."
    ),

    "python": (
        "Python is a general-purpose programming language "
        "known for its readable syntax and large ecosystem."
    ),

    "html": (
        "HTML, or HyperText Markup Language, is the standard "
        "markup language used to structure webpages."
    ),

    "css": (
        "CSS, or Cascading Style Sheets, controls the visual "
        "presentation and layout of webpages."
    ),

    "javascript": (
        "JavaScript is a programming language commonly used "
        "to add behavior and interactivity to webpages."
    ),
}


# ============================================================
# PARALLEL ANSWER SOURCES
# ============================================================

def parallel_answer_sources(query, topic=None):
    """Fetch answer sources concurrently and prefer a substantive answer."""
    futures = {}
    if topic:
        futures[CERBYD_EXECUTOR.submit(wikipedia_summary, topic)] = "wikipedia"
    futures[CERBYD_EXECUTOR.submit(duckduckgo_answer, query)] = "duckduckgo"

    results = {}
    for future in as_completed(futures):
        source = futures[future]
        try:
            results[source] = future.result()
        except Exception:
            results[source] = None

    ddg = results.get("duckduckgo")
    wiki = results.get("wikipedia")
    # Prefer a direct instant answer when it actually contains useful text;
    # use Wikipedia as a reliable fallback for topic-oriented questions.
    if ddg and len(str(ddg.get("answer", "")).strip()) >= 40:
        return {"type": "instant_answer", "data": ddg}
    if wiki and len(str(wiki.get("extract", "")).strip()) >= 40:
        return {"type": "wikipedia", "data": wiki}
    if ddg and ddg.get("answer"):
        return {"type": "instant_answer", "data": ddg}
    if wiki:
        return {"type": "wikipedia", "data": wiki}
    return None


# ============================================================
# CERBYD ANSWER QUALITY + SAFETY HELPERS
# ============================================================

_SELF_HARM_PATTERNS = [
    r"\b(kill|hurt|harm|end)\s+(myself|my life)\b",
    r"\b(suicid(?:e|al|ally))\b",
    r"\bwant(?:ing)?\s+to\s+die\b",
    r"\b(can't|cannot|dont|don't)\s+go\s+on\b",
    r"\bself[ -]?harm\b",
    r"\bways?\s+to\s+(?:die|end\s+my\s+life)\b",
]


def detect_self_harm_risk(query: str) -> bool:
    """Conservative keyword screening; this is a safety net, not a diagnosis."""
    text = re.sub(r"\s+", " ", (query or "").lower()).strip()
    return any(re.search(pattern, text, re.IGNORECASE) for pattern in _SELF_HARM_PATTERNS)


def safety_answer():
    """Supportive response shown before any ordinary search or answer call."""
    return {
        "type": "safety",
        "title": "You matter. Support is available.",
        "answer": (
            "I'm sorry things may feel difficult right now. You deserve support, "
            "and you do not have to handle this alone. If this is about you, please "
            "tell a trusted adult or someone you trust and stay with them if you can. "
            "If you are in immediate danger, call your local emergency number. "
            "If you are in India, Tele-MANAS offers mental-health support at 14416; "
            "112 is the emergency number. If you are elsewhere, use your local "
            "crisis service or findahelpline.com to find support in your country. "
            "Cerbyd cannot provide emergency care, but it can help you find support."
        ),
        "resources": [
            {"label": "India: Tele-MANAS mental-health support — 14416", "url": "tel:14416"},
            {"label": "India: Emergency services — 112", "url": "tel:112"},
            {"label": "Find a helpline in your country", "url": "https://findahelpline.com/"},
        ],
        "source": "Cerbyd safety support",
    }


def _normalise_math_text(text: str) -> str:
    """Normalize common natural-language arithmetic without evaluating arbitrary code."""
    value = text.strip().lower()
    value = re.sub(r"^(?:please\s+)?(?:calculate|compute|work out|what is|what's|solve)\s+", "", value)
    value = value.replace("×", "*").replace("÷", "/").replace("−", "-")
    value = re.sub(r"\bdivided by\b", "/", value)
    value = re.sub(r"\btimes\b|\bmultiplied by\b", "*", value)
    value = re.sub(r"\bplus\b", "+", value)
    value = re.sub(r"\bminus\b", "-", value)
    value = re.sub(r"\b(square root of)\s*(\d+(?:\.\d+)?)", r"sqrt(\2)", value)
    value = re.sub(r"\b(\d+(?:\.\d+)?)\s*percent\s+of\s+(\d+(?:\.\d+)?)", r"(\1/100)*\2", value)
    value = re.sub(r"\b(\d+(?:\.\d+)?)\s*%\s+of\s+(\d+(?:\.\d+)?)", r"(\1/100)*\2", value)
    return value.strip(" ?")


def _linear_form(node):
    """Return (coefficient of x, constant) for a safe linear-expression AST."""
    if isinstance(node, ast.Expression):
        return _linear_form(node.body)
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
        return (0.0, float(node.value))
    if isinstance(node, ast.Name) and node.id == "x":
        return (1.0, 0.0)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        a, b = _linear_form(node.operand)
        sign = -1.0 if isinstance(node.op, ast.USub) else 1.0
        return (sign * a, sign * b)
    if isinstance(node, ast.BinOp):
        a1, b1 = _linear_form(node.left)
        a2, b2 = _linear_form(node.right)
        if isinstance(node.op, ast.Add): return (a1 + a2, b1 + b2)
        if isinstance(node.op, ast.Sub): return (a1 - a2, b1 - b2)
        if isinstance(node.op, ast.Mult):
            if a1 and a2: raise ValueError("Only linear equations are supported.")
            return (a1 * b2 + a2 * b1, b1 * b2)
        if isinstance(node.op, ast.Div):
            if a2 or b2 == 0: raise ValueError("Division must be by a non-zero constant.")
            return (a1 / b2, b1 / b2)
    raise ValueError("Unsupported equation form.")


def solve_linear_equation(query: str):
    """Solve basic one-variable linear equations such as 2x + 3 = 11."""
    q = query.strip().lower()
    q = re.sub(r"^(?:please\s+)?(?:solve|find)\s+(?:for\s+)?x\s*:?\s*", "", q)
    q = re.sub(r"^(?:solve|find)\s+", "", q)
    if "=" not in q or len(q) > 160:
        return None
    q = q.replace("×", "*").replace("−", "-").replace("÷", "/").replace("^", "**")
    # Accept implicit multiplication: 2x, 3(x+1), and x(2).
    q = re.sub(r"(?<=\d)\s*x\b", "*x", q)
    q = re.sub(r"\bx\s*(?=\d|\()", "x*", q)
    q = re.sub(r"(?<=\d)\s*\(", "*(", q)
    q = re.sub(r"\)\s*(?=\d|x|\()", ")*", q)
    if not re.fullmatch(r"[0-9xX+*/().\s=\-]+", q):
        return None
    left, right = (part.strip() for part in q.split("=", 1))
    try:
        l_a, l_b = _linear_form(ast.parse(left, mode="eval"))
        r_a, r_b = _linear_form(ast.parse(right, mode="eval"))
        coefficient = l_a - r_a
        constant = r_b - l_b
        if abs(coefficient) < 1e-12:
            return {"kind": "equation", "answer": "All real numbers satisfy this equation." if abs(constant) < 1e-12 else "This equation has no solution.", "steps": ["Simplify both sides.", "The x terms cancel, so the equation is checked by comparing the constants."]}
        value = constant / coefficient
        if not math.isfinite(value):
            return None
        shown = int(value) if value.is_integer() else round(value, 10)
        steps = [f"Start with {query.strip()}.", f"Collect the x terms and constants: {coefficient:g}x = {constant:g}.", f"Divide both sides by {coefficient:g}: x = {shown}."]
        return {"kind": "equation", "answer": f"x = {shown}", "steps": steps}
    except Exception:
        return None



# ============================================================
# QUERY UNDERSTANDING + OPTIONAL GENERATIVE ANSWERS
# ============================================================

# Conservative fixes for frequent typing mistakes. This deliberately avoids
# rewriting unknown names, URLs, code, and most technical terms.
_COMMON_TYPO_FIXES = {
    "teh": "the", "thier": "their", "becuase": "because",
    "whta": "what", "waht": "what", "whats": "what's",
    "explaination": "explanation", "explian": "explain",
    "defintion": "definition", "langauge": "language",
    "programing": "programming", "progrmming": "programming",
    "websit": "website", "webiste": "website", "webiste": "website",
    "mak": "make", "creat": "create", "howto": "how to",
    "pyhton": "python", "javascrpt": "javascript",
    "internt": "internet", "computr": "computer",
    "infromation": "information", "infomation": "information",
    "recieve": "receive", "seperate": "separate",
    "definately": "definitely", "enviroment": "environment",
    "reccomend": "recommend", "whcih": "which", "wher": "where",
    "plese": "please", "plz": "please", "becaus": "because",
}

def normalize_user_query(query: str) -> str:
    """Normalize casing/spacing and correct only high-confidence common typos."""
    value = re.sub(r"\s+", " ", str(query or "")).strip()
    if not value:
        return ""
    # Do not touch URLs, code-like strings, or queries with file paths.
    if re.search(r"(https?://|www\.|[\\/]|\b(def|class|function|const|let|import)\b)", value, re.I):
        return value
    words = re.findall(r"\b[\w']+\b|[^\w\s]", value, flags=re.UNICODE)
    fixed = []
    for token in words:
        key = token.lower()
        replacement = _COMMON_TYPO_FIXES.get(key)
        # Only fuzzy-match a small, curated vocabulary of question words and
        # common Cerbyd topics. Unknown/proper words are intentionally preserved.
        if not replacement and key.isalpha() and len(key) >= 5 and token.islower():
            vocabulary = (
                "explain explanation define definition meaning describe "
                "website computer internet programming javascript python "
                "language information create build make learn understand "
                "difference between examples example history science "
                "technology artificial intelligence calculate translate"
            ).split()
            match = difflib.get_close_matches(key, vocabulary, n=1, cutoff=0.90)
            if match and key not in vocabulary:
                replacement = match[0]
        if replacement:
            # Keep all-caps formatting if it was used for emphasis.
            if token.isupper():
                replacement = replacement.upper()
            fixed.append(replacement)
        else:
            fixed.append(token)
    # Rejoin punctuation without adding spaces before punctuation.
    result = ""
    for token in fixed:
        if token in ".,?!:;)]}":
            result = result.rstrip() + token
        elif token in "([{":
            result += token
        else:
            result += (" " if result and not result.endswith((" ", "(", "[", "{")) else "") + token
    return re.sub(r"\s+", " ", result).strip()


def local_model_answer(query: str):
    """Generate a detailed answer using an optional Ollama-compatible endpoint."""
    if not CERBYD_AI_URL:
        return None
    prompt = (
        "You are Cerbyd, a careful and helpful general-purpose assistant. "
        "Answer the user's actual question directly. Normally provide a substantial, "
        "well-organized answer of 2-5 paragraphs with explanations and examples when useful. "
        "Use headings or numbered steps only when they improve readability. "
        "Do not pad the answer, invent facts, pretend to have searched the web, or make up sources. "
        "If the question is ambiguous, briefly state the most likely interpretation or ask one "
        "clear clarification. Respect capitalization differences and tolerate ordinary spelling mistakes. "
        "For code requests, provide correct complete code when feasible and explain where it goes. "
        "User question: " + query
    )
    try:
        response = get_http_session().post(
            CERBYD_AI_URL,
            json={
                "model": CERBYD_AI_MODEL,
                "prompt": prompt,
                "stream": False,
                "options": {"temperature": 0.25, "num_predict": 700},
            },
            timeout=(CONNECT_TIMEOUT, CERBYD_AI_TIMEOUT),
        )
        if not response.ok:
            return None
        payload = response.json()
        answer = str(payload.get("response", "")).strip()
        if len(answer) < 20:
            return None
        return {
            "type": "ai_answer",
            "title": "Cerbyd Answer",
            "answer": answer,
            "source": f"Cerbyd AI · {CERBYD_AI_MODEL}",
            "model": CERBYD_AI_MODEL,
        }
    except Exception as exc:
        print(f"[Cerbyd AI] Local model unavailable; using sourced fallback: {exc}")
        return None


# ============================================================
# SMART ANSWER ENGINE
# ============================================================

_SIMPLE_FACTS = [
    (r"\b(?:what\s+)?colou?r(?:s)?\s+(?:is|are)\s+(?:an?\s+)?apple\b|\bwhat\s+colou?r\s+(?:is|are)\s+apples?\b|\bcolou?r\s+of\s+(?:an?\s+)?apple\b",
     "Apples can be red, green, or yellow. The colour depends on the variety; some apples have more than one colour."),
    (r"\b(?:what\s+)?(?:is|are)\s+the\s+colou?r(?:s)?\s+of\s+(?:the\s+)?sky\b|\bwhy\s+is\s+the\s+sky\s+blue\b",
     "The daytime sky often looks blue because air molecules scatter shorter blue wavelengths of sunlight more than longer red wavelengths. Its colour can look different at sunrise, sunset, or under different weather conditions."),
    (r"\b(?:what\s+is\s+)?the\s+capital\s+of\s+india\b|\bcapital\s+city\s+of\s+india\b",
     "New Delhi is the capital of India."),
    (r"\b(?:what\s+is\s+)?the\s+capital\s+of\s+france\b|\bcapital\s+city\s+of\s+france\b",
     "Paris is the capital of France."),
    (r"\b(?:what\s+is\s+)?the\s+capital\s+of\s+japan\b|\bcapital\s+city\s+of\s+japan\b",
     "Tokyo is the capital of Japan."),
    (r"\bhow\s+many\s+planets\s+(?:(?:are\s+)?(?:there\s+)?in\s+)?(?:our\s+)?solar\s+system\b|\bnumber\s+of\s+planets\s+in\s+the\s+solar\s+system\b",
     "There are eight recognised planets in our Solar System: Mercury, Venus, Earth, Mars, Jupiter, Saturn, Uranus, and Neptune."),
    (r"\bwhat\s+is\s+(?:the\s+)?speed\s+of\s+light\b|\bspeed\s+of\s+light\s+in\s+vacuum\b",
     "The speed of light in a vacuum is exactly 299,792,458 metres per second, or about 300,000 kilometres per second."),
    (r"\bwho\s+wrote\s+(?:the\s+)?romeo\s+and\s+juliet\b|\bauthor\s+of\s+(?:the\s+)?romeo\s+and\s+juliet\b",
     "William Shakespeare wrote Romeo and Juliet."),
]


def simple_fact_answer(query: str):
    """Answer a small set of stable, common questions without unreliable search snippets."""
    normalized = re.sub(r"[\s?!.,;:]+", " ", str(query or "").casefold()).strip()
    for pattern, answer in _SIMPLE_FACTS:
        if re.search(pattern, normalized, re.IGNORECASE):
            return {
                "type": "fact",
                "title": "Quick answer",
                "answer": answer,
                "source": "Cerbyd Knowledge Base",
            }
    return None


def _query_terms(text: str):
    """Return meaningful words for comparing a search result with its query."""
    stop_words = {
        "what", "when", "where", "who", "whom", "why", "how", "is", "are", "was", "were",
        "the", "a", "an", "of", "to", "for", "in", "on", "at", "and", "or", "with",
        "does", "do", "did", "can", "could", "would", "should", "please", "tell", "me",
        "about", "explain", "give", "show", "find", "search", "web", "result", "results",
    }
    return {word for word in re.findall(r"[a-z0-9]+", str(text or "").casefold()) if len(word) > 2 and word not in stop_words}


def _search_result_relevance(query: str, item: dict) -> float:
    """Score whether a search result actually discusses the user's subject."""
    terms = _query_terms(query)
    if not terms:
        return 0.0
    title_terms = _query_terms(item.get("title", ""))
    snippet_terms = _query_terms(item.get("snippet", ""))
    combined = title_terms | snippet_terms
    matched = terms & combined
    # Subject terms in the title are stronger evidence than incidental snippet words.
    title_matches = terms & title_terms
    return (len(matched) / len(terms)) + (0.35 * len(title_matches) / len(terms))


def smart_answer(query):

    original_query = str(query or "").strip()
    query = normalize_user_query(original_query)

    if not query:
        return None

    # Safety checks run before calculator, web search, or any model call.
    if detect_self_harm_risk(query) or detect_self_harm_risk(original_query):
        return safety_answer()

    # Linear equations receive a deterministic, step-by-step solution.
    equation = solve_linear_equation(query)
    if equation:
        return {
            "type": "math_solution",
            "title": "Step-by-step math answer",
            "answer": equation["answer"],
            "steps": equation["steps"],
            "source": "Cerbyd Math Engine",
        }

    # --------------------------------------------------------
    # Calculator
    # --------------------------------------------------------

    math_query = _normalise_math_text(query)
    calculation = extract_calculation(math_query)

    if calculation:

        return {
            "type": "calculator",
            "title": "Calculator",
            "answer": str(
                calculation["result"]
            ),
            "data": calculation,
            "steps": [
                f"Expression: {calculation['expression']}",
                f"Evaluate using the standard order of operations.",
                f"Result: {calculation['result']}",
            ],
            "source": "Cerbyd Math Engine",
        }

    # --------------------------------------------------------
    # Dictionary
    # --------------------------------------------------------

    dictionary_match = re.match(
        r"^(?:define|definition of|meaning of)\s+(.+)$",
        query,
        re.IGNORECASE
    )

    if dictionary_match:

        word = (
            dictionary_match.group(
                1
            ).strip()
        )

        dictionary = dictionary_lookup(
            word
        )

        if dictionary:

            return {
                "type": "dictionary",
                "title": dictionary.get(
                    "word",
                    word
                ),
                "answer": (
                    dictionary["meanings"][0]
                    ["definitions"][0]
                    ["definition"]
                    if dictionary.get(
                        "meanings"
                    )
                    and dictionary["meanings"][0].get(
                        "definitions"
                    )
                    else ""
                ),
                "data": dictionary,
            }

    # --------------------------------------------------------
    # Common direct answers (avoid noisy search results for simple questions)
    # --------------------------------------------------------

    direct_fact = simple_fact_answer(query)
    if direct_fact:
        return direct_fact

    # --------------------------------------------------------
    # Common facts
    # --------------------------------------------------------

    lower_query = query.lower().strip(" ?.!\t\n")

    for keyword, answer in COMMON_FACTS.items():
        topic_question = re.fullmatch(
            rf"(?:what\s+is\s+|what\s+are\s+|define\s+|explain\s+)?{re.escape(keyword)}",
            lower_query,
            re.IGNORECASE,
        )
        if topic_question:
            return {
                "type": "fact",
                "title": keyword.title(),
                "answer": answer,
                "source": "Cerbyd Knowledge Base",
            }

    # --------------------------------------------------------
    # Optional generative answer (configured local model)
    # --------------------------------------------------------

    generated = local_model_answer(query)
    if generated:
        generated["corrected_query"] = query if query != original_query else None
        return generated

    # --------------------------------------------------------
    # Topic / question
    # --------------------------------------------------------

    topic = extract_topic(
        query
    )

    answer_result = parallel_answer_sources(
        query,
        topic
    )

    if answer_result:

        if answer_result["type"] == "wikipedia":

            data = answer_result[
                "data"
            ]

            return {
                "type": "wikipedia",
                "title": data.get(
                    "title",
                    topic or query
                ),
                "answer": data.get(
                    "extract",
                    ""
                ),
                "url": data.get(
                    "url",
                    ""
                ),
                "image": data.get(
                    "thumbnail",
                    ""
                ),
                "source": "Wikipedia",
            }

        return {
            "type": "instant_answer",
            "title": answer_result[
                "data"
            ].get(
                "title",
                query
            ),
            "answer": answer_result[
                "data"
            ].get(
                "answer",
                ""
            ),
            "url": answer_result[
                "data"
            ].get(
                "url",
                ""
            ),
            "source": "DuckDuckGo",
        }

    # Last-resort answer: use real web results instead of returning nothing.
    # This is a sourced summary of snippets, not a claim that Cerbyd has an AI model.
    try:
        results = web_search(query)[:5]
    except Exception:
        results = []

    useful = [
        item for item in results
        if item.get("snippet") and _search_result_relevance(query, item) >= 0.65
    ]
    if useful:
        # Combine multiple distinct snippets into readable, substantial context
        # instead of returning one short fragment as if it were a complete answer.
        seen_snippets = set()
        paragraphs = []
        for item in useful[:5]:
            snippet = re.sub(r"\s+", " ", str(item.get("snippet", "")).strip())
            key = snippet.casefold()
            if snippet and key not in seen_snippets:
                seen_snippets.add(key)
                title = str(item.get("title", "")).strip()
                paragraphs.append(f"{title}: {snippet}" if title else snippet)
        answer_text = "\n\n".join(paragraphs)
        return {
            "type": "web_summary",
            "title": f"Web results for {query}",
            "answer": answer_text,
            "url": useful[0].get("url", ""),
            "source": "Web search results",
            "sources": [
                {"title": item.get("title", ""), "url": item.get("url", "")}
                for item in useful[:5]
            ],
        }

    return None


# ============================================================
# SEARCH API
# ============================================================

@app.get("/api/search")
def api_search(
    q: str = Query(
        default=""
    ),
    type: str = Query(
        default="web"
    ),
):

    start_time = time.perf_counter()

    query = q.strip()

    if len(query) > MAX_QUERY_LENGTH:
        return JSONResponse(
            status_code=413,
            content={
                "success": False,
                "error": f"Search query is too long. Maximum is {MAX_QUERY_LENGTH} characters.",
                "results": [],
            }
        )

    if not query:

        return {
            "success": False,
            "error": "Search query is empty.",
            "results": [],
            "performance": {
                "milliseconds": 0
            },
        }

    search_type = (
        type.lower().strip()
    )

    if search_type == "web":

        results = web_search(
            query
        )

    elif search_type in (
        "images",
        "image"
    ):

        results = image_search(
            query
        )

    elif search_type == "news":

        results = news_search(
            query
        )

    elif search_type in (
        "shopping",
        "shop"
    ):

        results = shopping_search(
            query
        )

    else:

        results = web_search(
            query
        )

    # For normal web searches, include an answer in the same response as
    # the links. This lets the frontend render answers from /api/search
    # without depending entirely on a separate /api/answer request.
    answer_payload = None
    if search_type == "web":
        try:
            answer_payload = smart_answer(query)
        except Exception as exc:
            # Answer generation must never break ordinary web search.
            print(f"Cerbyd answer generation warning: {type(exc).__name__}: {exc}")

        # If the answer engine has no result, build a clearly sourced summary
        # from the search results already fetched by this request.
        if not answer_payload:
            relevant_results = [
                item for item in results
                if isinstance(item, dict)
                and str(item.get("snippet", "")).strip()
                and _search_result_relevance(query, item) >= 0.65
            ][:3]
            if relevant_results:
                answer_payload = {
                    "type": "web_summary",
                    "title": f"Web summary for {query}",
                    "answer": "\n\n".join(
                        (
                            f"{str(item.get('title', '')).strip()}: "
                            f"{' '.join(str(item.get('snippet', '')).split())}"
                        ).strip(": ")
                        for item in relevant_results
                    ),
                    "source": "Web search snippets",
                    "sources": [
                        {
                            "title": str(item.get("title", "")).strip(),
                            "url": str(item.get("url", "")).strip(),
                        }
                        for item in relevant_results
                    ],
                }

    elapsed_ms = (
        time.perf_counter()
        - start_time
    ) * 1000

    # Persist search history locally. Database failures never
    # prevent the search result from being returned.
    save_search_history(
        query,
        search_type,
        len(results),
        elapsed_ms
    )

    response_payload = {
        "success": True,
        "query": query,
        "type": search_type,
        "results": results,
        "count": len(results),
        "performance": {
            "milliseconds": round(
                elapsed_ms,
                2
            )
        },
        "engine": APP_NAME,
        "version": APP_VERSION,
        "database": True,
    }
    if search_type == "web":
        # Use one consistent title in the API response; the frontend also
        # normalizes the visible card title as a second line of defence.
        if isinstance(answer_payload, dict) and answer_payload.get("type") not in ("safety", "calculator", "math_solution"):
            answer_payload["title"] = "Cerbyd Answer"
        answer_text = (
            str(answer_payload.get("answer", "")).strip()
            if isinstance(answer_payload, dict)
            else ""
        )
        response_payload["answer"] = answer_text or None
        response_payload["answer_data"] = answer_payload
        response_payload["answer_found"] = bool(answer_text)

    return response_payload


# ============================================================
# FAST SAFETY CHECK API
# ============================================================

@app.get("/api/safety-check")
def api_safety_check(q: str = Query(default="")):
    query = q.strip()
    if len(query) > MAX_QUERY_LENGTH:
        return JSONResponse(status_code=413, content={"success": False, "flagged": False, "error": "Question is too long."})
    flagged = bool(query and detect_self_harm_risk(query))
    return {"success": True, "flagged": flagged, "answer": safety_answer() if flagged else None}


# ============================================================
# SMART ANSWER API
# ============================================================

@app.get("/api/answer")
def api_answer(
    q: str = Query(
        default=""
    )
):

    start_time = time.perf_counter()

    query = q.strip()

    if len(query) > MAX_QUERY_LENGTH:
        return JSONResponse(
            status_code=413,
            content={
                "success": False,
                "error": f"Question is too long. Maximum is {MAX_QUERY_LENGTH} characters.",
            }
        )

    if not query:

        return {
            "success": False,
            "error": "Question is empty.",
        }

    answer = smart_answer(
        query
    )

    elapsed_ms = (
        time.perf_counter()
        - start_time
    ) * 1000

    if not answer:

        return {
            "success": True,
            "found": False,
            "query": query,
            "answer": None,
            "performance": {
                "milliseconds": round(
                    elapsed_ms,
                    2
                )
            },
        }

    answer["success"] = True
    answer["found"] = True
    answer["query"] = query
    normalized_query = normalize_user_query(query)
    if normalized_query != query:
        answer["corrected_query"] = normalized_query
    answer["performance"] = {
        "milliseconds": round(
            elapsed_ms,
            2
        )
    }

    return answer


# ============================================================
# STATUS API
# ============================================================

@app.get("/api/status")
def api_status():

    with _cache_lock:
        cache_items = len(
            _cache
        )

    return {
        "success": True,
        "name": APP_NAME,
        "company": APP_COMPANY,
        "version": APP_VERSION,
        "build": 25,
        "codename": APP_CODENAME,

        "engine": {
            "name": "Cerbyd Speed Engine",
            "workers": CERBYD_WORKERS,
            "session_reuse": True,
            "cache": True,
            "cache_ttl_seconds": CACHE_TTL,
            "cache_items": cache_items,
            "pooled_http_connections": True,
            "parallel_web_providers": True,
            "max_web_results": MAX_WEB_RESULTS,
            "max_image_results": MAX_IMAGE_RESULTS,
        },

        "database": {
            "engine": "SQLite",
            "enabled": True,
            "file": DATABASE_FILE.name,
            "searches": database_count("searches"),
            "favorites": database_count("favorites"),
            "network_tests": database_count("network_tests"),
            "settings": database_count("settings"),
            "users": database_count("users"),
        },

        "public_release": {
            "rate_limit_enabled": True,
            "rate_limit_window_seconds": RATE_LIMIT_WINDOW,
            "search_requests_per_window": RATE_LIMIT_SEARCH,
            "network_tests_per_window": RATE_LIMIT_NETWORK,
            "max_query_length": MAX_QUERY_LENGTH,
        },

        "features": {
            "web_search": True,
            "smart_answers": True,
            "wikipedia": True,
            "dictionary": True,
            "calculator": True,
            "images": True,
            "news": True,
            "shopping": True,
            "directory": True,
            "network_test": True,
            "network_ping": True,
            "database": True,
            "search_history": True,
            "favorites": True,
            "network_history": True,
            "email_password_auth": True,
            "persistent_auth_sessions": True,
            "google_oauth": bool(os.getenv("GOOGLE_CLIENT_ID") and os.getenv("GOOGLE_CLIENT_SECRET")),
            "microsoft_oauth": bool(os.getenv("MICROSOFT_CLIENT_ID") and os.getenv("MICROSOFT_CLIENT_SECRET")),
            "apple_oauth": bool(os.getenv("APPLE_CLIENT_ID") and os.getenv("APPLE_TEAM_ID") and os.getenv("APPLE_KEY_ID") and os.getenv("APPLE_PRIVATE_KEY")),
            "rate_limiting": True,
            "security_headers": True,
            "compression": True,
        },
    }


# ============================================================
# HEALTH API
# ============================================================

@app.get("/health")
def health():

    with _cache_lock:
        cache_items = len(
            _cache
        )

    return {
        "status": "ok",
        "service": APP_NAME,
        "company": APP_COMPANY,
        "version": APP_VERSION,
        "codename": APP_CODENAME,

        "speed_engine": True,
        "ai": {
            "configured": bool(CERBYD_AI_URL),
            "model": CERBYD_AI_MODEL if CERBYD_AI_URL else None,
            "mode": "configured-model-with-knowledge-fallback" if CERBYD_AI_URL else "knowledge-and-web-fallback",
        },
        "session_reuse": True,
        "cache": True,
        "cache_items": cache_items,
        "workers": CERBYD_WORKERS,
        "public_rate_limit": True,
        "rate_limit_window_seconds": RATE_LIMIT_WINDOW,

        "database": {
            "enabled": True,
            "engine": "SQLite",
            "file": DATABASE_FILE.name,
            "searches": database_count("searches"),
            "favorites": database_count("favorites"),
            "network_tests": database_count("network_tests"),
        },

        "timestamp": time.time(),
    }


# ============================================================
# FRONTEND
# ============================================================

@app.get("/")
def homepage():

    if INDEX_FILE.exists():

        return FileResponse(
            INDEX_FILE
        )

    return JSONResponse(
        {
            "name": APP_NAME,
            "company": APP_COMPANY,
            "version": APP_VERSION,
            "build": 25,
            "message": (
                "Cerbyd Web backend is running. "
                "Place index.html beside main.py "
                "to serve the Cerbyd Web frontend."
            ),
        }
    )


# ============================================================
# MWY TOOL API (MAPS + TRANSLATOR)
# Calculator, calendar, and photo previews run locally in the browser.
# ============================================================

@app.get("/api/mwy/geocode")
def mwy_geocode(q: str = Query(..., min_length=2, max_length=200)):
    """Search for a place through OpenStreetMap Nominatim."""
    query = " ".join(q.split())
    results = request_json(
        "https://nominatim.openstreetmap.org/search",
        params={"format": "jsonv2", "limit": 1, "q": query},
        timeout=min(REQUEST_TIMEOUT, 6),
        cache_prefix="mwy_geocode",
    )
    if not isinstance(results, list):
        return JSONResponse(
            {"success": False, "error": "Map search is temporarily unavailable."},
            status_code=502,
        )
    return results


@app.get("/api/mwy/nearby")
def mwy_nearby(
    lat: float = Query(..., ge=-90, le=90),
    lon: float = Query(..., ge=-180, le=180),
    category: str = Query(default="cafe", min_length=2, max_length=40),
):
    """Find nearby places around browser-approved coordinates using Nominatim."""
    categories = {
        "cafe": "cafe",
        "restaurant": "restaurant",
        "hospital": "hospital",
        "pharmacy": "pharmacy",
        "park": "park",
        "library": "library",
        "supermarket": "supermarket",
        "school": "school",
    }
    selected = category.strip().lower()
    if selected not in categories:
        return JSONResponse(
            {"success": False, "error": "Choose a supported nearby category.", "results": []},
            status_code=400,
        )
    pad = 0.08
    results = request_json(
        "https://nominatim.openstreetmap.org/search",
        params={
            "format": "jsonv2",
            "limit": 8,
            "q": categories[selected],
            "viewbox": f"{lon-pad},{lat+pad},{lon+pad},{lat-pad}",
            "bounded": 1,
        },
        timeout=min(REQUEST_TIMEOUT, 6),
        cache_prefix="mwy_nearby",
    )
    if not isinstance(results, list):
        return JSONResponse(
            {"success": False, "error": "Nearby search is temporarily unavailable.", "results": []},
            status_code=502,
        )
    return {"success": True, "category": selected, "results": results}


# Language metadata is fetched from LibreTranslate when available, with a broad
# fallback list so the translator's language menu can still populate offline.
_TRANSLATOR_LANGUAGE_CACHE = {"time": 0.0, "items": []}
_TRANSLATOR_LANGUAGE_TTL = 3600
_TRANSLATOR_LANGUAGE_FALLBACK = [
    {"code": "af", "name": "Afrikaans"}, {"code": "sq", "name": "Albanian"},
    {"code": "am", "name": "Amharic"}, {"code": "ar", "name": "Arabic"},
    {"code": "hy", "name": "Armenian"}, {"code": "az", "name": "Azerbaijani"},
    {"code": "eu", "name": "Basque"}, {"code": "be", "name": "Belarusian"},
    {"code": "bn", "name": "Bengali"}, {"code": "bs", "name": "Bosnian"},
    {"code": "bg", "name": "Bulgarian"}, {"code": "ca", "name": "Catalan"},
    {"code": "ceb", "name": "Cebuano"}, {"code": "zh", "name": "Chinese"},
    {"code": "zh-TW", "name": "Chinese (Traditional)"}, {"code": "co", "name": "Corsican"},
    {"code": "hr", "name": "Croatian"}, {"code": "cs", "name": "Czech"},
    {"code": "da", "name": "Danish"}, {"code": "nl", "name": "Dutch"},
    {"code": "en", "name": "English"}, {"code": "eo", "name": "Esperanto"},
    {"code": "et", "name": "Estonian"}, {"code": "fi", "name": "Finnish"},
    {"code": "fr", "name": "French"}, {"code": "fy", "name": "Frisian"},
    {"code": "gl", "name": "Galician"}, {"code": "ka", "name": "Georgian"},
    {"code": "de", "name": "German"}, {"code": "el", "name": "Greek"},
    {"code": "gu", "name": "Gujarati"}, {"code": "ht", "name": "Haitian Creole"},
    {"code": "ha", "name": "Hausa"}, {"code": "haw", "name": "Hawaiian"},
    {"code": "he", "name": "Hebrew"}, {"code": "hi", "name": "Hindi"},
    {"code": "hmn", "name": "Hmong"}, {"code": "hu", "name": "Hungarian"},
    {"code": "is", "name": "Icelandic"}, {"code": "ig", "name": "Igbo"},
    {"code": "id", "name": "Indonesian"}, {"code": "ga", "name": "Irish"},
    {"code": "it", "name": "Italian"}, {"code": "ja", "name": "Japanese"},
    {"code": "jv", "name": "Javanese"}, {"code": "kn", "name": "Kannada"},
    {"code": "kk", "name": "Kazakh"}, {"code": "km", "name": "Khmer"},
    {"code": "rw", "name": "Kinyarwanda"}, {"code": "ko", "name": "Korean"},
    {"code": "ku", "name": "Kurdish"}, {"code": "ky", "name": "Kyrgyz"},
    {"code": "lo", "name": "Lao"}, {"code": "la", "name": "Latin"},
    {"code": "lv", "name": "Latvian"}, {"code": "lt", "name": "Lithuanian"},
    {"code": "lb", "name": "Luxembourgish"}, {"code": "mk", "name": "Macedonian"},
    {"code": "mg", "name": "Malagasy"}, {"code": "ms", "name": "Malay"},
    {"code": "ml", "name": "Malayalam"}, {"code": "mt", "name": "Maltese"},
    {"code": "mi", "name": "Maori"}, {"code": "mr", "name": "Marathi"},
    {"code": "mn", "name": "Mongolian"}, {"code": "my", "name": "Myanmar (Burmese)"},
    {"code": "ne", "name": "Nepali"}, {"code": "no", "name": "Norwegian"},
    {"code": "ny", "name": "Nyanja"}, {"code": "or", "name": "Odia"},
    {"code": "ps", "name": "Pashto"}, {"code": "fa", "name": "Persian"},
    {"code": "pl", "name": "Polish"}, {"code": "pt", "name": "Portuguese"},
    {"code": "pa", "name": "Punjabi"}, {"code": "ro", "name": "Romanian"},
    {"code": "ru", "name": "Russian"}, {"code": "sm", "name": "Samoan"},
    {"code": "gd", "name": "Scots Gaelic"}, {"code": "sr", "name": "Serbian"},
    {"code": "st", "name": "Sesotho"}, {"code": "sn", "name": "Shona"},
    {"code": "sd", "name": "Sindhi"}, {"code": "si", "name": "Sinhala"},
    {"code": "sk", "name": "Slovak"}, {"code": "sl", "name": "Slovenian"},
    {"code": "so", "name": "Somali"}, {"code": "es", "name": "Spanish"},
    {"code": "su", "name": "Sundanese"}, {"code": "sw", "name": "Swahili"},
    {"code": "sv", "name": "Swedish"}, {"code": "tl", "name": "Tagalog"},
    {"code": "tg", "name": "Tajik"}, {"code": "ta", "name": "Tamil"},
    {"code": "tt", "name": "Tatar"}, {"code": "te", "name": "Telugu"},
    {"code": "th", "name": "Thai"}, {"code": "tr", "name": "Turkish"},
    {"code": "tk", "name": "Turkmen"}, {"code": "uk", "name": "Ukrainian"},
    {"code": "ur", "name": "Urdu"}, {"code": "ug", "name": "Uyghur"},
    {"code": "uz", "name": "Uzbek"}, {"code": "vi", "name": "Vietnamese"},
    {"code": "cy", "name": "Welsh"}, {"code": "xh", "name": "Xhosa"},
    {"code": "yi", "name": "Yiddish"}, {"code": "yo", "name": "Yoruba"},
    {"code": "zu", "name": "Zulu"},
]


def _translator_languages():
    """Return the language codes supported by the live translation provider."""
    now = time.time()
    if _TRANSLATOR_LANGUAGE_CACHE["items"] and now - _TRANSLATOR_LANGUAGE_CACHE["time"] < _TRANSLATOR_LANGUAGE_TTL:
        return _TRANSLATOR_LANGUAGE_CACHE["items"], "cached-provider"

    # LibreTranslate-compatible servers publish their currently supported
    # language list at /languages. The list can vary by server/model.
    for base_url in (
        os.getenv("CERBYD_TRANSLATE_URL", "https://translate.argosopentech.com").rstrip("/"),
        "https://libretranslate.de",
    ):
        try:
            payload = request_json(
                f"{base_url}/languages", params={}, timeout=min(REQUEST_TIMEOUT, 5),
                cache_prefix="mwy_languages",
            )
            if isinstance(payload, list):
                languages = []
                seen = set()
                for item in payload:
                    if not isinstance(item, dict):
                        continue
                    code, name = item.get("code"), item.get("name")
                    if isinstance(code, str) and isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9_-]{2,12}", code) and code.lower() not in seen:
                        languages.append({"code": code, "name": name})
                        seen.add(code.lower())
                if languages:
                    languages.sort(key=lambda item: item["name"].casefold())
                    _TRANSLATOR_LANGUAGE_CACHE.update({"time": now, "items": languages})
                    return languages, "live-provider"
        except Exception:
            continue

    return _TRANSLATOR_LANGUAGE_FALLBACK, "fallback-list"


@app.get("/api/mwy/languages")
def mwy_languages():
    """Return available translator languages for dynamically populated menus."""
    languages, source = _translator_languages()
    return {"success": True, "languages": languages, "count": len(languages), "source": source}


@app.get("/api/mwy/translate")
def mwy_translate(
    text: str = Query(..., min_length=1, max_length=4000),
    source: str = Query("en", min_length=2, max_length=12),
    target: str = Query("hi", min_length=2, max_length=12),
):
    """Translate via a LibreTranslate-compatible service, then MyMemory fallback."""
    text = text.strip()
    if not text:
        return JSONResponse(
            {"success": False, "error": "Enter some text to translate first."},
            status_code=400,
        )

    if not re.fullmatch(r"[A-Za-z0-9_-]{2,12}", source) or not re.fullmatch(r"[A-Za-z0-9_-]{2,12}", target):
        return JSONResponse(
            {"success": False, "error": "Invalid language selection."},
            status_code=400,
        )
    if source.lower() == target.lower():
        return {"success": True, "translatedText": text, "provider": "same-language"}

    errors = []
    base_urls = [os.getenv("CERBYD_TRANSLATE_URL", "https://translate.argosopentech.com").rstrip("/"), "https://libretranslate.de"]
    for base_url in dict.fromkeys(base_urls):
        try:
            response = get_http_session().post(
                f"{base_url}/translate",
                data={"q": text, "source": source, "target": target, "format": "text"},
                timeout=min(REQUEST_TIMEOUT, 10),
            )
            if response.ok:
                payload = response.json()
                if isinstance(payload, dict) and isinstance(payload.get("translatedText"), str) and payload["translatedText"].strip():
                    return {"success": True, "translatedText": payload["translatedText"], "provider": "LibreTranslate"}
            errors.append(f"LibreTranslate HTTP {response.status_code}")
        except Exception as exc:
            errors.append(str(exc)[:120])

    # MyMemory can cover some language pairs not available on the selected
    # LibreTranslate instance. Its coverage is not universal either.
    try:
        payload = request_json(
            "https://api.mymemory.translated.net/get",
            params={"q": text, "langpair": f"{source}|{target}"},
            timeout=min(REQUEST_TIMEOUT, 8),
            cache_prefix="mwy_translate_mymemory",
        )
        if isinstance(payload, dict):
            response_data = payload.get("responseData") or {}
            translated = response_data.get("translatedText") if isinstance(response_data, dict) else None
            if payload.get("responseStatus") == 200 and translated:
                return {"success": True, "translatedText": translated, "provider": "MyMemory"}
            details = payload.get("responseDetails")
            if details:
                errors.append(str(details)[:160])
    except Exception as exc:
        errors.append(str(exc)[:120])

    return JSONResponse(
        {
            "success": False,
            "error": "This language pair is not available from the current translation providers. Try another language pair or configure CERBYD_TRANSLATE_URL with a translation server that supports it.",
            "details": errors[:3],
        },
        status_code=502,
    )


# ============================================================
# STARTUP
# ============================================================

@app.on_event("startup")
def startup():

    init_database()

    print()
    print("=" * 62)
    print(" CERBYD WEB")
    print(" By Cerbyd Inc.")
    print("=" * 62)
    print(f" Version : {APP_VERSION}")
    print(f" Codename: {APP_CODENAME}")
    print(" Engine  : Cerbyd Speed Engine + Public Protection")
    print(f" Workers : {CERBYD_WORKERS}")
    print(f" Cache   : {CACHE_TTL}s")
    print()
    print(" Web Search      : ONLINE")
    print(" MWY Tools       : ONLINE (Maps + Translator API)")
    print(" Smart Answers   : ONLINE")
    print(" Wikipedia       : ONLINE")
    print(" Dictionary      : ONLINE")
    print(" Calculator      : ONLINE")
    print(" Images          : ONLINE")
    print(" News            : ONLINE")
    print(" Shopping        : ONLINE")
    print(" Directory       : ONLINE")
    print(" Network Test    : ONLINE")
    print(" Network Ping    : ONLINE")
    print(" Database        : ONLINE")
    print(f" Database File   : {DATABASE_FILE.name}")
    print(" Rate Limiting   : ONLINE")
    print(" Security Headers: ONLINE")
    print(" Compression     : ONLINE")
    print()
    print(" Cerbyd Web is ready.")
    print("=" * 62)
    print()


# ============================================================
# SHUTDOWN
# ============================================================

@app.on_event("shutdown")
def shutdown():
    try:
        CERBYD_EXECUTOR.shutdown(wait=False, cancel_futures=True)
    except Exception:
        pass


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":

    import uvicorn

    uvicorn.run(
        "main:app",
        host=os.getenv("HOST", "0.0.0.0"),
        port=int(os.getenv("PORT", "8000")),
        reload=os.getenv("CERBYD_RELOAD", "false").lower() == "true",
        proxy_headers=os.getenv("CERBYD_PROXY_HEADERS", "true").lower() == "true",
        forwarded_allow_ips=os.getenv("CERBYD_FORWARDED_ALLOW_IPS", "*")
    )
