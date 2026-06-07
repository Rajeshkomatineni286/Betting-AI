#!/usr/bin/env python3
import asyncio
import contextlib
import dataclasses
import hashlib
import json
import logging
import math
import os
import random
import signal
import sqlite3
import statistics
import time
import traceback
from collections import defaultdict, deque
from dataclasses import dataclass, field
from datetime import datetime, date, timedelta, timezone
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path
from typing import Any, Callable, Deque, Dict, Iterable, List, Optional, Sequence, Tuple

import requests
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from dotenv import load_dotenv
from playwright.async_api import Browser, BrowserContext, Error as PlaywrightError, Page, async_playwright

APP_NAME = "BETACULAR_AI"
BASE_DIR = Path(__file__).resolve().parent
LOG_PATH = BASE_DIR / "betacular_ai.log"
DB_PATH = BASE_DIR / "betacular_ai.sqlite3"
STATE_PATH = BASE_DIR / "betacular_ai_state.json"
SCREENSHOT_DIR = BASE_DIR / "betacular_ai_artifacts"
REPORT_DIR = BASE_DIR / "betacular_ai_reports"
SNAPSHOT_DIR = SCREENSHOT_DIR / "html"
DEFAULT_BETACULAR_URL = "https://www.betacular.com/"
LIVE_SCAN_INTERVAL_SECONDS = 5
HEALTH_INTERVAL_MINUTES = 30
MAX_ODDS_HISTORY = 720
MAX_SCORE_HISTORY = 720
MIN_CONCURRENT_MATCH_CAPACITY = 20
IGNORED_STATUSES = {"suspended", "postponed", "retired", "abandoned", "closed", "settled"}
LOGIN_USER_SELECTORS = [
    "input[name='username']",
    "input[name='email']",
    "input[type='email']",
    "input[id*='user' i]",
]
LOGIN_PASSWORD_SELECTORS = [
    "input[name='password']",
    "input[type='password']",
]
LOGIN_BUTTON_SELECTORS = [
    "button[type='submit']",
    "input[type='submit']",
    "button:has-text('Log in')",
    "button:has-text('Login')",
    "button:has-text('Sign in')",
    "a:has-text('Log in')",
    "a:has-text('Login')",
    "a:has-text('Sign in')",
]
TENNIS_NAV_SELECTORS = [
    "a:has-text('Tennis')",
    "button:has-text('Tennis')",
    "[data-sport*='tennis' i]",
    "[href*='tennis' i]",
]
MATCH_SELECTOR_CANDIDATES = [
    "[data-testid*='match' i]",
    "[data-test*='match' i]",
    "[class*='match' i]",
    "[class*='event' i]",
    "[data-event-id]",
    "[id*='event' i]",
]
ODDS_SELECTOR_CANDIDATES = [
    "[data-testid*='odds' i]",
    "[data-test*='odds' i]",
    "[class*='odds' i]",
    "[class*='price' i]",
    "button[class*='selection' i]",
    "button:has-text('.')",
]
BACK_SELECTOR_CANDIDATES = [
    "[data-testid*='back' i]",
    "[data-test*='back' i]",
    "[class*='back' i]",
    "button:has-text('Back')",
]
LAY_SELECTOR_CANDIDATES = [
    "[data-testid*='lay' i]",
    "[data-test*='lay' i]",
    "[class*='lay' i]",
    "button:has-text('Lay')",
]
STATUS_SELECTOR_CANDIDATES = [
    "[data-testid*='status' i]",
    "[data-test*='status' i]",
    "[class*='status' i]",
    "[class*='state' i]",
    "[class*='live' i]",
]
SCORE_SELECTOR_CANDIDATES = [
    "[data-testid*='score' i]",
    "[data-test*='score' i]",
    "[class*='score' i]",
    "[class*='points' i]",
    "[class*='game' i]",
]


def utc_now() -> datetime:
    return datetime.now(timezone.utc)


def iso_now() -> str:
    return utc_now().isoformat(timespec="seconds")


def env_decimal(name: str, default: str) -> Decimal:
    value = os.getenv(name, default).strip()
    try:
        return Decimal(value)
    except Exception:
        return Decimal(default)


def env_int(name: str, default: int) -> int:
    value = os.getenv(name, str(default)).strip()
    try:
        return int(value)
    except Exception:
        return default


def round_money(value: Decimal) -> Decimal:
    return value.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)


def safe_float(value: Any, default: float = 0.0) -> float:
    if value is None:
        return default
    text = str(value).strip().replace(",", "")
    filtered = "".join(ch for ch in text if ch.isdigit() or ch in ".-")
    if filtered in {"", ".", "-", "-."}:
        return default
    try:
        return float(filtered)
    except Exception:
        return default


def normalize_text(value: Optional[str]) -> str:
    return " ".join((value or "").replace("\u00a0", " ").split())


def stable_id(parts: Sequence[str]) -> str:
    source = "|".join(normalize_text(part).lower() for part in parts if part)
    return hashlib.sha256(source.encode("utf-8")).hexdigest()[:24]


def parse_score_text(text: str) -> Tuple[str, str, str]:
    normalized = normalize_text(text)
    set_score = ""
    game_score = ""
    point_score = ""
    tokens = normalized.replace("-", " ").replace(":", " ").split()
    numeric_tokens = [token for token in tokens if token.replace(".", "", 1).isdigit()]
    tennis_points = {"0", "15", "30", "40", "AD", "A"}
    point_tokens = [token for token in tokens if token.upper() in tennis_points]
    if len(numeric_tokens) >= 2:
        set_score = f"{numeric_tokens[0]}-{numeric_tokens[1]}"
    if len(numeric_tokens) >= 4:
        game_score = f"{numeric_tokens[2]}-{numeric_tokens[3]}"
    if len(point_tokens) >= 2:
        point_score = f"{point_tokens[-2].upper()}-{point_tokens[-1].upper()}"
    return set_score, game_score, point_score


def implied_probability(odds: float) -> float:
    return 1.0 / odds if odds and odds > 1.0 else 0.0


def clamp(value: float, minimum: float, maximum: float) -> float:
    return max(minimum, min(maximum, value))


class JsonFormatter(logging.Formatter):
    def format(self, record: logging.LogRecord) -> str:
        payload = {
            "ts": datetime.fromtimestamp(record.created, timezone.utc).isoformat(timespec="seconds"),
            "level": record.levelname,
            "logger": record.name,
            "message": record.getMessage(),
        }
        if record.exc_info:
            payload["exception"] = self.formatException(record.exc_info)
        for key in ("match_id", "strategy", "trade_id", "event"):
            if hasattr(record, key):
                payload[key] = getattr(record, key)
        return json.dumps(payload, ensure_ascii=False)


def configure_logging() -> logging.Logger:
    logger = logging.getLogger(APP_NAME)
    logger.setLevel(logging.INFO)
    logger.handlers.clear()
    file_handler = logging.FileHandler(LOG_PATH, encoding="utf-8")
    file_handler.setFormatter(JsonFormatter())
    stream_handler = logging.StreamHandler()
    stream_handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    logger.addHandler(file_handler)
    logger.addHandler(stream_handler)
    logging.getLogger("apscheduler").setLevel(logging.WARNING)
    return logger


LOGGER = configure_logging()


@dataclass
class Config:
    username: str
    password: str
    telegram_bot_token: str
    telegram_chat_id: str
    initial_bankroll: Decimal
    max_stake: Decimal
    max_exposure: Decimal
    daily_loss_limit: Decimal
    betacular_url: str
    headless: bool
    maximum_simultaneous_trades: int
    scan_interval_seconds: int

    @classmethod
    def load(cls) -> "Config":
        load_dotenv(BASE_DIR / ".env")
        return cls(
            username=os.getenv("BETACULAR_USERNAME", "").strip(),
            password=os.getenv("BETACULAR_PASSWORD", "").strip(),
            telegram_bot_token=os.getenv("TELEGRAM_BOT_TOKEN", "").strip(),
            telegram_chat_id=os.getenv("TELEGRAM_CHAT_ID", "").strip(),
            initial_bankroll=env_decimal("INITIAL_BANKROLL", "1000"),
            max_stake=env_decimal("MAX_STAKE", "25"),
            max_exposure=env_decimal("MAX_EXPOSURE", "100"),
            daily_loss_limit=env_decimal("DAILY_LOSS_LIMIT", "100"),
            betacular_url=os.getenv("BETACULAR_URL", DEFAULT_BETACULAR_URL).strip() or DEFAULT_BETACULAR_URL,
            headless=os.getenv("HEADLESS", "true").strip().lower() not in {"0", "false", "no"},
            maximum_simultaneous_trades=env_int("MAXIMUM_SIMULTANEOUS_TRADES", 8),
            scan_interval_seconds=env_int("SCAN_INTERVAL_SECONDS", LIVE_SCAN_INTERVAL_SECONDS),
        )


@dataclass
class SelectorSet:
    tennis_market: str = ""
    match: str = ""
    odds: str = ""
    back: str = ""
    lay: str = ""
    market_status: str = ""
    score: str = ""
    discovered_at: str = ""

    def complete(self) -> bool:
        return all([self.tennis_market, self.match, self.odds, self.back, self.lay, self.market_status, self.score])


@dataclass
class MatchSnapshot:
    match_id: str
    tournament: str
    player_a: str
    player_b: str
    status: str
    set_score: str
    game_score: str
    point_score: str
    back_odds_a: float
    lay_odds_a: float
    back_odds_b: float
    lay_odds_b: float
    liquidity: float
    timestamp: str


@dataclass
class StrategySignal:
    strategy_name: str
    entry_signal: bool
    exit_signal: bool
    confidence: float
    side: str
    reason: str


@dataclass
class MatchState:
    match_id: str
    tournament: str = ""
    player_a: str = ""
    player_b: str = ""
    status: str = ""
    odds_history: Deque[MatchSnapshot] = field(default_factory=lambda: deque(maxlen=MAX_ODDS_HISTORY))
    score_history: Deque[Tuple[str, str, str, str]] = field(default_factory=lambda: deque(maxlen=MAX_SCORE_HISTORY))
    strategy_signals: Dict[str, StrategySignal] = field(default_factory=dict)
    opportunity_score: float = 0.0
    liquidity_score: float = 0.0
    volatility_score: float = 0.0
    odds_movement_score: float = 0.0
    confidence_score: float = 0.0
    last_seen: str = ""


@dataclass
class Position:
    trade_id: str
    match_id: str
    strategy_name: str
    side: str
    action: str
    player: str
    odds: Decimal
    stake: Decimal
    opened_at: str
    status: str = "OPEN"
    closed_at: str = ""
    hedge_odds: Decimal = Decimal("0")
    profit_a: Decimal = Decimal("0")
    profit_b: Decimal = Decimal("0")
    realized_pnl: Decimal = Decimal("0")


class TelegramNotifier:
    def __init__(self, config: Config, logger: logging.Logger):
        self.config = config
        self.logger = logger
        self.session = requests.Session()

    def enabled(self) -> bool:
        return bool(self.config.telegram_bot_token and self.config.telegram_chat_id)

    async def send(self, title: str, message: str) -> None:
        if not self.enabled():
            self.logger.info("telegram disabled: %s", title, extra={"event": "telegram_disabled"})
            return
        text = f"{APP_NAME} | {title}\n{message}"
        await asyncio.to_thread(self._send_sync, text[:3900])

    def _send_sync(self, text: str) -> None:
        url = f"https://api.telegram.org/bot{self.config.telegram_bot_token}/sendMessage"
        response = self.session.post(
            url,
            json={"chat_id": self.config.telegram_chat_id, "text": text, "disable_web_page_preview": True},
            timeout=15,
        )
        response.raise_for_status()


class Database:
    def __init__(self, path: Path, logger: logging.Logger):
        self.path = path
        self.logger = logger
        self.lock = asyncio.Lock()
        self.connection = sqlite3.connect(self.path, check_same_thread=False, timeout=30, isolation_level=None)
        self.connection.row_factory = sqlite3.Row
        self.connection.execute("PRAGMA journal_mode=WAL")
        self.connection.execute("PRAGMA synchronous=NORMAL")
        self.connection.execute("PRAGMA busy_timeout=30000")

    async def initialize(self) -> None:
        schema = [
            """
            CREATE TABLE IF NOT EXISTS matches (
                match_id TEXT PRIMARY KEY,
                tournament TEXT,
                player_a TEXT,
                player_b TEXT,
                status TEXT,
                opportunity_score REAL DEFAULT 0,
                first_seen TEXT,
                last_seen TEXT
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS scores (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                match_id TEXT,
                set_score TEXT,
                game_score TEXT,
                point_score TEXT,
                timestamp TEXT
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS odds (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                match_id TEXT,
                back_odds_a REAL,
                lay_odds_a REAL,
                back_odds_b REAL,
                lay_odds_b REAL,
                liquidity REAL,
                timestamp TEXT
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS strategies (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                match_id TEXT,
                strategy_name TEXT,
                entry_signal INTEGER,
                exit_signal INTEGER,
                confidence REAL,
                side TEXT,
                reason TEXT,
                opportunity_score REAL,
                timestamp TEXT
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS trades (
                trade_id TEXT PRIMARY KEY,
                match_id TEXT,
                strategy_name TEXT,
                side TEXT,
                action TEXT,
                player TEXT,
                odds TEXT,
                stake TEXT,
                opened_at TEXT,
                status TEXT,
                closed_at TEXT,
                hedge_odds TEXT,
                profit_a TEXT,
                profit_b TEXT,
                realized_pnl TEXT
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS reports (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                period TEXT,
                period_start TEXT,
                period_end TEXT,
                body TEXT,
                created_at TEXT
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS alerts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alert_type TEXT,
                message TEXT,
                created_at TEXT
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS errors (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                subsystem TEXT,
                message TEXT,
                stack TEXT,
                created_at TEXT
            )
            """,
        ]
        async with self.lock:
            await asyncio.to_thread(self._execute_many, schema)

    def _execute_many(self, statements: Sequence[str]) -> None:
        cursor = self.connection.cursor()
        for statement in statements:
            cursor.execute(statement)
        self.connection.commit()

    async def execute(self, statement: str, parameters: Sequence[Any] = ()) -> None:
        async with self.lock:
            await asyncio.to_thread(self._execute, statement, parameters)

    def _execute(self, statement: str, parameters: Sequence[Any]) -> None:
        self.connection.execute(statement, parameters)
        self.connection.commit()

    async def query(self, statement: str, parameters: Sequence[Any] = ()) -> List[sqlite3.Row]:
        async with self.lock:
            return await asyncio.to_thread(self._query, statement, parameters)

    def _query(self, statement: str, parameters: Sequence[Any]) -> List[sqlite3.Row]:
        cursor = self.connection.execute(statement, parameters)
        return cursor.fetchall()

    async def upsert_match(self, snapshot: MatchSnapshot, opportunity_score: float) -> None:
        await self.execute(
            """
            INSERT INTO matches(match_id, tournament, player_a, player_b, status, opportunity_score, first_seen, last_seen)
            VALUES(?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(match_id) DO UPDATE SET
                tournament=excluded.tournament,
                player_a=excluded.player_a,
                player_b=excluded.player_b,
                status=excluded.status,
                opportunity_score=excluded.opportunity_score,
                last_seen=excluded.last_seen
            """,
            (
                snapshot.match_id,
                snapshot.tournament,
                snapshot.player_a,
                snapshot.player_b,
                snapshot.status,
                opportunity_score,
                snapshot.timestamp,
                snapshot.timestamp,
            ),
        )

    async def insert_score(self, snapshot: MatchSnapshot) -> None:
        await self.execute(
            "INSERT INTO scores(match_id, set_score, game_score, point_score, timestamp) VALUES(?, ?, ?, ?, ?)",
            (snapshot.match_id, snapshot.set_score, snapshot.game_score, snapshot.point_score, snapshot.timestamp),
        )

    async def insert_odds(self, snapshot: MatchSnapshot) -> None:
        await self.execute(
            """
            INSERT INTO odds(match_id, back_odds_a, lay_odds_a, back_odds_b, lay_odds_b, liquidity, timestamp)
            VALUES(?, ?, ?, ?, ?, ?, ?)
            """,
            (
                snapshot.match_id,
                snapshot.back_odds_a,
                snapshot.lay_odds_a,
                snapshot.back_odds_b,
                snapshot.lay_odds_b,
                snapshot.liquidity,
                snapshot.timestamp,
            ),
        )

    async def insert_strategy(self, match_id: str, signal_value: StrategySignal, opportunity_score: float) -> None:
        await self.execute(
            """
            INSERT INTO strategies(match_id, strategy_name, entry_signal, exit_signal, confidence, side, reason, opportunity_score, timestamp)
            VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                match_id,
                signal_value.strategy_name,
                int(signal_value.entry_signal),
                int(signal_value.exit_signal),
                signal_value.confidence,
                signal_value.side,
                signal_value.reason,
                opportunity_score,
                iso_now(),
            ),
        )

    async def upsert_trade(self, position: Position) -> None:
        await self.execute(
            """
            INSERT INTO trades(trade_id, match_id, strategy_name, side, action, player, odds, stake, opened_at, status, closed_at, hedge_odds, profit_a, profit_b, realized_pnl)
            VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(trade_id) DO UPDATE SET
                status=excluded.status,
                closed_at=excluded.closed_at,
                hedge_odds=excluded.hedge_odds,
                profit_a=excluded.profit_a,
                profit_b=excluded.profit_b,
                realized_pnl=excluded.realized_pnl
            """,
            (
                position.trade_id,
                position.match_id,
                position.strategy_name,
                position.side,
                position.action,
                position.player,
                str(position.odds),
                str(position.stake),
                position.opened_at,
                position.status,
                position.closed_at,
                str(position.hedge_odds),
                str(position.profit_a),
                str(position.profit_b),
                str(position.realized_pnl),
            ),
        )

    async def insert_report(self, period: str, start: str, end: str, body: str) -> None:
        await self.execute(
            "INSERT INTO reports(period, period_start, period_end, body, created_at) VALUES(?, ?, ?, ?, ?)",
            (period, start, end, body, iso_now()),
        )

    async def insert_alert(self, alert_type: str, message: str) -> None:
        await self.execute("INSERT INTO alerts(alert_type, message, created_at) VALUES(?, ?, ?)", (alert_type, message, iso_now()))

    async def insert_error(self, subsystem: str, exc: BaseException) -> None:
        await self.execute(
            "INSERT INTO errors(subsystem, message, stack, created_at) VALUES(?, ?, ?, ?)",
            (subsystem, str(exc), traceback.format_exc(), iso_now()),
        )

    async def close(self) -> None:
        async with self.lock:
            await asyncio.to_thread(self.connection.close)


class BrowserEngine:
    def __init__(self, config: Config, notifier: TelegramNotifier, db: Database, logger: logging.Logger):
        self.config = config
        self.notifier = notifier
        self.db = db
        self.logger = logger
        self.playwright_manager: Any = None
        self.browser: Optional[Browser] = None
        self.context: Optional[BrowserContext] = None
        self.page: Optional[Page] = None
        self.logged_in = False
        self.reconnect_lock = asyncio.Lock()

    async def start(self) -> None:
        await self.stop()
        self.playwright_manager = await async_playwright().start()
        self.browser = await self.playwright_manager.chromium.launch(headless=self.config.headless, args=["--no-sandbox", "--disable-dev-shm-usage"])
        self.context = await self.browser.new_context(viewport={"width": 1440, "height": 1100})
        self.page = await self.context.new_page()
        self.page.set_default_timeout(12000)
        self.page.on("crash", lambda _: asyncio.create_task(self._browser_crash_alert()))
        self.logger.info("browser launched", extra={"event": "browser_start"})

    async def _browser_crash_alert(self) -> None:
        self.logger.error("browser page crashed", extra={"event": "browser_crash"})
        await self.db.insert_alert("browser_crash", "Browser page crashed")
        await self.notifier.send("Browser crash", "Browser page crashed; recovery engine restarting browser")
        await self.reconnect()

    async def stop(self) -> None:
        if self.context:
            with contextlib.suppress(Exception):
                await self.context.close()
        if self.browser:
            with contextlib.suppress(Exception):
                await self.browser.close()
        if self.playwright_manager:
            with contextlib.suppress(Exception):
                await self.playwright_manager.stop()
        self.browser = None
        self.context = None
        self.page = None
        self.playwright_manager = None
        self.logged_in = False

    async def reconnect(self) -> None:
        async with self.reconnect_lock:
            await self.start()
            await self.login()

    async def login(self) -> bool:
        if not self.page:
            await self.start()
        page = self.require_page()
        try:
            await page.goto(self.config.betacular_url, wait_until="domcontentloaded")
            await page.wait_for_load_state("networkidle", timeout=15000)
            await self._open_login_form(page)
            user_selector = await self._first_visible(page, LOGIN_USER_SELECTORS)
            password_selector = await self._first_visible(page, LOGIN_PASSWORD_SELECTORS)
            if user_selector and password_selector and self.config.username and self.config.password:
                await page.fill(user_selector, self.config.username)
                await page.fill(password_selector, self.config.password)
                button_selector = await self._first_visible(page, LOGIN_BUTTON_SELECTORS)
                if button_selector:
                    await page.click(button_selector)
                else:
                    await page.keyboard.press("Enter")
                await page.wait_for_load_state("networkidle", timeout=15000)
            self.logged_in = await self._is_authenticated(page)
            if not self.logged_in:
                raise RuntimeError("Login failed or credentials were not accepted")
            self.logger.info("login successful", extra={"event": "login_success"})
            return True
        except Exception as exc:
            self.logged_in = False
            self.logger.exception("login failure", extra={"event": "login_failure"})
            await self.db.insert_error("login", exc)
            await self.db.insert_alert("login_failure", str(exc))
            await self.notifier.send("Login failure", str(exc))
            await self.capture_artifacts("login_failure")
            return False

    async def _open_login_form(self, page: Page) -> None:
        for selector in LOGIN_BUTTON_SELECTORS + ["text=/login/i", "text=/sign in/i"]:
            with contextlib.suppress(Exception):
                locator = page.locator(selector).first
                if await locator.count() and await locator.is_visible():
                    await locator.click()
                    await page.wait_for_timeout(1000)
                    return

    async def _is_authenticated(self, page: Page) -> bool:
        logout_markers = ["text=/logout/i", "text=/log out/i", "text=/my account/i", "text=/account/i", "text=/balance/i"]
        for selector in logout_markers:
            with contextlib.suppress(Exception):
                locator = page.locator(selector).first
                if await locator.count() and await locator.is_visible():
                    return True
        if self.config.username and self.config.password:
            password_selector = await self._first_visible(page, LOGIN_PASSWORD_SELECTORS)
            return password_selector == ""
        return True

    async def ensure_session(self) -> bool:
        page = self.require_page()
        authenticated = await self._is_authenticated(page)
        if authenticated:
            self.logged_in = True
            return True
        self.logged_in = False
        self.logger.warning("logout detected", extra={"event": "logout_detected"})
        await self.db.insert_alert("logout_detected", "Session logout detected")
        await self.notifier.send("Logout detected", "Session expired; attempting automatic reconnect")
        return await self.login()

    async def _first_visible(self, page: Page, selectors: Sequence[str]) -> str:
        for selector in selectors:
            with contextlib.suppress(Exception):
                locator = page.locator(selector).first
                if await locator.count() and await locator.is_visible():
                    return selector
        return ""

    async def capture_artifacts(self, prefix: str) -> None:
        SCREENSHOT_DIR.mkdir(exist_ok=True)
        SNAPSHOT_DIR.mkdir(parents=True, exist_ok=True)
        page = self.page
        if not page:
            return
        stamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        screenshot_path = SCREENSHOT_DIR / f"{prefix}_{stamp}.png"
        html_path = SNAPSHOT_DIR / f"{prefix}_{stamp}.html"
        with contextlib.suppress(Exception):
            await page.screenshot(path=str(screenshot_path), full_page=True)
        with contextlib.suppress(Exception):
            html_path.write_text(await page.content(), encoding="utf-8")
        self.logger.info("captured artifacts %s %s", screenshot_path, html_path, extra={"event": "artifact_capture"})

    def require_page(self) -> Page:
        if not self.page:
            raise RuntimeError("Browser page is not initialized")
        return self.page


class DiscoveryEngine:
    def __init__(self, browser_engine: BrowserEngine, logger: logging.Logger):
        self.browser_engine = browser_engine
        self.logger = logger
        self.selectors = SelectorSet()

    async def discover(self) -> SelectorSet:
        page = self.browser_engine.require_page()
        await self._navigate_to_tennis(page)
        for attempt in range(1, 4):
            self.selectors = SelectorSet(
                tennis_market=await self._discover_first(page, TENNIS_NAV_SELECTORS),
                match=await self._discover_first(page, MATCH_SELECTOR_CANDIDATES),
                odds=await self._discover_first(page, ODDS_SELECTOR_CANDIDATES),
                back=await self._discover_first(page, BACK_SELECTOR_CANDIDATES),
                lay=await self._discover_first(page, LAY_SELECTOR_CANDIDATES),
                market_status=await self._discover_first(page, STATUS_SELECTOR_CANDIDATES),
                score=await self._discover_first(page, SCORE_SELECTOR_CANDIDATES),
                discovered_at=iso_now(),
            )
            if self.selectors.complete():
                self.logger.info("selector discovery complete %s", dataclasses.asdict(self.selectors), extra={"event": "selector_discovery"})
                return self.selectors
            await self.browser_engine.capture_artifacts(f"selector_discovery_attempt_{attempt}")
            await page.wait_for_timeout(1500 * attempt)
            await page.reload(wait_until="domcontentloaded")
        self.selectors = self._fallback_selectors()
        self.logger.warning("selector discovery incomplete; using resilient fallback selectors", extra={"event": "selector_discovery_fallback"})
        return self.selectors

    async def _navigate_to_tennis(self, page: Page) -> None:
        await page.goto(self.browser_engine.config.betacular_url, wait_until="domcontentloaded")
        await page.wait_for_load_state("networkidle", timeout=15000)
        for selector in TENNIS_NAV_SELECTORS:
            with contextlib.suppress(Exception):
                locator = page.locator(selector).first
                if await locator.count() and await locator.is_visible():
                    await locator.click()
                    await page.wait_for_load_state("networkidle", timeout=15000)
                    return

    async def _discover_first(self, page: Page, candidates: Sequence[str]) -> str:
        for selector in candidates:
            with contextlib.suppress(Exception):
                count = await page.locator(selector).count()
                if count > 0:
                    return selector
        return ""

    def _fallback_selectors(self) -> SelectorSet:
        return SelectorSet(
            tennis_market="a:has-text('Tennis'), button:has-text('Tennis'), [href*='tennis' i]",
            match="[data-testid*='match' i], [class*='match' i], [class*='event' i], [data-event-id]",
            odds="[data-testid*='odds' i], [class*='odds' i], [class*='price' i], button",
            back="[data-testid*='back' i], [class*='back' i], button:has-text('Back')",
            lay="[data-testid*='lay' i], [class*='lay' i], button:has-text('Lay')",
            market_status="[data-testid*='status' i], [class*='status' i], [class*='live' i]",
            score="[data-testid*='score' i], [class*='score' i], [class*='game' i], [class*='points' i]",
            discovered_at=iso_now(),
        )


class StrategyEngine:
    def evaluate(self, state: MatchState) -> List[StrategySignal]:
        snapshots = list(state.odds_history)
        if len(snapshots) < 2:
            return [self._neutral(name, "insufficient history") for name in self.strategy_names()]
        return [
            self.first_break(state),
            self.break_back(state),
            self.momentum_reversal(state),
            self.set_winner_reversal(state),
            self.five_five_volatility(state),
            self.tiebreak(state),
        ]

    def strategy_names(self) -> List[str]:
        return [
            "First Break Strategy",
            "Break Back Strategy",
            "Momentum Reversal Strategy",
            "Set Winner Reversal Strategy",
            "5-5 Volatility Strategy",
            "Tiebreak Strategy",
        ]

    def _neutral(self, name: str, reason: str) -> StrategySignal:
        return StrategySignal(name, False, False, 0.0, "", reason)

    def first_break(self, state: MatchState) -> StrategySignal:
        latest = state.odds_history[-1]
        games = [safe_float(x) for x in latest.game_score.split("-") if x != ""]
        movement = self._recent_movement(state, "a")
        early_set = sum(games) <= 5 if len(games) == 2 else True
        entry = early_set and abs(movement) >= 0.06 and latest.back_odds_a > 1.2
        side = "A" if movement < 0 else "B"
        confidence = clamp(45 + abs(movement) * 260 + state.volatility_score * 0.25, 0, 100) if entry else clamp(abs(movement) * 130, 0, 45)
        exit_signal = not early_set or abs(movement) < 0.015
        return StrategySignal("First Break Strategy", entry, exit_signal, confidence, side, "early-game break pressure detected")

    def break_back(self, state: MatchState) -> StrategySignal:
        latest = state.odds_history[-1]
        games = [safe_float(x) for x in latest.game_score.split("-") if x != ""]
        imbalance = abs(games[0] - games[1]) if len(games) == 2 else 0
        movement_a = self._recent_movement(state, "a")
        entry = imbalance == 1 and abs(movement_a) >= 0.04
        side = "B" if movement_a < 0 else "A"
        confidence = clamp(40 + abs(movement_a) * 230 + state.volatility_score * 0.20, 0, 100) if entry else clamp(abs(movement_a) * 100, 0, 40)
        return StrategySignal("Break Back Strategy", entry, imbalance == 0, confidence, side, "single-break imbalance with reversal pressure")

    def momentum_reversal(self, state: MatchState) -> StrategySignal:
        snapshots = list(state.odds_history)[-6:]
        probabilities = [implied_probability(s.back_odds_a) for s in snapshots if s.back_odds_a > 1]
        if len(probabilities) < 4:
            return self._neutral("Momentum Reversal Strategy", "insufficient momentum sample")
        deltas = [probabilities[i] - probabilities[i - 1] for i in range(1, len(probabilities))]
        reversal = len(deltas) >= 3 and deltas[-1] * sum(deltas[:-1]) < 0 and abs(deltas[-1]) > 0.015
        side = "A" if deltas[-1] > 0 else "B"
        confidence = clamp(35 + abs(deltas[-1]) * 900 + state.volatility_score * 0.25, 0, 100) if reversal else clamp(abs(sum(deltas)) * 150, 0, 35)
        return StrategySignal("Momentum Reversal Strategy", reversal, not reversal and abs(sum(deltas[-2:])) < 0.01, confidence, side, "probability momentum reversal")

    def set_winner_reversal(self, state: MatchState) -> StrategySignal:
        latest = state.odds_history[-1]
        sets = [safe_float(x) for x in latest.set_score.split("-") if x != ""]
        movement = self._recent_movement(state, "a")
        set_edge = abs(sets[0] - sets[1]) >= 1 if len(sets) == 2 else False
        entry = set_edge and abs(movement) > 0.035 and 1.35 <= latest.back_odds_a <= 5.0
        side = "B" if sets and sets[0] > sets[1] else "A"
        confidence = clamp(38 + abs(movement) * 260 + state.confidence_score * 0.20, 0, 100) if entry else clamp(abs(movement) * 100, 0, 38)
        return StrategySignal("Set Winner Reversal Strategy", entry, False, confidence, side, "set-score favorite vulnerable to reversal")

    def five_five_volatility(self, state: MatchState) -> StrategySignal:
        latest = state.odds_history[-1]
        entry = latest.game_score in {"5-5", "6-5", "5-6"} and state.volatility_score >= 45
        movement = self._recent_movement(state, "a")
        side = "A" if movement < 0 else "B"
        confidence = clamp(42 + state.volatility_score * 0.55 + abs(movement) * 120, 0, 100) if entry else clamp(state.volatility_score * 0.60, 0, 42)
        return StrategySignal("5-5 Volatility Strategy", entry, latest.game_score not in {"5-5", "6-5", "5-6"}, confidence, side, "late-set volatility cluster")

    def tiebreak(self, state: MatchState) -> StrategySignal:
        latest = state.odds_history[-1]
        text = f"{latest.game_score} {latest.point_score}".lower()
        is_tiebreak = "6-6" in text or "tb" in text or "tie" in text
        movement = self._recent_movement(state, "a")
        entry = is_tiebreak and state.volatility_score >= 25
        side = "A" if movement < 0 else "B"
        confidence = clamp(45 + state.volatility_score * 0.45 + abs(movement) * 170, 0, 100) if entry else clamp(state.volatility_score * 0.40, 0, 45)
        return StrategySignal("Tiebreak Strategy", entry, not is_tiebreak, confidence, side, "tiebreak price instability")

    def _recent_movement(self, state: MatchState, runner: str) -> float:
        snapshots = list(state.odds_history)[-6:]
        if len(snapshots) < 2:
            return 0.0
        first = snapshots[0].back_odds_a if runner == "a" else snapshots[0].back_odds_b
        last = snapshots[-1].back_odds_a if runner == "a" else snapshots[-1].back_odds_b
        return implied_probability(last) - implied_probability(first)


class RankingEngine:
    def rank(self, state: MatchState) -> float:
        snapshots = list(state.odds_history)
        if not snapshots:
            state.opportunity_score = 0.0
            return 0.0
        latest = snapshots[-1]
        state.liquidity_score = clamp(math.log10(max(latest.liquidity, 1)) * 18, 0, 100)
        probs_a = [implied_probability(s.back_odds_a) for s in snapshots[-24:] if s.back_odds_a > 1]
        probs_b = [implied_probability(s.back_odds_b) for s in snapshots[-24:] if s.back_odds_b > 1]
        all_probs = probs_a + probs_b
        volatility = statistics.pstdev(all_probs) * 420 if len(all_probs) >= 2 else 0.0
        state.volatility_score = clamp(volatility, 0, 100)
        movement = 0.0
        if len(probs_a) >= 2:
            movement += abs(probs_a[-1] - probs_a[0]) * 320
        if len(probs_b) >= 2:
            movement += abs(probs_b[-1] - probs_b[0]) * 320
        state.odds_movement_score = clamp(movement, 0, 100)
        confidences = [signal_value.confidence for signal_value in state.strategy_signals.values()]
        state.confidence_score = max(confidences) if confidences else 0.0
        score = (
            state.liquidity_score * 0.20
            + state.odds_movement_score * 0.25
            + state.volatility_score * 0.25
            + state.confidence_score * 0.30
        )
        state.opportunity_score = clamp(score, 0, 100)
        return state.opportunity_score


class RiskEngine:
    def __init__(self, config: Config, logger: logging.Logger):
        self.config = config
        self.logger = logger
        self.trading_enabled = True
        self.daily_realized_pnl = Decimal("0")

    def can_open(self, stake: Decimal, exposure: Decimal, open_trade_count: int) -> Tuple[bool, str]:
        if not self.trading_enabled:
            return False, "trading disabled"
        if stake > self.config.max_stake:
            return False, "stake exceeds max stake"
        if exposure + stake > self.config.max_exposure:
            return False, "exposure exceeds max exposure"
        if open_trade_count >= self.config.maximum_simultaneous_trades:
            return False, "maximum simultaneous trades reached"
        if self.daily_realized_pnl <= -abs(self.config.daily_loss_limit):
            self.trading_enabled = False
            return False, "daily loss limit breached"
        return True, "approved"

    def record_pnl(self, pnl: Decimal) -> None:
        self.daily_realized_pnl = round_money(self.daily_realized_pnl + pnl)
        if self.daily_realized_pnl <= -abs(self.config.daily_loss_limit):
            self.trading_enabled = False
            self.logger.warning("daily loss limit breached", extra={"event": "risk_stop"})

    def reset_daily(self) -> None:
        self.daily_realized_pnl = Decimal("0")
        self.trading_enabled = True


class PaperTradingEngine:
    def __init__(self, config: Config, db: Database, risk: RiskEngine, logger: logging.Logger):
        self.config = config
        self.db = db
        self.risk = risk
        self.logger = logger
        self.bankroll = config.initial_bankroll
        self.open_positions: Dict[str, Position] = {}
        self.closed_positions: Dict[str, Position] = {}

    def exposure(self) -> Decimal:
        return round_money(sum((position.stake for position in self.open_positions.values()), Decimal("0")))

    async def evaluate(self, state: MatchState) -> None:
        await self._close_positions_on_exit(state)
        actionable = [sig for sig in state.strategy_signals.values() if sig.entry_signal and sig.confidence >= 62]
        actionable.sort(key=lambda sig: sig.confidence, reverse=True)
        for signal_value in actionable[:2]:
            if self._has_open_strategy(state.match_id, signal_value.strategy_name):
                continue
            await self._open_position(state, signal_value)

    def _has_open_strategy(self, match_id: str, strategy_name: str) -> bool:
        return any(p.match_id == match_id and p.strategy_name == strategy_name for p in self.open_positions.values())

    async def _open_position(self, state: MatchState, signal_value: StrategySignal) -> None:
        latest = state.odds_history[-1]
        player = state.player_a if signal_value.side == "A" else state.player_b
        odds_value = latest.back_odds_a if signal_value.side == "A" else latest.back_odds_b
        if odds_value <= 1.01:
            return
        confidence_fraction = Decimal(str(clamp(signal_value.confidence / 100, 0.1, 1.0)))
        stake = round_money(min(self.config.max_stake, self.bankroll * Decimal("0.01") * confidence_fraction))
        allowed, reason = self.risk.can_open(stake, self.exposure(), len(self.open_positions))
        if not allowed:
            self.logger.info("paper trade rejected %s", reason, extra={"event": "trade_rejected", "match_id": state.match_id, "strategy": signal_value.strategy_name})
            return
        trade_id = stable_id([state.match_id, signal_value.strategy_name, signal_value.side, iso_now(), str(random.random())])
        odds = Decimal(str(odds_value))
        profit_a, profit_b = self._book_for_back(signal_value.side, odds, stake)
        position = Position(
            trade_id=trade_id,
            match_id=state.match_id,
            strategy_name=signal_value.strategy_name,
            side=signal_value.side,
            action="BACK",
            player=player,
            odds=odds,
            stake=stake,
            opened_at=iso_now(),
            profit_a=profit_a,
            profit_b=profit_b,
        )
        self.open_positions[trade_id] = position
        await self.db.upsert_trade(position)
        self.logger.info("paper trade opened", extra={"event": "trade_open", "match_id": state.match_id, "strategy": signal_value.strategy_name, "trade_id": trade_id})

    async def _close_positions_on_exit(self, state: MatchState) -> None:
        latest = state.odds_history[-1] if state.odds_history else None
        if not latest:
            return
        positions = [p for p in self.open_positions.values() if p.match_id == state.match_id]
        for position in positions:
            signal_value = state.strategy_signals.get(position.strategy_name)
            adverse = self._adverse_move(position, latest)
            profitable = self._profitable_move(position, latest)
            should_close = bool(signal_value and signal_value.exit_signal) or adverse or profitable
            if should_close:
                await self._hedge_close(position, latest)

    def _adverse_move(self, position: Position, latest: MatchSnapshot) -> bool:
        current = Decimal(str(latest.back_odds_a if position.side == "A" else latest.back_odds_b or 0))
        return current > Decimal("1.18") * position.odds if current > 0 else False

    def _profitable_move(self, position: Position, latest: MatchSnapshot) -> bool:
        current = Decimal(str(latest.lay_odds_a if position.side == "A" else latest.lay_odds_b or 0))
        return current > 0 and current < Decimal("0.92") * position.odds

    async def _hedge_close(self, position: Position, latest: MatchSnapshot) -> None:
        hedge_odds = Decimal(str(latest.lay_odds_a if position.side == "A" else latest.lay_odds_b or 0))
        if hedge_odds <= Decimal("1.01"):
            hedge_odds = position.odds
        hedge_stake = round_money(position.stake * position.odds / hedge_odds)
        pnl = round_money(hedge_stake - position.stake)
        position.status = "CLOSED"
        position.closed_at = iso_now()
        position.hedge_odds = hedge_odds
        position.realized_pnl = pnl
        position.profit_a = pnl
        position.profit_b = pnl
        self.bankroll = round_money(self.bankroll + pnl)
        self.risk.record_pnl(pnl)
        self.closed_positions[position.trade_id] = position
        del self.open_positions[position.trade_id]
        await self.db.upsert_trade(position)
        self.logger.info("paper trade hedged closed", extra={"event": "trade_close", "match_id": position.match_id, "strategy": position.strategy_name, "trade_id": position.trade_id})

    def _book_for_back(self, side: str, odds: Decimal, stake: Decimal) -> Tuple[Decimal, Decimal]:
        win_profit = round_money((odds - Decimal("1")) * stake)
        lose_profit = -stake
        return (win_profit, lose_profit) if side == "A" else (lose_profit, win_profit)

    def metrics(self, start: datetime, end: datetime) -> Dict[str, Any]:
        positions = [p for p in self.closed_positions.values() if start.isoformat() <= p.closed_at <= end.isoformat()]
        pnl_values = [p.realized_pnl for p in positions]
        wins = [p for p in positions if p.realized_pnl > 0]
        losses = [p for p in positions if p.realized_pnl < 0]
        gross_profit = sum((p.realized_pnl for p in wins), Decimal("0"))
        gross_loss = abs(sum((p.realized_pnl for p in losses), Decimal("0")))
        net = sum(pnl_values, Decimal("0"))
        profit_factor = float(gross_profit / gross_loss) if gross_loss > 0 else float(gross_profit) if gross_profit > 0 else 0.0
        roi = float((net / self.config.initial_bankroll) * Decimal("100")) if self.config.initial_bankroll > 0 else 0.0
        avg_profit = gross_profit / len(wins) if wins else Decimal("0")
        avg_loss = gross_loss / len(losses) if losses else Decimal("0")
        drawdown = self._max_drawdown(pnl_values)
        return {
            "trades_executed": len(positions),
            "green_ups": len([p for p in positions if p.profit_a == p.profit_b and p.realized_pnl > 0]),
            "win_rate": (len(wins) / len(positions) * 100) if positions else 0.0,
            "profit_factor": profit_factor,
            "roi": roi,
            "average_profit": str(round_money(avg_profit)),
            "average_loss": str(round_money(avg_loss)),
            "maximum_drawdown": str(drawdown),
            "net_pnl": str(round_money(net)),
        }

    def _max_drawdown(self, pnl_values: List[Decimal]) -> Decimal:
        peak = Decimal("0")
        equity = Decimal("0")
        max_dd = Decimal("0")
        for pnl in pnl_values:
            equity += pnl
            peak = max(peak, equity)
            max_dd = min(max_dd, equity - peak)
        return round_money(abs(max_dd))


class MatchExtractor:
    def __init__(self, selectors: SelectorSet, logger: logging.Logger):
        self.selectors = selectors
        self.logger = logger

    async def extract(self, page: Page) -> List[MatchSnapshot]:
        script = r"""
        (selectors) => {
            const clean = (value) => (value || '').replace(/\u00a0/g, ' ').replace(/\s+/g, ' ').trim();
            const oddsNumber = (value) => {
                const match = clean(value).match(/\b\d{1,2}\.\d{1,2}\b/);
                return match ? Number(match[0]) : 0;
            };
            const nodes = Array.from(document.querySelectorAll(selectors.match));
            const candidates = nodes.length ? nodes : Array.from(document.querySelectorAll('article, section, li, tr, div')).filter((node) => /tennis|set|game|\b15\b|\b30\b|\b40\b/i.test(node.innerText || ''));
            return candidates.slice(0, 80).map((node, index) => {
                const text = clean(node.innerText);
                const attrs = ['data-event-id', 'data-match-id', 'id'].map((name) => node.getAttribute(name)).filter(Boolean);
                const oddsNodes = Array.from(node.querySelectorAll(selectors.odds || 'button, span, div'));
                const odds = oddsNodes.map((n) => oddsNumber(n.innerText)).filter((value) => value > 1.01 && value < 100);
                const statusNode = selectors.market_status ? node.querySelector(selectors.market_status) : null;
                const scoreNode = selectors.score ? node.querySelector(selectors.score) : null;
                const liquidityMatch = text.match(/(?:£|\$|€)\s?([\d,]+(?:\.\d+)?)/);
                return {
                    index,
                    id: attrs[0] || '',
                    text,
                    status: clean(statusNode ? statusNode.innerText : ''),
                    score: clean(scoreNode ? scoreNode.innerText : ''),
                    odds,
                    liquidity: liquidityMatch ? Number(liquidityMatch[1].replace(/,/g, '')) : odds.length * 1000
                };
            }).filter((item) => item.text.length > 10 || item.odds.length >= 2);
        }
        """
        raw_items = await page.evaluate(script, dataclasses.asdict(self.selectors))
        snapshots: List[MatchSnapshot] = []
        for item in raw_items:
            snapshot = self._normalize_item(item)
            if snapshot and self._is_live_tennis(snapshot):
                snapshots.append(snapshot)
        snapshots.sort(key=lambda item: item.liquidity, reverse=True)
        return snapshots[: max(MIN_CONCURRENT_MATCH_CAPACITY, len(snapshots))]

    def _normalize_item(self, item: Dict[str, Any]) -> Optional[MatchSnapshot]:
        text = normalize_text(item.get("text", ""))
        lowered = text.lower()
        if not text:
            return None
        status = normalize_text(item.get("status") or ("Live" if "live" in lowered or "in-play" in lowered else "Live"))
        players = self._extract_players(text)
        if len(players) < 2:
            return None
        score_text = normalize_text(item.get("score") or text)
        set_score, game_score, point_score = parse_score_text(score_text)
        odds = [float(value) for value in item.get("odds", []) if float(value) > 1.01]
        while len(odds) < 4:
            odds.append(0.0)
        tournament = self._extract_tournament(text, players)
        match_id = normalize_text(item.get("id")) or stable_id([tournament, players[0], players[1]])
        return MatchSnapshot(
            match_id=match_id,
            tournament=tournament,
            player_a=players[0],
            player_b=players[1],
            status=status,
            set_score=set_score,
            game_score=game_score,
            point_score=point_score,
            back_odds_a=odds[0],
            lay_odds_a=odds[1],
            back_odds_b=odds[2],
            lay_odds_b=odds[3],
            liquidity=float(item.get("liquidity") or 0),
            timestamp=iso_now(),
        )

    def _extract_players(self, text: str) -> List[str]:
        separators = [" v ", " vs ", " - ", "\n"]
        compact = text.replace("\r", "\n")
        lines = [normalize_text(line) for line in compact.split("\n") if normalize_text(line)]
        names: List[str] = []
        for line in lines[:8]:
            low = line.lower()
            if any(word in low for word in ["tennis", "live", "set", "game", "odds", "back", "lay"]):
                continue
            if safe_float(line, -999) != -999:
                continue
            if 2 <= len(line) <= 60:
                names.append(line)
        if len(names) >= 2:
            return names[:2]
        for separator in separators:
            if separator in f" {text.lower()} ":
                parts = [normalize_text(part) for part in text.split(separator.strip())]
                if len(parts) >= 2:
                    return [parts[0][:60], parts[1][:60]]
        capitalized = []
        for token in text.split():
            if token[:1].isupper() and not any(ch.isdigit() for ch in token):
                capitalized.append(token.strip(" ,.;"))
        if len(capitalized) >= 4:
            return [" ".join(capitalized[:2]), " ".join(capitalized[2:4])]
        return []

    def _extract_tournament(self, text: str, players: List[str]) -> str:
        first_line = normalize_text(text.split("\n")[0])
        if first_line and all(player not in first_line for player in players):
            return first_line[:120]
        return "Live Tennis"

    def _is_live_tennis(self, snapshot: MatchSnapshot) -> bool:
        status = snapshot.status.lower()
        if any(blocked in status for blocked in IGNORED_STATUSES):
            return False
        combined = f"{snapshot.tournament} {snapshot.status} {snapshot.set_score} {snapshot.game_score} {snapshot.point_score}".lower()
        return "tennis" in combined or "live" in combined or bool(snapshot.set_score or snapshot.game_score or snapshot.point_score)


class MonitoringEngine:
    def __init__(
        self,
        browser_engine: BrowserEngine,
        discovery_engine: DiscoveryEngine,
        db: Database,
        strategy_engine: StrategyEngine,
        ranking_engine: RankingEngine,
        trading_engine: PaperTradingEngine,
        notifier: TelegramNotifier,
        logger: logging.Logger,
        config: Config,
    ):
        self.browser_engine = browser_engine
        self.discovery_engine = discovery_engine
        self.db = db
        self.strategy_engine = strategy_engine
        self.ranking_engine = ranking_engine
        self.trading_engine = trading_engine
        self.notifier = notifier
        self.logger = logger
        self.config = config
        self.states: Dict[str, MatchState] = {}
        self.running = False
        self.matches_scanned = 0
        self.matches_qualified = 0
        self.started_at = utc_now()

    async def start(self) -> None:
        self.running = True
        while self.running:
            cycle_started = time.monotonic()
            try:
                await self._scan_cycle()
            except PlaywrightError as exc:
                await self._handle_recoverable("browser", exc)
            except requests.RequestException as exc:
                await self._handle_recoverable("internet", exc)
            except sqlite3.OperationalError as exc:
                await self._handle_recoverable("database", exc)
            except Exception as exc:
                await self._handle_recoverable("monitoring", exc)
            elapsed = time.monotonic() - cycle_started
            await asyncio.sleep(max(0.5, self.config.scan_interval_seconds - elapsed))

    async def stop(self) -> None:
        self.running = False
        await self._save_state()

    async def _scan_cycle(self) -> None:
        if not await self.browser_engine.ensure_session():
            return
        page = self.browser_engine.require_page()
        extractor = MatchExtractor(self.discovery_engine.selectors, self.logger)
        snapshots = await extractor.extract(page)
        if not snapshots:
            await self.browser_engine.capture_artifacts("no_live_matches")
            self.discovery_engine.selectors = await self.discovery_engine.discover()
            return
        self.matches_scanned += len(snapshots)
        tasks = [self._process_snapshot(snapshot) for snapshot in snapshots]
        await asyncio.gather(*tasks)
        ranked = sorted(self.states.values(), key=lambda state: state.opportunity_score, reverse=True)
        self.matches_qualified += len([state for state in ranked if state.opportunity_score >= 50])
        self.logger.info("scan complete matches=%s top=%s", len(snapshots), [(s.match_id, round(s.opportunity_score, 2)) for s in ranked[:5]], extra={"event": "scan_complete"})

    async def _process_snapshot(self, snapshot: MatchSnapshot) -> None:
        state = self.states.get(snapshot.match_id)
        if not state:
            state = MatchState(match_id=snapshot.match_id)
            self.states[snapshot.match_id] = state
        state.tournament = snapshot.tournament
        state.player_a = snapshot.player_a
        state.player_b = snapshot.player_b
        state.status = snapshot.status
        state.last_seen = snapshot.timestamp
        state.odds_history.append(snapshot)
        state.score_history.append((snapshot.timestamp, snapshot.set_score, snapshot.game_score, snapshot.point_score))
        preliminary_signals = self.strategy_engine.evaluate(state)
        state.strategy_signals = {sig.strategy_name: sig for sig in preliminary_signals}
        self.ranking_engine.rank(state)
        signals = self.strategy_engine.evaluate(state)
        state.strategy_signals = {sig.strategy_name: sig for sig in signals}
        self.ranking_engine.rank(state)
        await self.db.upsert_match(snapshot, state.opportunity_score)
        await self.db.insert_score(snapshot)
        await self.db.insert_odds(snapshot)
        await asyncio.gather(*(self.db.insert_strategy(snapshot.match_id, sig, state.opportunity_score) for sig in signals))
        await self.trading_engine.evaluate(state)
        self.logger.info("match updated", extra={"event": "match_update", "match_id": snapshot.match_id})

    async def _handle_recoverable(self, subsystem: str, exc: BaseException) -> None:
        self.logger.exception("recoverable subsystem failure %s", subsystem, extra={"event": "recovery", "match_id": subsystem})
        await self.db.insert_error(subsystem, exc)
        await self.db.insert_alert(f"{subsystem}_failure", str(exc))
        await self.notifier.send(f"{subsystem.title()} failure", f"{exc}\nRecovery engine restarting affected subsystem")
        if subsystem in {"browser", "internet", "monitoring"}:
            await asyncio.sleep(5)
            await self.browser_engine.reconnect()
        if subsystem == "database":
            await asyncio.sleep(2)

    async def _save_state(self) -> None:
        payload = {
            "saved_at": iso_now(),
            "matches": {
                match_id: {
                    "tournament": state.tournament,
                    "player_a": state.player_a,
                    "player_b": state.player_b,
                    "status": state.status,
                    "opportunity_score": state.opportunity_score,
                    "last_seen": state.last_seen,
                }
                for match_id, state in self.states.items()
            },
            "open_positions": {trade_id: dataclasses.asdict(position) for trade_id, position in self.trading_engine.open_positions.items()},
        }
        STATE_PATH.write_text(json.dumps(payload, default=str, indent=2), encoding="utf-8")


class ReportEngine:
    def __init__(self, db: Database, monitoring: MonitoringEngine, trading: PaperTradingEngine, notifier: TelegramNotifier, logger: logging.Logger):
        self.db = db
        self.monitoring = monitoring
        self.trading = trading
        self.notifier = notifier
        self.logger = logger
        REPORT_DIR.mkdir(exist_ok=True)

    async def daily(self) -> None:
        today = utc_now().date()
        start = datetime.combine(today, datetime.min.time(), tzinfo=timezone.utc)
        end = start + timedelta(days=1)
        await self.generate("daily", start, end)
        self.trading.risk.reset_daily()

    async def weekly(self) -> None:
        now = utc_now()
        start = datetime.combine((now - timedelta(days=now.weekday())).date(), datetime.min.time(), tzinfo=timezone.utc)
        end = start + timedelta(days=7)
        await self.generate("weekly", start, end)

    async def monthly(self) -> None:
        now = utc_now()
        start = datetime(now.year, now.month, 1, tzinfo=timezone.utc)
        next_month = datetime(now.year + (1 if now.month == 12 else 0), 1 if now.month == 12 else now.month + 1, 1, tzinfo=timezone.utc)
        await self.generate("monthly", start, next_month)

    async def generate(self, period: str, start: datetime, end: datetime) -> str:
        metrics = self.trading.metrics(start, end)
        body = json.dumps(
            {
                "period": period,
                "period_start": start.isoformat(),
                "period_end": end.isoformat(),
                "matches_scanned": self.monitoring.matches_scanned,
                "matches_qualified": self.monitoring.matches_qualified,
                **metrics,
            },
            indent=2,
        )
        path = REPORT_DIR / f"{APP_NAME.lower()}_{period}_{start.date().isoformat()}.json"
        path.write_text(body, encoding="utf-8")
        await self.db.insert_report(period, start.isoformat(), end.isoformat(), body)
        await self.notifier.send(f"{period.title()} report", body)
        self.logger.info("report generated %s", path, extra={"event": "report_generated"})
        return body


class HealthMonitor:
    def __init__(self, monitoring: MonitoringEngine, trading: PaperTradingEngine, db: Database, notifier: TelegramNotifier, logger: logging.Logger):
        self.monitoring = monitoring
        self.trading = trading
        self.db = db
        self.notifier = notifier
        self.logger = logger
        self.started_at = utc_now()

    async def send_health(self) -> None:
        uptime = utc_now() - self.started_at
        db_status = "ok"
        try:
            await self.db.query("SELECT 1")
        except Exception as exc:
            db_status = f"error: {exc}"
        message = "\n".join(
            [
                "Status: running",
                f"Uptime: {uptime}",
                f"Matches tracked: {len(self.monitoring.states)}",
                f"Paper trades executed: {len(self.trading.closed_positions) + len(self.trading.open_positions)}",
                f"Open exposure: {self.trading.exposure()}",
                f"Database status: {db_status}",
            ]
        )
        await self.notifier.send("Health", message)
        self.logger.info("health sent", extra={"event": "health"})


class BetacularAI:
    def __init__(self) -> None:
        self.config = Config.load()
        self.db = Database(DB_PATH, LOGGER)
        self.notifier = TelegramNotifier(self.config, LOGGER)
        self.browser_engine = BrowserEngine(self.config, self.notifier, self.db, LOGGER)
        self.discovery_engine = DiscoveryEngine(self.browser_engine, LOGGER)
        self.strategy_engine = StrategyEngine()
        self.ranking_engine = RankingEngine()
        self.risk_engine = RiskEngine(self.config, LOGGER)
        self.trading_engine = PaperTradingEngine(self.config, self.db, self.risk_engine, LOGGER)
        self.monitoring_engine = MonitoringEngine(
            self.browser_engine,
            self.discovery_engine,
            self.db,
            self.strategy_engine,
            self.ranking_engine,
            self.trading_engine,
            self.notifier,
            LOGGER,
            self.config,
        )
        self.report_engine = ReportEngine(self.db, self.monitoring_engine, self.trading_engine, self.notifier, LOGGER)
        self.health_monitor = HealthMonitor(self.monitoring_engine, self.trading_engine, self.db, self.notifier, LOGGER)
        self.scheduler = AsyncIOScheduler(timezone="UTC")
        self.shutdown_event = asyncio.Event()

    async def startup(self) -> None:
        SCREENSHOT_DIR.mkdir(exist_ok=True)
        SNAPSHOT_DIR.mkdir(parents=True, exist_ok=True)
        REPORT_DIR.mkdir(exist_ok=True)
        await self.db.initialize()
        await self.browser_engine.start()
        await self.browser_engine.login()
        self.discovery_engine.selectors = await self.discovery_engine.discover()
        self._configure_scheduler()
        self.scheduler.start()
        await self.notifier.send("Startup", "BETACULAR_AI started in paper-trading mode")
        LOGGER.info("startup complete", extra={"event": "startup"})

    def _configure_scheduler(self) -> None:
        self.scheduler.add_job(self.health_monitor.send_health, "interval", minutes=HEALTH_INTERVAL_MINUTES, id="health", replace_existing=True)
        self.scheduler.add_job(self.report_engine.daily, "cron", hour=23, minute=59, id="daily_report", replace_existing=True)
        self.scheduler.add_job(self.report_engine.weekly, "cron", day_of_week="sun", hour=23, minute=58, id="weekly_report", replace_existing=True)
        self.scheduler.add_job(self.report_engine.monthly, "cron", day="last", hour=23, minute=57, id="monthly_report", replace_existing=True)

    async def run(self) -> None:
        loop = asyncio.get_running_loop()
        for sig in (signal.SIGINT, signal.SIGTERM):
            with contextlib.suppress(NotImplementedError):
                loop.add_signal_handler(sig, self.shutdown_event.set)
        await self.startup()
        monitor_task = asyncio.create_task(self.monitoring_engine.start())
        shutdown_task = asyncio.create_task(self.shutdown_event.wait())
        done, pending = await asyncio.wait({monitor_task, shutdown_task}, return_when=asyncio.FIRST_COMPLETED)
        for task in pending:
            task.cancel()
        for task in done:
            if task is monitor_task and task.exception():
                raise task.exception()
        await self.shutdown()

    async def shutdown(self) -> None:
        LOGGER.info("shutdown started", extra={"event": "shutdown"})
        await self.monitoring_engine.stop()
        if self.scheduler.running:
            self.scheduler.shutdown(wait=False)
        await self.browser_engine.stop()
        await self.db.close()
        LOGGER.info("shutdown complete", extra={"event": "shutdown"})


async def main() -> None:
    app = BetacularAI()
    try:
        await app.run()
    except Exception as exc:
        LOGGER.exception("fatal exception", extra={"event": "fatal_exception"})
        with contextlib.suppress(Exception):
            await app.db.insert_error("fatal", exc)
        with contextlib.suppress(Exception):
            await app.notifier.send("Fatal exception", str(exc))
        with contextlib.suppress(Exception):
            await app.shutdown()
        raise


if __name__ == "__main__":
    asyncio.run(main())
