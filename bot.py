#██      ██    ██████    ██████████  ██      ██  ██      ██    ██████    
#██      ██    ██████    ██████████  ██      ██  ██      ██    ██████    
#██    ██    ██      ██        ██    ██      ██    ██  ██    ██      ██  
#██    ██    ██      ██        ██    ██      ██    ██  ██    ██      ██  
#██████      ██████████      ██      ██      ██      ██      ██████████  
#██████      ██████████      ██      ██      ██      ██      ██████████  
#██    ██    ██      ██    ██        ██      ██      ██      ██      ██  
#██    ██    ██      ██    ██        ██      ██      ██      ██      ██  
#██      ██  ██      ██  ██████████    ██████        ██      ██      ██  
#██      ██  ██      ██  ██████████    ██████        ██      ██      ██  

import warnings
import sys
import random
from collections import deque
import threading
import queue
warnings.filterwarnings("ignore", category=Warning)

import time
import uuid
from datetime import datetime, timedelta
from decimal import Decimal
import urllib.request
import json
import pytz
import base64
import kalshi_python
from kalshi_python.models.create_order_request import CreateOrderRequest

try:
    import matplotlib
    matplotlib.use("Agg")  # headless - no display server on a trading VPS
    import matplotlib.pyplot as plt
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import padding
from cryptography.hazmat.primitives.serialization import load_pem_private_key

# --- YOUR API CREDENTIALS ---
KEY_ID = ""

console_log_buffer = deque(maxlen=300)
console_log_lock = threading.Lock()

class _TeeStdout:
    def __init__(self, original):
        self.original = original
        self._line_buffer = ""

    def write(self, text):
        self.original.write(text)
        with console_log_lock:
            self._line_buffer += text
            while "\n" in self._line_buffer:
                line, self._line_buffer = self._line_buffer.split("\n", 1)
                if line.strip():
                    console_log_buffer.append(line)

    def flush(self):
        self.original.flush()

sys.stdout = _TeeStdout(sys.stdout)
# -------------------------------------------

PRIVATE_KEY_PATH = "private_key.pem"

# u set DEMO_MODE = True for Kalshi Sandbox; set False to trade live
DEMO_MODE = False 
BUDGET_DOLLARS = 4 # set to 35.99 on the day, 15 at night
# --- AUTOSELL CONFIG ---
# when its true, any open position that reaches PROFIT_TARGET_DOLLARS or more in
# profit (total, not per-contract) will get sold
AUTOSELLING = True
PROFIT_TARGET_DOLLARS = .30 # set to $1.10 on the day, .45 at night

# For LARGE positions only, use a trailing stop instead of the fixed
# PROFIT_TARGET_DOLLARS above: once profit reaches the arm level, track the
# best profit seen and sell if it pulls back by the trail amount, rather than
# selling flat the instant the target is first touched. Small positions are
# unaffected and keep the exact fixed-target behavior above.
TRAILING_STOP_ENABLED = True
TRAILING_STOP_MIN_CONTRACTS = 20  # only positions with MORE than this many contracts use the trailing stop; count is checked live, so a position that grows past this via a multi-share/secondary add picks it up automatically
TRAILING_STOP_ARM_DOLLARS = 0.30  # unrealized profit at which trailing takes over (starts equal to PROFIT_TARGET_DOLLARS's current default; tune independently)
TRAILING_STOP_TRAIL_DOLLARS = 0.10  # how far profit can fall back from its peak before selling - untested starting guess, tune against logged data
# when its, any open position that reaches STOP_LOSS_DOLLARS or more in
# losses (total) will be automatically sold to
# cut downsides instead of holding forver.
STOP_LOSS_ENABLED = True
STOP_LOSS_DOLLARS = 4 # set to $20.00 on the day, 5 at night

# How often the dedicated position-monitoring thread checks open positions for
# stop-loss/take-profit, independent of the slower main scan loop (which only
# looks for new buy opportunities). Lower = faster loss detection but its more API calls.
POSITION_CHECK_INTERVAL_SECONDS = 0.1

# Late in a market's life, a single large order (a "whale") can spike the
# quoted price hard against a held position and hold it there for a while
# before reverting - not necessarily a genuine reversal. Below this much time
# remaining, require the stop-loss condition to hold for a sustained duration
# before actually selling, so a temporary spike doesn't stop out a trade that
# recovers. Check count is derived from the duration so it stays correct if
# POSITION_CHECK_INTERVAL_SECONDS ever changes.
STOP_LOSS_CONFIRMATION_TIME_THRESHOLD_MINUTES = 2
STOP_LOSS_CONFIRMATION_SECONDS = 3

# Session-level circuit breaker: once cumulative REALIZED losses for this run
# hit this amount, stop opening any NEW positions (including secondary adds)
# for the rest of the session. Already-open positions still get managed
# normally to their own take-profit/stop-loss - this only blocks new risk.
# This is the one guard that caps how bad an entire unattended session can
# get, independent of which specific trade pattern causes the next loss.
DAILY_LOSS_LIMIT_ENABLED = True
DAILY_LOSS_LIMIT_DOLLARS = 3 # set to 15 on the day, 6 at night
# ------------------------

# --- TRIGGER THRESHOLDS (editable live via Telegram: /setthreshold, /setmultishare) ---
STANDARD_MAX_MINUTES = 2
HARD_ABSOLUTE_MAX_MINUTES = 3
EARLY_SPIKE_PRICE_CENTS = 97  # set to 97 on the day, 98 at night
NORMAL_TRIGGER_PRICE_CENTS = 96 # set to 96.5 on the day, 97 at night
MULTI_SHARE_THRESHOLD = 98
SECONDARY_TIME_LIMIT = 2
SECONDARY_PRICE_CENTS = 98
VELOCITY_FILTER_ENABLED = True
MAX_PRICE_JUMP_CENTS = 12  # skip a buy if the ask jumped more than this many cents since the last check - a violent single-tick move (crash/spike) is more likely to reverse than a steady trend
MULTI_SHARE_CONTRACT_COUNT = 3  # contracts bought on a multi-share trigger (both yes and no) # set to 40 on the day, 20 at night
# ----------------------------------------------------------------------------------

# --- LIQUIDITY FILTERS ---
# Two separate guards against bad fills / bad signal:
#  - book depth: how many contracts sit at the exact price level you'd be
#    matching against right now (skips a single trigger if the book is thin)
#  - market volume: total contracts traded in this market so far (skips the
#    WHOLE market this cycle if it's too illiquid to trust the quoted price)
LIQUIDITY_FILTER_ENABLED = True
MIN_BOOK_DEPTH_CONTRACTS = 10  # skip a buy trigger if fewer than this many contracts are resting at the top-of-book price you'd fill against
MIN_MARKET_VOLUME_CONTRACTS = 500  # skip a market entirely if its total traded volume is below this
VOLUME_CACHE_TTL_SECONDS = 15  # how often to re-fetch a market's volume (avoids an extra API call every 0.5s loop cycle)
# --------------------------

EDITABLE_THRESHOLDS = {
    # short aliases (use these day-to-day)
    "smm": "STANDARD_MAX_MINUTES",
    "ham": "HARD_ABSOLUTE_MAX_MINUTES",
    "esp": "EARLY_SPIKE_PRICE_CENTS",
    "ntp": "NORMAL_TRIGGER_PRICE_CENTS",
    "mst": "MULTI_SHARE_THRESHOLD",
    "stl": "SECONDARY_TIME_LIMIT",
    "spc": "SECONDARY_PRICE_CENTS",
    "vfe": "VELOCITY_FILTER_ENABLED",
    "mpj": "MAX_PRICE_JUMP_CENTS",
    "lfe": "LIQUIDITY_FILTER_ENABLED",
    "mbd": "MIN_BOOK_DEPTH_CONTRACTS",
    "mvc": "MIN_MARKET_VOLUME_CONTRACTS",
    "tse": "TRAILING_STOP_ENABLED",
    "tsm": "TRAILING_STOP_MIN_CONTRACTS",
    "tsa": "TRAILING_STOP_ARM_DOLLARS",
    "tst": "TRAILING_STOP_TRAIL_DOLLARS",
    "scs": "STOP_LOSS_CONFIRMATION_SECONDS",
    # full names still work too
    "standard_max_minutes": "STANDARD_MAX_MINUTES",
    "hard_absolute_max_minutes": "HARD_ABSOLUTE_MAX_MINUTES",
    "early_spike_price_cents": "EARLY_SPIKE_PRICE_CENTS",
    "normal_trigger_price_cents": "NORMAL_TRIGGER_PRICE_CENTS",
    "multi_share_threshold": "MULTI_SHARE_THRESHOLD",
    "secondary_time_limit": "SECONDARY_TIME_LIMIT",
    "secondary_price_cents": "SECONDARY_PRICE_CENTS",
    "velocity_filter_enabled": "VELOCITY_FILTER_ENABLED",
    "max_price_jump_cents": "MAX_PRICE_JUMP_CENTS",
    "liquidity_filter_enabled": "LIQUIDITY_FILTER_ENABLED",
    "min_book_depth_contracts": "MIN_BOOK_DEPTH_CONTRACTS",
    "min_market_volume_contracts": "MIN_MARKET_VOLUME_CONTRACTS",
    "trailing_stop_enabled": "TRAILING_STOP_ENABLED",
    "trailing_stop_min_contracts": "TRAILING_STOP_MIN_CONTRACTS",
    "trailing_stop_arm_dollars": "TRAILING_STOP_ARM_DOLLARS",
    "trailing_stop_trail_dollars": "TRAILING_STOP_TRAIL_DOLLARS",
    "stop_loss_confirmation_seconds": "STOP_LOSS_CONFIRMATION_SECONDS",
}
THRESHOLD_SHORT_NAMES = ["smm", "ham", "esp", "ntp", "mst", "stl", "spc", "vfe", "mpj", "lfe", "mbd", "mvc", "tse", "tsm", "tsa", "tst", "scs"]

# --- NIGHT MODE ---
# Pulled directly from the "# set to X on the day, Y at night" comments
# already in this file. /nightmode on|off swaps all seven at once.
DAY_NIGHT_VALUES = {
    "BUDGET_DOLLARS": {"day": 35.99, "night": 15},
    "PROFIT_TARGET_DOLLARS": {"day": 1.10, "night": 0.45},
    "STOP_LOSS_DOLLARS": {"day": 20.00, "night": 5},
    "DAILY_LOSS_LIMIT_DOLLARS": {"day": 15, "night": 6},
    "EARLY_SPIKE_PRICE_CENTS": {"day": 97, "night": 98},
    "NORMAL_TRIGGER_PRICE_CENTS": {"day": 96.5, "night": 97},
    "MULTI_SHARE_CONTRACT_COUNT": {"day": 40, "night": 20},
}
night_mode_active = False
# ------------------


HOST = "https://external-api.demo.kalshi.co/trade-api/v2" if DEMO_MODE else "https://external-api.kalshi.com/trade-api/v2"
traded_tickers = set()

# --- LATENCY: avoid redundant per-cycle API calls ---
# The active market only actually changes once every ~15 minutes, and a
# market's close_time never changes once the market exists - but the old
# main loop re-resolved both on EVERY single 0.5s cycle, and check_market_and_trade
# separately re-fetched close_time again every cycle too. That's 3 wasted
# round-trips per cycle, on top of the orderbook fetch that's actually needed
# every time. Caching these means more cycles land on "just fetch the
# orderbook and check the price" - the part that actually needs to be fast
# when a threshold is about to cross.
_active_market_cache = {"ticker": None, "close_time": None}
_market_close_time_cache = {}  # ticker -> close_time (UTC datetime), cached forever per ticker
_market_volume_cache = {}  # ticker -> (volume, fetched_at_epoch_seconds) - short TTL since volume changes, unlike close_time
# -----------------------------------------------------

secondary_traded_sides = {}  # ticker -> set of sides ("yes"/"no") already used for a secondary buy - tracked per side so a reversal can still trigger the OTHER side's secondary shot
stop_loss_breach_started = {}  # ticker -> epoch seconds when the loss first crossed -STOP_LOSS_DOLLARS, used for a wall-clock (not check-count) confirmation window
last_known_bid = {}  # ticker -> (bid_cents, epoch seconds) for the most recent VALID bid seen, used for a defensive exit attempt if the book goes empty mid-confirmation
trailing_stop_peak = {}  # ticker -> highest unrealized profit dollars seen since the trailing stop armed (large positions only, see TRAILING_STOP_MIN_CONTRACTS)
_pending_settlement_last_check = {}  # ticker -> epoch seconds we last polled a CLOSED market whose settlement result hasn't posted yet, so we retry instead of giving up (see check_autosell)
_pending_settlement_first_seen = {}  # ticker -> epoch seconds we first saw it closed-but-unsettled, so we can give up after MAX_SETTLEMENT_WAIT_MINUTES rather than retry forever
PENDING_SETTLEMENT_RECHECK_SECONDS = 2  # how often to re-poll a closed-but-unsettled market (avoids hammering /markets/{ticker} every 0.1s while waiting)
MAX_SETTLEMENT_WAIT_MINUTES = 15  # if Kalshi still hasn't posted a result after this long, stop retrying and fall back to the old "not tracked" warning rather than leaking memory forever
price_history = {}  # market_ticker -> {"yes_ask": int, "no_ask": int} from the previous check, used to detect violent single-tick swings
open_positions = {}  # ticker -> {"side": "yes"/"no", "entry_price_cents": float, "count": int}
positions_lock = threading.Lock()  # guards open_positions since a background thread now checks it independently of the main loop
held_positions = set()  # tickers manually exempted (via /hold) from automatic stop-loss/take-profit - guarded by positions_lock

session_realized_pnl = 0.0  # cumulative realized $ P/L for this run - read by the main loop (buy side) and written by the monitor thread (sell/settlement side)
session_pnl_lock = threading.Lock()
session_start_balance = None  # captured once at startup - real account balance, used as the authoritative source for session P/L (session_realized_pnl misses trades whose settlement result isn't available yet - see get_session_pnl)

# --- TELEGRAM ALERTS: HOURLY / DAILY P/L SUMMARY ---
# Sends a message to your phone (via Telegram) with how much you've made in
# the last hour and the last day, so you can check in without opening logs.
#
TELEGRAM_BOT_TOKEN = "8812396237:AAHukS65VOniwzFiaReJF8an8EfqmRvv-08"   # your real full token
TELEGRAM_CHAT_ID = "5494748163"
ALERTS_ENABLED = True
SUMMARY_CHECK_INTERVAL_SECONDS = 60  # how often the summary thread checks whether an hour/day has elapsed
# ----------------------------------------------------

_hourly_checkpoint_pnl = 0.0
_hourly_checkpoint_time = time.time()
_daily_checkpoint_pnl = 0.0
_daily_checkpoint_time = time.time()

# --- TWO-WAY TELEGRAM CONTROL ---
# Text the bot from your phone: /status (open positions + P/L), /pause (stop
# opening new positions - open ones still get managed normally), /resume.
# /unlockloss overrides a tripped daily loss limit; /relock re-arms it.
TELEGRAM_COMMAND_POLL_INTERVAL_SECONDS = 3
trading_paused = False
_pause_until = None  # epoch seconds when a timed /pausefor ends; None = no timer (either running, or paused indefinitely via /pause)
_pause_lock = threading.Lock()
_loss_limit_alerted = False  # so the loss-limit push alert fires once per trip, not every scan cycle
loss_limit_overridden = False
_telegram_update_offset = 0
bot_start_time = time.time()  # used by /uptime
# ---------------------------------

# --- PERSISTENT ALL-TIME STATS (survives restarts) ---
STATS_FILE_PATH = "bot_stats.json"
stats_lock = threading.Lock()

def _load_stats():
    defaults = {
        "lifetime_pnl": 0.0,
        "total_trades": 0,
        "total_wins": 0,
        "longest_win_streak": 0,
        "current_streak_count": 0,
        "current_streak_type": None,
        "best_day": {"date": None, "pnl": None},
        "worst_day": {"date": None, "pnl": None},
        "today_date": None,
        "today_pnl": 0.0,
    }
    try:
        with open(STATS_FILE_PATH, "r") as f:
            loaded = json.load(f)
        defaults.update(loaded)
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        pass
    return defaults

all_time_stats = _load_stats()

def _save_stats():
    try:
        with open(STATS_FILE_PATH, "w") as f:
            json.dump(all_time_stats, f, indent=2)
    except Exception as e:
        print(f"--> [WARNING] Could not save stats file: {e}")

def _finalize_day_if_needed():
    """Rolls 'today's' running total into best/worst day once the calendar
    date actually changes. Must be called with stats_lock held."""
    today_str = datetime.now().strftime("%Y-%m-%d")
    if all_time_stats["today_date"] is None:
        all_time_stats["today_date"] = today_str
        return
    if all_time_stats["today_date"] != today_str:
        finished_pnl = all_time_stats["today_pnl"]
        finished_date = all_time_stats["today_date"]
        if all_time_stats["best_day"]["pnl"] is None or finished_pnl > all_time_stats["best_day"]["pnl"]:
            all_time_stats["best_day"] = {"date": finished_date, "pnl": finished_pnl}
        if all_time_stats["worst_day"]["pnl"] is None or finished_pnl < all_time_stats["worst_day"]["pnl"]:
            all_time_stats["worst_day"] = {"date": finished_date, "pnl": finished_pnl}
        all_time_stats["today_date"] = today_str
        all_time_stats["today_pnl"] = 0.0

def record_trade_stats(amount_dollars):
    """Updates lifetime win/loss/streak/best-day stats and persists to disk.
    Inherits the same limitation as session_realized_pnl - only counts trades
    that were actively sold or whose settlement result was found in time."""
    with stats_lock:
        _finalize_day_if_needed()
        all_time_stats["lifetime_pnl"] += amount_dollars
        all_time_stats["total_trades"] += 1
        all_time_stats["today_pnl"] += amount_dollars

        if amount_dollars > 0:
            all_time_stats["total_wins"] += 1
            if all_time_stats["current_streak_type"] == "win":
                all_time_stats["current_streak_count"] += 1
            else:
                all_time_stats["current_streak_type"] = "win"
                all_time_stats["current_streak_count"] = 1
            if all_time_stats["current_streak_count"] > all_time_stats["longest_win_streak"]:
                all_time_stats["longest_win_streak"] = all_time_stats["current_streak_count"]
        elif amount_dollars < 0:
            if all_time_stats["current_streak_type"] == "loss":
                all_time_stats["current_streak_count"] += 1
            else:
                all_time_stats["current_streak_type"] = "loss"
                all_time_stats["current_streak_count"] = 1

        _save_stats()
# -------------------------------------------------------

# --- PER-TRADE LOG (for /history and /wins) ---
TRADE_LOG_FILE = "bot_trade_log.json"
TRADE_LOG_MAX_ENTRIES = 1000  # /expectancy needs a decent sample; /history etc. still only show the latest 20
trade_log_lock = threading.Lock()

def _load_trade_log():
    try:
        with open(TRADE_LOG_FILE, "r") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return []

def _save_trade_log(log):
    try:
        with open(TRADE_LOG_FILE, "w") as f:
            json.dump(log, f, indent=2)
    except Exception as e:
        print(f"--> [WARNING] Could not save trade log: {e}")

def record_trade_log_entry(ticker, amount_dollars, reason):
    with trade_log_lock:
        log = _load_trade_log()
        log.append({
            "ticker": ticker,
            "amount": amount_dollars,
            "reason": reason,
            "timestamp": datetime.now().isoformat(),
        })
        log = log[-TRADE_LOG_MAX_ENTRIES:]
        _save_trade_log(log)
# ------------------------------------------------

# --- END-OF-DAY EQUITY CURVE CHART (sent as a Telegram photo) ---
EQUITY_CHART_PATH = "equity_curve_today.png"

def _build_equity_curve_chart(window_start_dt, out_path=EQUITY_CHART_PATH):
    """Builds a cumulative realized-P/L line chart from the trade log,
    covering trades since window_start_dt, saves it as a PNG, and returns
    the path. Returns None if matplotlib isn't installed or there's nothing
    to plot yet (rather than sending an empty/misleading chart)."""
    if not MATPLOTLIB_AVAILABLE:
        print("--> [WARNING] matplotlib isn't installed - skipping equity curve chart (pip install matplotlib).")
        return None

    log = _load_trade_log()
    todays_trades = []
    for entry in log:
        try:
            ts = datetime.fromisoformat(entry["timestamp"])
        except (ValueError, KeyError):
            continue
        if ts >= window_start_dt:
            todays_trades.append((ts, entry.get("amount", 0.0)))
    if not todays_trades:
        return None
    todays_trades.sort(key=lambda pair: pair[0])

    times = [window_start_dt] + [t for t, _ in todays_trades]
    cumulative = [0.0]
    running = 0.0
    for _, amt in todays_trades:
        running += amt
        cumulative.append(running)

    try:
        fig, ax = plt.subplots(figsize=(8, 4.5), dpi=150)
        line_color = "#2ecc71" if cumulative[-1] >= 0 else "#e74c3c"
        ax.plot(times, cumulative, color=line_color, linewidth=2)
        ax.axhline(0, color="#888888", linewidth=1, linestyle="--")
        ax.fill_between(times, cumulative, 0, color=line_color, alpha=0.15)
        ax.set_title(f"Equity Curve \u2013 {window_start_dt.strftime('%Y-%m-%d')}")
        ax.set_ylabel("Cumulative P/L ($)")
        ax.set_xlabel("Time")
        ax.grid(True, alpha=0.3)
        fig.autofmt_xdate()
        fig.tight_layout()
        fig.savefig(out_path)
        plt.close(fig)
        return out_path
    except Exception as e:
        print(f"--> [WARNING] Could not build equity curve chart: {e}")
        return None
# ------------------------------------------------------------

# --- STOP-LOSS POST-MORTEM (for /stops) ---
# Every stop-loss exit is saved along with what the market later SETTLED at,
# so /stops can answer the real question: would holding have been better?
STOPS_LOG_FILE = "bot_stops_log.json"
STOPS_LOG_MAX_ENTRIES = 500
stops_lock = threading.Lock()

def _load_stops_log():
    try:
        with open(STOPS_LOG_FILE, "r") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return []

def _save_stops_log(log):
    try:
        with open(STOPS_LOG_FILE, "w") as f:
            json.dump(log, f, indent=2)
    except Exception as e:
        print(f"--> [WARNING] Could not save stops log: {e}")

def record_stop_event(ticker, side, entry_cents, exit_cents, count, realized, minutes_left):
    with stops_lock:
        log = _load_stops_log()
        log.append({
            "ticker": ticker,
            "side": side,
            "entry_cents": entry_cents,
            "exit_cents": exit_cents,
            "count": count,
            "realized": realized,
            "minutes_left": minutes_left,
            "result": None,  # filled in later by _resolve_pending_stops()
            "timestamp": datetime.now().isoformat(),
        })
        _save_stops_log(log[-STOPS_LOG_MAX_ENTRIES:])

def _resolve_pending_stops(max_lookups=40):
    """Looks up the settlement result for any stop-outs that don't have one
    yet. Only runs when /stops is requested, so it costs nothing otherwise."""
    with stops_lock:
        log = _load_stops_log()
    pending = sorted({e["ticker"] for e in log if e.get("result") is None})[:max_lookups]
    found = {}
    for ticker in pending:
        is_closed, _, result = check_market_status(ticker)
        if is_closed and result in ("yes", "no", "void"):
            found[ticker] = result
    if found:
        with stops_lock:
            log = _load_stops_log()  # re-read so a stop that happened meanwhile isn't overwritten
            for e in log:
                if e.get("result") is None and e.get("ticker") in found:
                    e["result"] = found[e["ticker"]]
            _save_stops_log(log)

def _stop_if_held_pnl(e):
    """What this stopped-out slice would have made/lost if held to expiration."""
    if e["result"] == e["side"]:
        return (100 - e["entry_cents"]) * e["count"] / 100.0
    return -e["entry_cents"] * e["count"] / 100.0

def _summarize_stops(entries):
    """-> (count, would_have_won, net_effect_of_stopping). net > 0 means the
    stop-loss saved money vs holding; net < 0 means it cost money."""
    won = sum(1 for e in entries if e["result"] == e["side"])
    net = sum(e["realized"] - _stop_if_held_pnl(e) for e in entries)
    return len(entries), won, net

def _build_stops_message():
    _resolve_pending_stops()
    with stops_lock:
        log = _load_stops_log()
    if not log:
        return "No stop-loss exits recorded yet. Data starts building the next time a stop-loss fires."

    resolved = [e for e in log if e.get("result") in ("yes", "no")]
    pending = [e for e in log if e.get("result") is None]
    voided = [e for e in log if e.get("result") == "void"]

    lines = [f"\U0001F6D1 STOP-LOSS POST-MORTEM ({len(log)} stop-outs)"]
    if not resolved:
        lines.append(f"None have a settlement result yet ({len(pending)} pending). Check back after the markets close.")
        return "\n".join(lines)

    n, won, net = _summarize_stops(resolved)
    actual = sum(e["realized"] for e in resolved)
    held = sum(_stop_if_held_pnl(e) for e in resolved)
    lines.append(f"Would have WON if held: {won} of {n} ({won / n * 100:.0f}%)")
    lines.append(f"Would have LOST anyway: {n - won} of {n}")
    lines.append(f"Actual P/L from these exits: {_signed_money(actual)}")
    lines.append(f"If held to expiration instead: {_signed_money(held)}")
    if net > 0.005:
        lines.append(f"\u2705 Net: stop-loss SAVED you {_signed_money(net)}")
    elif net < -0.005:
        lines.append(f"\u26A0\uFE0F Net: stop-loss COST you {_signed_money(-net)} vs. just holding")
    else:
        lines.append("Net: about break-even vs. holding")

    late = [e for e in resolved if e.get("minutes_left") is not None
            and e["minutes_left"] < STOP_LOSS_CONFIRMATION_TIME_THRESHOLD_MINUTES]
    early = [e for e in resolved if e not in late]
    if late and early:
        ln, lw, lnet = _summarize_stops(late)
        en, ew, enet = _summarize_stops(early)
        lines.append("--- By timing ---")
        lines.append(f"Late (<{STOP_LOSS_CONFIRMATION_TIME_THRESHOLD_MINUTES}m left, confirmation window): "
                     f"{ln} stops, {lw} would've won, net {_signed_money(lnet)}")
        lines.append(f"Earlier: {en} stops, {ew} would've won, net {_signed_money(enet)}")

    lines.append("--- Most recent ---")
    for e in reversed(log[-5:]):
        try:
            t = datetime.fromisoformat(e["timestamp"]).strftime("%m/%d %I:%M%p")
        except (ValueError, KeyError):
            t = "??/??"
        head = (f"{t} {e['side'].upper()} x{e['count']:g} {e['entry_cents']:.0f}\u2192{e['exit_cents']}\u00a2 "
                f"{_signed_money(e['realized'])}")
        if e.get("result") in ("yes", "no"):
            outcome = "won" if e["result"] == e["side"] else "lost"
            lines.append(f"{head} | held: {_signed_money(_stop_if_held_pnl(e))} ({outcome})")
        elif e.get("result") == "void":
            lines.append(f"{head} | market voided")
        else:
            lines.append(f"{head} | result pending")

    if pending or voided:
        lines.append(f"({len(pending)} pending, {len(voided)} voided - excluded from the totals above)")
    if n < 10:
        lines.append("Small sample - don't over-read this yet.")
    return "\n".join(lines)

def _build_expectancy_message(last_n=None):
    log = _load_trade_log()
    if last_n:
        log = log[-last_n:]
    amounts = [e.get("amount", 0.0) for e in log]
    if not amounts:
        return "No completed trades recorded yet."

    wins = [a for a in amounts if a > 0]
    losses = [a for a in amounts if a < 0]
    n = len(amounts)
    win_rate = len(wins) / n * 100
    total = sum(amounts)
    scope = f"last {n} trades" if last_n else f"all {n} logged trades"
    lines = [f"\U0001F4D0 EXPECTANCY ({scope})",
             f"Win rate: {win_rate:.1f}% ({len(wins)}W / {len(losses)}L)"]

    if wins and losses:
        avg_win = sum(wins) / len(wins)
        avg_loss = abs(sum(losses) / len(losses))
        breakeven = avg_loss / (avg_win + avg_loss) * 100
        gap = win_rate - breakeven
        lines.append(f"Avg win: +${avg_win:.2f} | Avg loss: -${avg_loss:.2f}")
        lines.append(f"One average loss wipes out {avg_loss / avg_win:.1f} average wins")
        lines.append(f"Break-even win rate: {breakeven:.1f}%")
        if gap >= 0:
            lines.append(f"\u2705 You're {gap:.1f} pts ABOVE break-even")
        else:
            lines.append(f"\u26A0\uFE0F You're {-gap:.1f} pts BELOW break-even - this setup is losing money on average")
        lines.append(f"Profit factor: {sum(wins) / abs(sum(losses)):.2f}")
    elif wins:
        lines.append(f"Avg win: +${sum(wins) / len(wins):.2f} | No losses in this sample yet, so break-even can't be computed")
    elif losses:
        lines.append(f"Avg loss: -${abs(sum(losses) / len(losses)):.2f} | No wins in this sample")

    lines.append(f"Expected per trade: {_signed_money(total / n)} | Total: {_signed_money(total)}")

    by_reason = {}
    for e in log:
        r = e.get("reason") or "Unknown"
        cnt, amt = by_reason.get(r, (0, 0.0))
        by_reason[r] = (cnt + 1, amt + e.get("amount", 0.0))
    lines.append("--- By exit type ---")
    for r, (cnt, amt) in sorted(by_reason.items(), key=lambda kv: -kv[1][0]):
        lines.append(f"{r}: {cnt} trades, {_signed_money(amt)}")

    if n < 30:
        lines.append("Small sample - treat this as a rough read.")
    lines.append("(A partial fill counts as its own entry.)")
    return "\n".join(lines)
# ------------------------------------------------

# --- LIVE MARKET MOOD (calm vs choppy, based on recent price swings) ---
recent_price_jumps = deque(maxlen=30)
price_jumps_lock = threading.Lock()
MOOD_CHOPPY_THRESHOLD_CENTS = 8.5  # avg swing per check at/above this = choppy

def record_price_jump(jump_cents):
    with price_jumps_lock:
        recent_price_jumps.append(jump_cents)

def get_market_mood_raw():
    """Returns 'choppy', 'calm', or None (not enough data yet)."""
    with price_jumps_lock:
        jumps = list(recent_price_jumps)
    if len(jumps) < 5:
        return None
    avg_jump = sum(jumps) / len(jumps)
    return "choppy" if avg_jump >= MOOD_CHOPPY_THRESHOLD_CENTS else "calm"

def get_market_mood():
    with price_jumps_lock:
        jumps = list(recent_price_jumps)
    mood = get_market_mood_raw()
    if mood is None:
        return "\U0001F937 Not enough data yet"
    avg_jump = sum(jumps) / len(jumps)
    if mood == "choppy":
        return f"\u26A1 CHOPPY (avg swing {avg_jump:.1f}\u00a2/check)"
    return f"\U0001F60C CALM (avg swing {avg_jump:.1f}\u00a2/check)"
# ------------------------------------------------------------------

# --- MOOD-GATED BUY TRIGGERS ("tanking or spiking unless it's in our favor") ---
# Skips a buy trigger when the market currently reads CHOPPY, since that's
# exactly the condition under which last-minute reversals happen - EXCEPT
# when the side you're about to buy has shown a sustained, one-directional
# push toward triggering (not just a noisy bounce), which is treated as
# genuinely "in our favor" and allowed through even during chop.
MOOD_GATE_ENABLED = True
PRICE_SEQUENCE_LEN = 4  # consecutive readings required to confirm a sustained push
recent_price_sequences = {}  # market_ticker -> deque of (yes_ask, no_ask) tuples, oldest first

def record_price_sequence(market_ticker, yes_ask, no_ask):
    seq = recent_price_sequences.setdefault(market_ticker, deque(maxlen=PRICE_SEQUENCE_LEN))
    seq.append((yes_ask, no_ask))

def is_sustained_favorable_move(market_ticker, side):
    """True if this side's price has moved consistently UP over the last
    PRICE_SEQUENCE_LEN readings - a real one-directional push, not chop -
    even if the broader market mood currently reads choppy."""
    seq = recent_price_sequences.get(market_ticker)
    if not seq or len(seq) < PRICE_SEQUENCE_LEN:
        return False  # not enough data to confirm a real trend - no exception granted
    values = [yes if side == "yes" else no for (yes, no) in seq]
    non_decreasing = all(values[i] <= values[i + 1] for i in range(len(values) - 1))
    return non_decreasing and values[-1] > values[0]

def mood_allows_buy(market_ticker, side):
    if not MOOD_GATE_ENABLED:
        return True
    mood = get_market_mood_raw()
    if mood != "choppy":
        return True  # calm, or not enough data yet - no gate needed
    if is_sustained_favorable_move(market_ticker, side):
        print(f"--> [MOOD GATE] Market is choppy, but {side.upper()} has shown a sustained push "
              f"in its favor over the last {PRICE_SEQUENCE_LEN} checks - allowing the buy.")
        return True
    print(f"--> [MOOD GATE] Skipping {side.upper()} buy - market is choppy right now and this move "
          f"hasn't shown a sustained push in its favor. Last-minute reversals live in conditions like this.")
    return False
# --------------------------------------------------------------------------

# --- LIVE CONFIG PERSISTENCE ---
# /set* commands only change the RUNNING process's in-memory value. Without
# this, any restart (crash, manual restart, laptop sleep) silently reverts
# every live-tuned setting back to whatever's hardcoded in this file, with
# no warning that it happened. This saves each change to disk and restores
# it on the next startup.
CONFIG_OVERRIDES_FILE = "bot_config_overrides.json"

def _load_config_overrides():
    try:
        with open(CONFIG_OVERRIDES_FILE, "r") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return {}

def _save_config_override(name, value):
    try:
        overrides = _load_config_overrides()
        overrides[name] = value
        with open(CONFIG_OVERRIDES_FILE, "w") as f:
            json.dump(overrides, f, indent=2)
    except Exception as e:
        print(f"--> [WARNING] Could not save config override for {name}: {e}")

def _apply_saved_overrides():
    """Called once at startup - re-applies any settings changed live via
    Telegram in a previous run, so a restart doesn't silently undo them."""
    overrides = _load_config_overrides()
    if not overrides:
        return
    applied = []
    for name, value in overrides.items():
        if name in globals():
            globals()[name] = value
            applied.append(f"{name}={value}")
    if applied:
        print(f"--> Restored {len(applied)} setting(s) from a previous session: " + ", ".join(applied))
# --------------------------------

# --- NAMED CONFIG PRESETS ---
# /savepreset <name> snapshots the fields below; /loadpreset <name> restores
# them all at once (and persists the load the same way /set* commands do,
# so it survives a restart too).
PRESETS_FILE = "bot_presets.json"
PRESET_FIELDS = [
    "BUDGET_DOLLARS", "PROFIT_TARGET_DOLLARS", "STOP_LOSS_DOLLARS", "DAILY_LOSS_LIMIT_DOLLARS",
    "STANDARD_MAX_MINUTES", "HARD_ABSOLUTE_MAX_MINUTES", "EARLY_SPIKE_PRICE_CENTS",
    "NORMAL_TRIGGER_PRICE_CENTS", "MULTI_SHARE_THRESHOLD", "SECONDARY_TIME_LIMIT",
    "SECONDARY_PRICE_CENTS", "VELOCITY_FILTER_ENABLED", "MAX_PRICE_JUMP_CENTS",
    "MULTI_SHARE_CONTRACT_COUNT", "AUTOSELLING", "STOP_LOSS_ENABLED",
]

def _load_presets():
    try:
        with open(PRESETS_FILE, "r") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return {}

def _save_presets(presets):
    try:
        with open(PRESETS_FILE, "w") as f:
            json.dump(presets, f, indent=2)
    except Exception as e:
        print(f"--> [WARNING] Could not save presets file: {e}")
# ----------------------------

def load_private_key():
    """uses my rsa priv key for signing request"""
    with open(PRIVATE_KEY_PATH, "rb") as key_file:
        return load_pem_private_key(key_file.read(), password=None)

def send_alert(message):
    """Sends a Telegram message. Never raises - a failed alert should never
    take down the trading loop."""
    if not ALERTS_ENABLED:
        return
    if "PASTE_YOUR" in TELEGRAM_BOT_TOKEN or "PASTE_YOUR" in TELEGRAM_CHAT_ID:
        print("--> [WARNING] ALERTS_ENABLED is True but TELEGRAM_BOT_TOKEN/CHAT_ID aren't set yet.")
        return
    try:
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        payload = json.dumps({"chat_id": TELEGRAM_CHAT_ID, "text": message}).encode("utf-8")
        req = urllib.request.Request(
            url, data=payload, headers={"Content-Type": "application/json"}, method="POST"
        )
        urllib.request.urlopen(req, timeout=10)
    except Exception as e:
        print(f"--> [WARNING] Telegram alert failed to send: {e}")

def send_photo(image_path, caption=None):
    """Sends a local image file to Telegram as a photo (multipart upload via
    urllib, matching how send_alert already talks to Telegram - no extra
    HTTP library dependency). Never raises - a failed chart send should
    never take down the trading loop."""
    if not ALERTS_ENABLED:
        return
    if "PASTE_YOUR" in TELEGRAM_BOT_TOKEN or "PASTE_YOUR" in TELEGRAM_CHAT_ID:
        print("--> [WARNING] ALERTS_ENABLED is True but TELEGRAM_BOT_TOKEN/CHAT_ID aren't set yet.")
        return
    try:
        with open(image_path, "rb") as f:
            image_bytes = f.read()
        boundary = uuid.uuid4().hex

        def _field(name, value):
            return (f"--{boundary}\r\nContent-Disposition: form-data; name=\"{name}\"\r\n\r\n"
                    f"{value}\r\n").encode("utf-8")

        body = bytearray()
        body.extend(_field("chat_id", TELEGRAM_CHAT_ID))
        if caption:
            body.extend(_field("caption", caption))
        body.extend((f"--{boundary}\r\nContent-Disposition: form-data; name=\"photo\"; "
                     f"filename=\"chart.png\"\r\nContent-Type: image/png\r\n\r\n").encode("utf-8"))
        body.extend(image_bytes)
        body.extend(f"\r\n--{boundary}--\r\n".encode("utf-8"))

        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendPhoto"
        req = urllib.request.Request(
            url, data=bytes(body),
            headers={"Content-Type": f"multipart/form-data; boundary={boundary}"},
            method="POST"
        )
        urllib.request.urlopen(req, timeout=20)
    except Exception as e:
        print(f"--> [WARNING] Telegram photo send failed: {e}")

# --- NON-BLOCKING PUSH ALERTS ---
# send_alert() is a synchronous network call (up to a 10s timeout). That's fine
# for replying to a Telegram command, but the position-monitor thread (stop-loss
# / take-profit, checking every 0.1s) and the main scan loop must NEVER sit
# waiting on Telegram. push_alert() just drops the message on a queue and
# returns instantly; one background worker sends them in order.
_push_queue = queue.Queue(maxsize=200)

def push_alert(message):
    """Fire-and-forget Telegram alert. Safe to call from any thread, never
    blocks, never raises. Used for trade events and warnings."""
    if not ALERTS_ENABLED:
        return
    try:
        _push_queue.put_nowait(message)
    except queue.Full:
        print("--> [WARNING] Push alert queue full - dropping an alert.")

def _push_alert_worker():
    while True:
        message = _push_queue.get()
        try:
            send_alert(message)
        except Exception as e:
            print(f"--> [WARNING] Push alert worker error (continuing): {e}")
        time.sleep(0.3)  # stay well under Telegram's per-chat rate limit during bursts
# --------------------------------

from cryptography.hazmat.primitives.asymmetric import padding


def sign_request(private_key, timestamp_str, method, path):
    """generates required rsa-pss required by kalshi v2 API"""
    msg = f"{timestamp_str}{method}{path}".encode("utf-8")
    signature = private_key.sign(
        msg,
        padding.PSS(
            mgf=padding.MGF1(hashes.SHA256()),
            salt_length=padding.PSS.MAX_LENGTH
        ),
        hashes.SHA256()
    )
    return base64.b64encode(signature).decode("utf-8")

def kalshi_request(method, endpoint, payload=None):
    """authenticated REST requests to Kalshi V2 endpoints."""
    url = f"{HOST}{endpoint}"
    timestamp_str = str(int(time.time() * 1000))
    path = f"/trade-api/v2{endpoint}" 
    
    private_key = load_private_key()
    sig = sign_request(private_key, timestamp_str, method, path)
    
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "KALSHI-ACCESS-KEY": KEY_ID,
        "KALSHI-ACCESS-TIMESTAMP": timestamp_str,
        "KALSHI-ACCESS-SIGNATURE": sig
    }
    
    data = json.dumps(payload).encode("utf-8") if payload else None
    if method == "POST":
        print(f"--> DEBUG POST PAYLOAD: {payload}")
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    
    try:
        with urllib.request.urlopen(req) as response:
            return json.loads(response.read().decode())
    except urllib.error.HTTPError as e:
        error_body = e.read().decode()
        print(f"--> [HTTP {e.code}] Full Server Response: {error_body}")
        raise e
    
def transfer_shard_funds():
    """puts my wallet funds manually into Shard 2"""
    endpoint = "/portfolio/intra_exchange_instance_transfer"
    payload = {
        "amount": 10000,
        "source": "event_contract",
        "destination": "event_contract",
        "source_exchange_shard": 0,
        "destination_exchange_shard": 2,
        "source_subaccount": 0,
        "destination_subaccount": 0
    }
    
    try:
        print("--> Sending manual shard transfer request...")
        response = kalshi_request("POST", endpoint, payload=payload)
        print("--> Successfully transferred shard funds! Transfer ID:", response.get("transfer_id"))
        return response
    except Exception as e:
        print(f"--> [ERROR] Shard transfer failed: {e}")
        return None

def get_current_event_ticker():
    """figures out active current bitcoin ticker"""
    try:
        endpoint = "/markets?series_ticker=KXBTC15M&status=open"
        data = kalshi_request("GET", endpoint)
        markets = data.get("markets", [])
        
        if markets and isinstance(markets, list):
            now_utc = datetime.now(pytz.UTC)
            valid_markets = []
            for m in markets:
                close_time_str = m.get("close_time") or m.get("expiration_time")
                if close_time_str:
                    close_time = datetime.fromisoformat(close_time_str.replace("Z", "+00:00"))
                    if close_time > now_utc:
                        valid_markets.append((m, close_time))
            
            if valid_markets:
                valid_markets.sort(key=lambda x: x[1])
                resolved_event_ticker = valid_markets[0][0].get("event_ticker")
                if resolved_event_ticker:
                    print(f"--> [LIVE] Dynamically resolved active event ticker: {resolved_event_ticker}")
                    return resolved_event_ticker
            
    except Exception as e:
        print(f"--> [WARNING] Production event lookup via API failed: {e}")
        
    eastern = pytz.timezone('US/Eastern')
    now_et = datetime.now(eastern)
    minutes_to_add = 15 - (now_et.minute % 15)
    expiration_time = now_et + timedelta(minutes=minutes_to_add)
    
    year_str = expiration_time.strftime("%y")
    month_str = expiration_time.strftime("%b")
    day_str = expiration_time.strftime("%d")
    time_str = expiration_time.strftime("%H%M")
    
    calculated_ticker = f"KXBTC15M-{year_str}{month_str}{day_str}{time_str}"
    print(f"--> [LIVE FALLBACK] Calculated expected ticker: {calculated_ticker}")
    return calculated_ticker

def _signed_money(amount):
    return f"{'+' if amount >= 0 else '-'}${abs(amount):.2f}"

def _push_buy_alert(ticker, side, price_cents, count, is_secondary, forced_count, response):
    """Telegram push for a newly placed buy. Never raises - an alert problem
    must not affect trading."""
    try:
        if is_secondary:
            kind = "secondary add"
        elif forced_count is not None:
            kind = "multi-share"
        else:
            kind = "standard"
        cost = count * price_cents / 100.0
        lines = [f"\U0001F7E2 BUY ({kind}): {side.upper()} x{count} @ {price_cents}\u00a2 = ${cost:.2f}"]
        detail = ticker
        close_time = _market_close_time_cache.get(ticker)
        if close_time:
            mins_left = (close_time - datetime.now(pytz.UTC)).total_seconds() / 60.0
            detail += f" | {mins_left:.1f}m left"
        lines.append(detail)
        try:
            fc = float(response.get("fill_count"))
            if fc < count:
                lines.append(f"\u23F3 Filled {fc:g} of {count} so far")
        except (TypeError, ValueError, AttributeError):
            pass  # response didn't include a usable fill_count - just report the order
        push_alert("\n".join(lines))
    except Exception as e:
        print(f"--> [WARNING] Could not build buy alert: {e}")

def execute_order(ticker, side, price_cents, budget_dollars=None, forced_count=None, is_secondary=False):
    """Executes a V2 order via native authenticated HTTP POST."""
    if price_cents <= 0:
        print("--> [ERROR] Invalid price cents for order execution.")
        return None

    if forced_count is not None:
        count = forced_count
    else:
        if budget_dollars is None:
            # Read the CURRENT global here, at call time - the old
            # `budget_dollars=BUDGET_DOLLARS` default was evaluated once when
            # the script started and never updated again, silently ignoring
            # every /setbudget change no matter how many times it was sent.
            budget_dollars = BUDGET_DOLLARS
        budget_cents = int(budget_dollars * 100)
        count = budget_cents // price_cents
        if count < 1:
            print(f"--> [SKIP] Budget ${budget_dollars:.2f} can't cover price {price_cents}¢. Skipping trade.")
            return None

    client_order_id = str(uuid.uuid4())

    print(f"--> Sizing order: Buying {count} contract(s) at {price_cents}¢ (Total Spend: ${count * (price_cents/100.0):.2f})")

    endpoint = "/portfolio/events/orders"

    if side.lower() == "yes":
        market_side = "bid"
        yes_price_dollars = Decimal(price_cents) / Decimal("100")
    else:
        market_side = "ask"
        yes_price_dollars = Decimal(100 - price_cents) / Decimal("100")

    price_str = f"{yes_price_dollars:.4f}"
    count_str = f"{count:.2f}"

    payload = {
        "ticker": ticker,
        "client_order_id": client_order_id,
        "side": market_side,
        "count": count_str,
        "price": price_str,
        "time_in_force": "good_till_canceled",
        "self_trade_prevention_type": "taker_at_cross"
    }

    try:
        response = kalshi_request("POST", endpoint, payload=payload)
        if is_secondary:
            secondary_traded_sides.setdefault(ticker, set()).add(side.lower())
        else:
            traded_tickers.add(ticker)

        record_position(ticker, side.lower(), price_cents, count)

        local_time_str = time.strftime('%I:%M:%S %p')
        print(f"[{local_time_str}] SUCCESS! V2 Order placed for {ticker}. ID: {client_order_id}")
        _push_buy_alert(ticker, side.lower(), price_cents, count, is_secondary, forced_count, response)
        return response
    except Exception as e:
        print(f"--> [ERROR] V2 Order execution failed: {e}")
        return None

def record_position(ticker, side, price_cents, count):
    """tracks my open positions so autosell can check its profits/losses later"""
    with positions_lock:
        existing = open_positions.get(ticker)
        if existing and existing["side"] == side:
            total_cost = existing["entry_price_cents"] * existing["count"] + price_cents * count
            total_count = existing["count"] + count
            existing["entry_price_cents"] = total_cost / total_count
            existing["count"] = total_count
        else:
            open_positions[ticker] = {"side": side, "entry_price_cents": float(price_cents), "count": count}

def get_active_market_strike_ticker(event_ticker):
    """gets active market strike tickers through REST. Also returns the
    market's close_time if this same response includes it, so callers can
    avoid a separate, redundant /markets/{ticker} fetch just for a value
    that never changes once a market exists. Returns (ticker, close_time_str)."""
    try:
        data = kalshi_request("GET", f"/events/{event_ticker}")
        markets = data.get("markets", [])
        if markets and len(markets) > 0:
            market = markets[0]
            ticker = market.get("ticker")
            close_time_str = market.get("close_time") or market.get("expiration_time")
            return ticker, close_time_str
    except Exception as e:
        print(f"--> [ERROR] Could not resolve market ticker for event {event_ticker}: {e}")
    return None, None

def _get_cached_close_time(market_ticker, close_time_str_hint=None):
    """Returns a market's close_time as a UTC datetime, cached forever per
    ticker since it's immutable once the market exists. Uses the hint from
    the event listing when available; only falls back to a direct
    /markets/{ticker} fetch (also then cached) if that hint wasn't given."""
    if market_ticker in _market_close_time_cache:
        return _market_close_time_cache[market_ticker]

    close_time_str = close_time_str_hint
    if not close_time_str:
        try:
            market_data = kalshi_request("GET", f"/markets/{market_ticker}")
            market_info = market_data.get("market", {})
            close_time_str = market_info.get("close_time") or market_info.get("expiration_time")
        except Exception as e:
            print(f"--> [WARNING] Could not fetch close_time for {market_ticker}: {e}")
            return None

    if not close_time_str:
        return None

    close_time = datetime.fromisoformat(close_time_str.replace("Z", "+00:00"))
    _market_close_time_cache[market_ticker] = close_time
    return close_time

def get_market_volume(market_ticker):
    """Returns this market's total traded volume (contracts), cached for
    VOLUME_CACHE_TTL_SECONDS per ticker so the liquidity filter doesn't add
    an extra API round-trip on every 0.5s loop cycle. Returns None on failure
    so callers can choose to fail open rather than blocking trading on a
    transient API hiccup."""
    cached = _market_volume_cache.get(market_ticker)
    now = time.time()
    if cached and (now - cached[1]) < VOLUME_CACHE_TTL_SECONDS:
        return cached[0]

    try:
        market_data = kalshi_request("GET", f"/markets/{market_ticker}")
        market_info = market_data.get("market", market_data)
        volume = market_info.get("volume")
        if volume is None:
            volume = market_info.get("volume_24h")
        if volume is None:
            return cached[0] if cached else None
        volume = int(volume)
        _market_volume_cache[market_ticker] = (volume, now)
        return volume
    except Exception as e:
        print(f"--> [WARNING] Could not fetch volume for {market_ticker}: {e}")
        return cached[0] if cached else None

def get_position_bid_price(market_ticker, side):
    """gets the current best bid (in cents) for the side of a held position -
    i.e. the price one could sell into right now."""
    try:
        data = kalshi_request("GET", f"/markets/{market_ticker}/orderbook")
        ob = data.get("orderbook_fp") or data.get("orderbook") or data
        yes_bids = ob.get("yes_dollars") or ob.get("yes") or []
        no_bids = ob.get("no_dollars") or ob.get("no") or []

        def get_top_bid_cents(bids):
            if not bids:
                return 0
            top_entry = bids[-1] if isinstance(bids, list) else bids
            price_val = top_entry[0] if isinstance(top_entry, list) else top_entry
            if isinstance(price_val, str) or float(price_val) <= 1.0:
                return int(round(float(price_val) * 100))
            return int(round(float(price_val)))

        return get_top_bid_cents(yes_bids if side == "yes" else no_bids)
    except Exception as e:
        print(f"--> [ERROR] Could not fetch bid price for {market_ticker}: {e}")
        return None

def execute_sell_order(ticker, side, price_cents, count):
    """Sells to CLOSE an existing position.

    IMPORTANT: this endpoint's 'side' field is book_side (bid/ask), not
    yes/no, and it has NO 'action' field - Kalshi's V2 orders endpoint only
    understands which side of the book you're trading, always priced in YES
    terms. To actually close a position (not open a new/opposite one), submit
    the OPPOSITE book_side from a fresh buy of that side, with reduce_only=True
    so the exchange caps the order at your existing position:
        - Closing a YES position -> book_side "ask" (sell YES), price = YES price directly
        - Closing a NO position  -> book_side "bid" (buy YES = sell NO), price = 100 - NO price
    reduce_only requires time_in_force to be immediate_or_cancel or fill_or_kill.
    """
    if price_cents <= 0:
        print("--> [ERROR] Invalid price cents for sell order.")
        return None
 
    client_order_id = str(uuid.uuid4())
    endpoint = "/portfolio/events/orders"
 
    if side.lower() == "yes":
        market_side = "ask"   # ask = sell YES -> closes a long-yes position
        order_price_cents = price_cents
    else:
        market_side = "bid"   # bid = buy YES = sell NO -> closes a long-no position
        order_price_cents = 100 - price_cents
 
    # Kalshi rejects a literal 0¢ price as invalid (and likely 100¢ too, since
    # those represent settled certainty rather than a tradable price). Clamp
    # into the valid 1-99 range so an extreme bid (e.g. current_bid=100 on a
    # "no" position) doesn't silently block every take-profit/stop-loss retry.
    order_price_cents = max(1, min(99, order_price_cents))
    yes_price_dollars = Decimal(order_price_cents) / Decimal("100")
 
    price_str = f"{yes_price_dollars:.4f}"
    count_str = f"{count:.2f}"
 
    payload = {
        "ticker": ticker,
        "client_order_id": client_order_id,
        "side": market_side,
        "count": count_str,
        "price": price_str,
        "time_in_force": "immediate_or_cancel",
        "reduce_only": True,
        "self_trade_prevention_type": "taker_at_cross"
    }
 
    try:
        response = kalshi_request("POST", endpoint, payload=payload)
    except Exception as e:
        print(f"--> [ERROR] Sell order failed for {ticker}: {e}")
        return 0.0

    local_time_str = time.strftime('%I:%M:%S %p')
    try:
        fill_count = float(response.get("fill_count", "0") or 0)
    except (TypeError, ValueError, AttributeError):
        print(f"--> [WARNING] Could not parse fill_count from sell response for {ticker}: {response}")
        fill_count = 0.0

    if fill_count <= 0:
        # The order was ACCEPTED but an IOC order with no matching liquidity
        # at that exact price gets canceled with 0 fills - this is NOT a sale.
        # The position is still fully open; check_autosell will retry next cycle.
        print(f"--> [WARNING] Sell order for {ticker} was accepted but did NOT fill "
              f"(0 of {count} - price likely moved before it could cross). "
              f"Position remains open, will retry next check.")
    elif fill_count < count:
        print(f"[{local_time_str}] PARTIAL SELL for {ticker}: filled {fill_count} of {count} "
              f"contract(s) @ ~{price_cents}\u00a2. ID: {client_order_id}")
    else:
        print(f"[{local_time_str}] AUTOSOLD {ticker}! Sold {fill_count} contract(s) @ {price_cents}\u00a2. ID: {client_order_id}")

    return fill_count
    
def check_market_status(market_ticker):
    """checks if a market has already closed/expired, how much time is left
    if not, and the settlement result if it has closed - returns
    (is_closed, remaining_minutes_or_None, result_or_None). Combined into one
    call since this runs frequently per open position now. result reads
    Kalshi's "market_result" field: "yes"/"no" on a normal settlement,
    "void" if the market was voided (contracts refunded at cost - no real
    gain/loss), or None if unsettled/unavailable rather than guessing."""
    try:
        data = kalshi_request("GET", f"/markets/{market_ticker}")
        market_info = data.get("market", {})
        status = (market_info.get("status") or "").lower()
        result = (market_info.get("market_result") or "").lower() or None
        if status and status not in ("open", "active"):
            return True, None, result

        close_time_str = market_info.get("close_time") or market_info.get("expiration_time")
        if close_time_str:
            close_time = datetime.fromisoformat(close_time_str.replace("Z", "+00:00"))
            now_utc = datetime.now(pytz.UTC)
            if close_time <= now_utc:
                return True, None, result
            remaining_minutes = (close_time - now_utc).total_seconds() / 60.0
            return False, remaining_minutes, None

        return False, None, None
    except Exception as e:
        print(f"--> [WARNING] Could not verify close status for {market_ticker}: {e}")
        return False, None, None

daily_biggest_win = 0.0
daily_biggest_win_ticker = None

def _record_realized_pnl(amount_dollars, reason, market_ticker):
    global session_realized_pnl, daily_biggest_win, daily_biggest_win_ticker
    with session_pnl_lock:
        session_realized_pnl += amount_dollars
        total = session_realized_pnl
        if amount_dollars > daily_biggest_win:
            daily_biggest_win = amount_dollars
            daily_biggest_win_ticker = market_ticker
    local_time_str = time.strftime('%I:%M:%S %p')
    sign = "+" if amount_dollars >= 0 else ""
    print(f"[{local_time_str}] [SESSION P/L] {reason} for {market_ticker}: {sign}${amount_dollars:.2f} "
          f"| Running session total: ${total:.2f}")
    record_trade_stats(amount_dollars)
    record_trade_log_entry(market_ticker, amount_dollars, reason)
    return total

def _push_exit_alert(reason, ticker, side, filled, entry_cents, exit_cents, realized, remaining, total):
    try:
        icon = {"Take-profit": "\U0001F4B0", "Stop-loss": "\U0001F6D1"}.get(reason, "\U0001F4B8")
        lines = [
            f"{icon} {reason.upper()}: sold {side.upper()} x{filled:g} @ {exit_cents}\u00a2 (in @ {entry_cents:.1f}\u00a2)",
            ticker,
            f"P/L: {_signed_money(realized)} | Session (tracked): {_signed_money(total)}",
        ]
        if remaining > 0:
            lines.append(f"\u26A0\uFE0F Partial fill - {remaining:g} contract(s) still open")
        push_alert("\n".join(lines))
    except Exception as e:
        print(f"--> [WARNING] Could not build exit alert: {e}")

def _apply_fill_to_position(market_ticker, filled_count, sell_price_cents=None, reason="Sold", minutes_left=None):
    """Updates open_positions based on what an exit order ACTUALLY filled,
    rather than assuming the whole requested count sold. filled_count of 0
    means the IOC order didn't cross the book at all - leave the position
    untouched so the next check retries at a fresh price. Also records the
    realized P/L from whatever portion actually sold."""
    if not filled_count or filled_count <= 0:
        return
    with positions_lock:
        position = open_positions.get(market_ticker)
        if not position:
            return
        entry_price = position["entry_price_cents"]
        pos_side = position["side"]
        if filled_count >= position["count"]:
            del open_positions[market_ticker]
            remaining = 0
            trailing_stop_peak.pop(market_ticker, None)  # fully closed - clear any trailing-stop peak tracked for it
        else:
            position["count"] -= filled_count
            remaining = position["count"]

    if sell_price_cents is not None:
        realized = (sell_price_cents - entry_price) * filled_count / 100.0
        total = _record_realized_pnl(realized, reason, market_ticker)
        # Extras below must never be able to break the bookkeeping above.
        try:
            if reason == "Stop-loss":
                record_stop_event(market_ticker, pos_side, entry_price, sell_price_cents,
                                  filled_count, realized, minutes_left)
            if reason != "Manual sell":  # /sell already replies to you directly
                _push_exit_alert(reason, market_ticker, pos_side, filled_count, entry_price,
                                 sell_price_cents, realized, remaining, total)
        except Exception as e:
            print(f"--> [WARNING] Post-sell bookkeeping/alert failed (trade itself was recorded fine): {e}")


def get_kalshi_account_balance():
    """Fetches the actual cash/portfolio balance from Kalshi in dollars."""
    try:
        data = kalshi_request("GET", "/portfolio/balance")
        # Kalshi usually returns balance in cents (e.g., balance or cash_balance)
        balance_cents = data.get("balance") or data.get("cash_balance") or 0
        return float(balance_cents) / 100.0
    except Exception as e:
        print(f"--> [WARNING] Failed to fetch account balance: {e}")
        return None

def get_session_pnl():
    """Returns the REAL session P/L, adjusted for money currently tied up in
    open positions. Naively using (current balance - starting balance) is
    WRONG: buying a position spends cash immediately, making it look like a
    big loss the instant you buy, even though the money just moved into an
    asset you still hold (this was firing the daily loss limit on fresh buys
    with $0.00 unrealized P/L). Adding back the cost basis of everything
    still open corrects for that - only genuinely realized gains/losses
    (from sells and settlements, which have already flowed through to cash)
    show up here. Returns None if balance can't be fetched or the starting
    balance was never captured - callers should treat None as "unknown," not $0."""
    if session_start_balance is None:
        return None
    current = get_kalshi_account_balance()
    if current is None:
        return None
    with positions_lock:
        open_cost_basis = sum(pos["entry_price_cents"] / 100.0 * pos["count"] for pos in open_positions.values())
    return (current - session_start_balance) + open_cost_basis

def check_autosell(market_ticker):
    """this oversees exits for an open position:
    - Takes profit once unrealized P/L reaches PROFIT_TARGET_DOLLARS (if AUTOSELLING).
    - Cuts losses once unrealized P/L drops to -STOP_LOSS_DOLLARS (if STOP_LOSS_ENABLED),
      but late in the market's life requires the loss to persist across several
      consecutive checks first, to filter out a single whale-driven price spike
      that reverts rather than a genuine reversal.
    + they both share the same bid lookup so this only costs one extra call per check."""
    if not AUTOSELLING and not STOP_LOSS_ENABLED:
        return

    with positions_lock:
        position = open_positions.get(market_ticker)
    if not position:
        return

    # Reuse the same close_time cache the buy-side loop already populates
    # instead of hitting /markets/{ticker} on every single position check.
    # This was adding a full redundant round-trip to the TAKE-PROFIT/STOP-LOSS
    # decision path on every ~0.5s check - exactly the kind of delay that lets
    # a brief profit window slip by before the market flips. We only need a
    # live fetch once we're actually at/past the cached close_time, since the
    # settlement result genuinely can't be known ahead of time.
    cached_close_time = _market_close_time_cache.get(market_ticker)
    now_utc = datetime.now(pytz.UTC)
    if cached_close_time and now_utc < cached_close_time:
        remaining_minutes = (cached_close_time - now_utc).total_seconds() / 60.0
        is_closed, result = False, None
    else:
        # Once we know it's closed but Kalshi hasn't posted a settlement
        # result yet, don't re-fetch /markets/{ticker} on every 0.1s cycle
        # while waiting - that's a lot of wasted calls for a value that only
        # changes once, on its own schedule.
        last_pending_check = _pending_settlement_last_check.get(market_ticker)
        if last_pending_check is not None and (now_utc.timestamp() - last_pending_check) < PENDING_SETTLEMENT_RECHECK_SECONDS:
            return
        is_closed, remaining_minutes, result = check_market_status(market_ticker)

    if is_closed:
        if result in ("yes", "no"):
            print(f"--> [POSITION MGMT] {market_ticker} settled '{result}'. Dropping from tracked positions.")
            with positions_lock:
                closed_position = open_positions.pop(market_ticker, None)
                held_positions.discard(market_ticker)
            stop_loss_breach_started.pop(market_ticker, None)
            last_known_bid.pop(market_ticker, None)
            trailing_stop_peak.pop(market_ticker, None)
            _pending_settlement_last_check.pop(market_ticker, None)
            _pending_settlement_first_seen.pop(market_ticker, None)
            if closed_position:
                if result == closed_position["side"]:
                    realized = (100 - closed_position["entry_price_cents"]) * closed_position["count"] / 100.0
                else:
                    realized = -closed_position["entry_price_cents"] * closed_position["count"] / 100.0
                total = _record_realized_pnl(realized, "Settled (held to expiration)", market_ticker)
                settle_label = "\u2705 SETTLED WIN" if realized > 0 else "\u274C SETTLED LOSS"
                push_alert(
                    f"{settle_label}: {closed_position['side'].upper()} "
                    f"x{closed_position['count']} (in @ {closed_position['entry_price_cents']:.1f}\u00a2)\n"
                    f"{market_ticker}\n"
                    f"P/L: {_signed_money(realized)} | Session (tracked): {_signed_money(total)}"
                )
            return

        elif result == "void":
            print(f"--> [POSITION MGMT] {market_ticker} was voided - contracts refunded at cost, "
                  f"no gain/loss (not counted against session P/L).")
            with positions_lock:
                closed_position = open_positions.pop(market_ticker, None)
                held_positions.discard(market_ticker)
            stop_loss_breach_started.pop(market_ticker, None)
            last_known_bid.pop(market_ticker, None)
            trailing_stop_peak.pop(market_ticker, None)
            _pending_settlement_last_check.pop(market_ticker, None)
            _pending_settlement_first_seen.pop(market_ticker, None)
            # Logged at $0 so it still shows up in /history (rather than just
            # vanishing) without touching lifetime_pnl, win rate, or streaks -
            # a void isn't a real trade outcome.
            record_trade_log_entry(market_ticker, 0.0, "Voided (refunded)")
            push_alert(f"\u21A9\uFE0F VOIDED: {market_ticker} - contracts refunded at cost, no gain/loss.")
            return

        else:
            # Closed, but Kalshi hasn't posted the settlement result yet.
            # Previously this dropped the position untracked right here,
            # which silently erased real wins/losses from every stat that
            # matters (lifetime P/L, win rate, /history) - the account
            # balance still moved, the bot just stopped watching for it.
            # Instead: keep the position tracked and keep polling (throttled
            # above) until a real result shows up, or we give up after
            # MAX_SETTLEMENT_WAIT_MINUTES so a genuinely stuck market can't
            # leak memory or hammer the API forever.
            now_ts_pending = now_utc.timestamp()
            first_seen = _pending_settlement_first_seen.setdefault(market_ticker, now_ts_pending)
            _pending_settlement_last_check[market_ticker] = now_ts_pending
            waited_minutes = (now_ts_pending - first_seen) / 60.0

            if waited_minutes < MAX_SETTLEMENT_WAIT_MINUTES:
                print(f"--> [POSITION MGMT] {market_ticker} closed but settlement result not posted yet "
                      f"({waited_minutes:.1f}m waiting) - will keep checking every "
                      f"{PENDING_SETTLEMENT_RECHECK_SECONDS}s instead of dropping it untracked.")
                return

            print(f"--> [WARNING] {market_ticker} closed {waited_minutes:.0f}m ago with still no settlement "
                  f"result - giving up on this one. Session P/L does NOT include this position's outcome.")
            with positions_lock:
                open_positions.pop(market_ticker, None)
                held_positions.discard(market_ticker)
            stop_loss_breach_started.pop(market_ticker, None)
            last_known_bid.pop(market_ticker, None)
            trailing_stop_peak.pop(market_ticker, None)
            _pending_settlement_last_check.pop(market_ticker, None)
            _pending_settlement_first_seen.pop(market_ticker, None)
            push_alert(f"\u26A0\uFE0F {market_ticker} closed {waited_minutes:.0f}m ago but its settlement result "
                       f"never posted - this outcome is NOT in your tracked session P/L. Check /balance for the real number.")
            return

    current_bid = get_position_bid_price(market_ticker, position["side"])
    now_ts = time.time()

    if current_bid is None or current_bid <= 0:
        # Book is empty on this side right now - very often this happens
        # BECAUSE a losing side is collapsing toward worthless and nobody
        # wants to bid on it, i.e. the exact moment a stop-loss matters most.
        # If we were already mid-confirmation on a real breach before the
        # book went quiet, don't just do nothing: attempt a best-effort exit
        # at the lowest legal price (1c). If nothing's really there to match,
        # this is a harmless 0-fill (see execute_sell_order); if there IS a
        # resting bid the orderbook snapshot missed, this actually saves the
        # position from riding to zero. Never do this on a fresh/unconfirmed
        # position - only once we've already established a genuine breach.
        breach_started = stop_loss_breach_started.get(market_ticker)
        if STOP_LOSS_ENABLED and breach_started is not None:
            with positions_lock:
                is_held = market_ticker in held_positions
            if not is_held:
                entry_price = position["entry_price_cents"]
                count = position["count"]
                elapsed = now_ts - breach_started
                print(f"--> [STOP-LOSS] {market_ticker} has no live bid ({elapsed:.1f}s into a confirmed breach) - "
                      f"book looks empty on the losing side. Attempting a defensive exit at 1\u00a2 rather than "
                      f"riding this to zero blind...")
                filled = execute_sell_order(market_ticker, position["side"], 1, count)
                if filled and filled > 0:
                    _apply_fill_to_position(market_ticker, filled, sell_price_cents=1,
                                            reason="Stop-loss (defensive - no live bid)")
                    stop_loss_breach_started.pop(market_ticker, None)
        # Whether or not a defensive attempt fired, there's no valid bid to
        # value the position against this cycle - skip further action, but
        # crucially do NOT clear stop_loss_breach_started here: a momentary
        # empty book shouldn't erase real confirmation progress already made.
        return

    last_known_bid[market_ticker] = (current_bid, now_ts)

    entry_price = position["entry_price_cents"]
    count = position["count"]
    profit_dollars = (current_bid - entry_price) * count / 100.0

    local_time_str = time.strftime('%I:%M:%S %p')
    print(f"[{local_time_str}] [POSITION CHECK] {market_ticker} | Side: {position['side']} | "
          f"Entry: {entry_price:.1f}\u00a2 | Current Bid: {current_bid}\u00a2 | Count: {count} | "
          f"Unrealized P/L: ${profit_dollars:.2f}")

    with positions_lock:
        is_held = market_ticker in held_positions
    if is_held:
        print(f"--> [HELD] {market_ticker} is manually held via /hold - skipping automatic take-profit/stop-loss. "
              f"Send /unhold to hand it back to automation, or /sell to close it now.")
        return

    if AUTOSELLING and TRAILING_STOP_ENABLED and count > TRAILING_STOP_MIN_CONTRACTS:
        # Large position - trail instead of using the flat PROFIT_TARGET_DOLLARS
        # exit below. Once profit reaches the arm level, track the best profit
        # seen (trailing_stop_peak) and sell only if it falls back by the trail
        # amount, so a strong move isn't cut short right at the old fixed target.
        if profit_dollars >= TRAILING_STOP_ARM_DOLLARS:
            peak = trailing_stop_peak.get(market_ticker, profit_dollars)
            if profit_dollars > peak:
                peak = profit_dollars
                trailing_stop_peak[market_ticker] = peak
            trigger_level = peak - TRAILING_STOP_TRAIL_DOLLARS
            if profit_dollars <= trigger_level:
                stop_loss_breach_started.pop(market_ticker, None)
                print(f"--> TRAILING STOP TRIGGERED! {market_ticker} profit pulled back to ${profit_dollars:.2f} "
                      f"from a peak of ${peak:.2f} (>= ${TRAILING_STOP_TRAIL_DOLLARS:.2f} pullback). "
                      f"Selling {count} contract(s) to lock in the gain...")
                filled = execute_sell_order(market_ticker, position["side"], current_bid, count)
                _apply_fill_to_position(market_ticker, filled, sell_price_cents=current_bid, reason="Trailing stop")
                trailing_stop_peak.pop(market_ticker, None)
                return
            print(f"--> [TRAILING STOP WATCH] {market_ticker} profit ${profit_dollars:.2f}, peak ${peak:.2f}, "
                  f"sells if it drops to ${trigger_level:.2f}.")
        # Not armed yet (profit hasn't reached TRAILING_STOP_ARM_DOLLARS) - a
        # large position just holds here rather than taking the small fixed
        # target below, which is the whole point of trailing for big size.
    elif AUTOSELLING and profit_dollars >= PROFIT_TARGET_DOLLARS:
        stop_loss_breach_started.pop(market_ticker, None)  # position recovered into profit - any stop-loss streak no longer applies
        print(f"--> TAKE-PROFIT TRIGGERED! Profit ${profit_dollars:.2f} >= ${PROFIT_TARGET_DOLLARS:.2f} target. "
              f"Selling {count} contract(s)...")
        filled = execute_sell_order(market_ticker, position["side"], current_bid, count)
        _apply_fill_to_position(market_ticker, filled, sell_price_cents=current_bid, reason="Take-profit")
        return

    if STOP_LOSS_ENABLED and profit_dollars <= -STOP_LOSS_DOLLARS:
        needs_confirmation = (remaining_minutes is not None
                              and remaining_minutes < STOP_LOSS_CONFIRMATION_TIME_THRESHOLD_MINUTES)
        if needs_confirmation:
            breach_started = stop_loss_breach_started.get(market_ticker)
            if breach_started is None:
                stop_loss_breach_started[market_ticker] = now_ts
                breach_started = now_ts
            elapsed = now_ts - breach_started
            if elapsed < STOP_LOSS_CONFIRMATION_SECONDS:
                print(f"--> [STOP-LOSS WATCH] {market_ticker} loss ${profit_dollars:.2f} past -${STOP_LOSS_DOLLARS:.2f} "
                      f"limit ({elapsed:.1f}s/{STOP_LOSS_CONFIRMATION_SECONDS}s confirming, "
                      f"{remaining_minutes:.1f}m left). Waiting to see if it holds before selling.")
                return
        print(f"--> STOP-LOSS TRIGGERED! Loss ${profit_dollars:.2f} <= -${STOP_LOSS_DOLLARS:.2f} limit. "
              f"Selling {count} contract(s) to cut losses...")
        filled = execute_sell_order(market_ticker, position["side"], current_bid, count)
        _apply_fill_to_position(market_ticker, filled, sell_price_cents=current_bid,
                                reason="Stop-loss", minutes_left=remaining_minutes)
        stop_loss_breach_started.pop(market_ticker, None)
        return

    # Neither condition met this check - if a loss streak was building, it
    # didn't hold up, so reset it rather than let stale strikes accumulate.
    stop_loss_breach_started.pop(market_ticker, None)

def check_all_autosells():
    """Runs position-exit check against every currently open position."""
    if not AUTOSELLING and not STOP_LOSS_ENABLED:
        return
    with positions_lock:
        tickers = list(open_positions.keys())
    for ticker in tickers:
        check_autosell(ticker)

_loss_limit_pnl_cache = {"value": None, "checked_at": 0.0}
_loss_limit_pnl_cache_lock = threading.Lock()
LOSS_LIMIT_PNL_CACHE_TTL_SECONDS = 5  # avoids hitting the balance API on every ~2.5s scan cycle

def get_cached_session_pnl_for_limit_check():
    """Same real balance-based P/L as get_session_pnl(), but cached briefly
    since the daily loss limit is checked every main-loop cycle now - a 5s
    cache keeps that check current without adding a live API call that often."""
    now = time.time()
    with _loss_limit_pnl_cache_lock:
        if now - _loss_limit_pnl_cache["checked_at"] < LOSS_LIMIT_PNL_CACHE_TTL_SECONDS:
            return _loss_limit_pnl_cache["value"]
    fresh = get_session_pnl()
    with _loss_limit_pnl_cache_lock:
        _loss_limit_pnl_cache["value"] = fresh
        _loss_limit_pnl_cache["checked_at"] = now
    return fresh

def _auto_resume_if_pause_expired():
    """Ends a timed /pausefor once its time is up. Called from both the scan
    loop and the Telegram thread so it happens promptly either way."""
    global trading_paused, _pause_until
    with _pause_lock:
        if trading_paused and _pause_until is not None and time.time() >= _pause_until:
            trading_paused = False
            _pause_until = None
            push_alert("\u25B6\uFE0F Timed pause finished - trading RESUMED.")

def check_market_and_trade(market_ticker):
    """checks active orderbook with standard windows and secondary sub-2-minute high-price triggers."""
    global _loss_limit_alerted
    _auto_resume_if_pause_expired()  # first, so a finished timer isn't held up by the loss-limit check below

    if DAILY_LOSS_LIMIT_ENABLED and not loss_limit_overridden:
        current_pnl = get_cached_session_pnl_for_limit_check()
        if current_pnl is not None and current_pnl <= -DAILY_LOSS_LIMIT_DOLLARS:
            if not _loss_limit_alerted:
                _loss_limit_alerted = True
                push_alert(f"\U0001F6D1 DAILY LOSS LIMIT HIT: session P/L {_signed_money(current_pnl)} is at/past "
                           f"-${DAILY_LOSS_LIMIT_DOLLARS:.2f}.\nNo new positions will be opened. Open positions are "
                           f"still managed normally.\nSend /unlockloss to override.")
            local_time_str = time.strftime('%I:%M:%S %p')
            print(f"[{local_time_str}] [DAILY LOSS LIMIT] Session P/L ${current_pnl:.2f} has hit the "
                  f"-${DAILY_LOSS_LIMIT_DOLLARS:.2f} limit. No new positions will be opened. "
                  f"(Already-open positions still get managed normally. Send /unlockloss via Telegram to override.)")
            return
        elif current_pnl is None:
            local_time_str = time.strftime('%I:%M:%S %p')
            print(f"[{local_time_str}] [WARNING] Could not verify balance for daily loss limit check this cycle - "
                  f"proceeding without blocking (transient API issue assumed).")
        else:
            _loss_limit_alerted = False  # back inside the limit - re-arm the alert for the next trip

    if trading_paused:
        local_time_str = time.strftime('%I:%M:%S %p')
        print(f"[{local_time_str}] [PAUSED] Trading paused via Telegram /pause. "
              f"No new positions will be opened. (Already-open positions still get managed normally.)")
        return

    # Thresholds below are module-level globals (see top of file) so /setthreshold
    # and /setmultishare can change them live from Telegram without a restart.

    # 1. Check expiration/close time window
    try:
        close_time = _get_cached_close_time(market_ticker)

        if close_time:
            now_utc = datetime.now(pytz.UTC)
            remaining_minutes = (close_time - now_utc).total_seconds() / 60.0
            
            if remaining_minutes > HARD_ABSOLUTE_MAX_MINUTES:
                local_time_str = time.strftime('%I:%M:%S %p')
                print(f"[{local_time_str}] Market {market_ticker} has too much time left ({remaining_minutes:.1f} min > {HARD_ABSOLUTE_MAX_MINUTES}m cap). Skipping.")
                return
            
            if remaining_minutes < 0.3:
                local_time_str = time.strftime('%I:%M:%S %p')
                print(f"[{local_time_str}] Market {market_ticker} is expiring imminently ({remaining_minutes:.1f} min left). Skipping.")
                return
    except Exception as e:
        print(f"--> [WARNING] Could not verify market expiration time: {e}")
        return

    # 2. Check orderbook and evaluate triggers
    try:
        data = kalshi_request("GET", f"/markets/{market_ticker}/orderbook")
        
        ob = data.get("orderbook_fp") or data.get("orderbook") or data
        yes_bids = ob.get("yes_dollars") or ob.get("yes") or []
        no_bids = ob.get("no_dollars") or ob.get("no") or []
        
        def get_top_bid_cents_and_size(bids):
            if not bids:
                return 0, 0
            top_entry = bids[-1] if isinstance(bids, list) else bids
            if isinstance(top_entry, list):
                price_val = top_entry[0]
                size_val = top_entry[1] if len(top_entry) > 1 else 0
            else:
                price_val = top_entry
                size_val = 0

            if isinstance(price_val, str) or float(price_val) <= 1.0:
                price_cents = int(round(float(price_val) * 100))
            else:
                price_cents = int(round(float(price_val)))
            try:
                size = int(round(float(size_val)))
            except (TypeError, ValueError):
                size = 0
            return price_cents, size

        best_yes_bid, best_yes_bid_size = get_top_bid_cents_and_size(yes_bids)
        best_no_bid, best_no_bid_size = get_top_bid_cents_and_size(no_bids)
        
        yes_ask = (100 - best_no_bid) if best_no_bid > 0 else 0
        no_ask = (100 - best_yes_bid) if best_yes_bid > 0 else 0

        # Depth available AT that ask price - a YES buy matches against the
        # resting NO bid (and vice versa), so the size on that opposite side's
        # top-of-book entry is exactly how many contracts you could fill here.
        yes_ask_depth = best_no_bid_size
        no_ask_depth = best_yes_bid_size

        # Market-wide volume floor - skips the WHOLE market this cycle if it's
        # too illiquid to trust the quoted price at all, independent of what's
        # sitting at the top of book right now. Fails open (doesn't block) if
        # the volume fetch itself fails, so a transient API hiccup here can't
        # freeze trading the way an expiration-check failure does.
        if LIQUIDITY_FILTER_ENABLED:
            market_volume = get_market_volume(market_ticker)
            if market_volume is not None and market_volume < MIN_MARKET_VOLUME_CONTRACTS:
                local_time_str = time.strftime('%I:%M:%S %p')
                print(f"[{local_time_str}] [LIQUIDITY FILTER] Skipping {market_ticker} - volume "
                      f"{market_volume} contracts is below the {MIN_MARKET_VOLUME_CONTRACTS} floor.")
                return

        # Compare against the last check to catch violent single-tick swings
        # (a "crash"/spike) before it can trigger a buy - update history
        # immediately so this always happens, even on early returns below.
        prev_prices = price_history.get(market_ticker)
        price_history[market_ticker] = {"yes_ask": yes_ask, "no_ask": no_ask}
        if prev_prices:
            yes_jump = abs(yes_ask - prev_prices["yes_ask"])
            no_jump = abs(no_ask - prev_prices["no_ask"])
            record_price_jump(max(yes_jump, no_jump))
        else:
            yes_jump = no_jump = 0
        record_price_sequence(market_ticker, yes_ask, no_ask)

        def yes_side_stable():
            if VELOCITY_FILTER_ENABLED and yes_jump > MAX_PRICE_JUMP_CENTS:
                print(f"--> [VELOCITY FILTER] Skipping YES buy - price jumped {yes_jump}\u00a2 since last "
                      f"check (> {MAX_PRICE_JUMP_CENTS}\u00a2 cap). Looks like a violent swing, not a stable trend.")
                return False
            if LIQUIDITY_FILTER_ENABLED and yes_ask_depth < MIN_BOOK_DEPTH_CONTRACTS:
                print(f"--> [LIQUIDITY FILTER] Skipping YES buy - only {yes_ask_depth} contract(s) at "
                      f"the top of book (< {MIN_BOOK_DEPTH_CONTRACTS} required). Book looks thin.")
                return False
            return True

        def no_side_stable():
            if VELOCITY_FILTER_ENABLED and no_jump > MAX_PRICE_JUMP_CENTS:
                print(f"--> [VELOCITY FILTER] Skipping NO buy - price jumped {no_jump}\u00a2 since last "
                      f"check (> {MAX_PRICE_JUMP_CENTS}\u00a2 cap). Looks like a violent swing, not a stable trend.")
                return False
            if LIQUIDITY_FILTER_ENABLED and no_ask_depth < MIN_BOOK_DEPTH_CONTRACTS:
                print(f"--> [LIQUIDITY FILTER] Skipping NO buy - only {no_ask_depth} contract(s) at "
                      f"the top of book (< {MIN_BOOK_DEPTH_CONTRACTS} required). Book looks thin.")
                return False
            return True

        local_time_str = time.strftime('%I:%M:%S %p')
        print(f"[{local_time_str}] Market: {market_ticker} | Time Left: {remaining_minutes:.1f}m | YES Ask: {yes_ask}¢ | NO Ask: {no_ask}¢")
        
        # 3. Check if already traded (with secondary exception override)
        if market_ticker in traded_tickers:
            sides_used_secondary = secondary_traded_sides.get(market_ticker, set())
            if remaining_minutes < SECONDARY_TIME_LIMIT:
                if yes_ask > SECONDARY_PRICE_CENTS and "yes" not in sides_used_secondary:
                    print(f"--> SECONDARY TRIGGER HIT! [< {SECONDARY_TIME_LIMIT}m & YES Ask {yes_ask}¢ > {SECONDARY_PRICE_CENTS}¢]. Buying 2 more shares...")
                    if yes_side_stable() and mood_allows_buy(market_ticker, "yes"):
                        execute_order(market_ticker, side="yes", price_cents=yes_ask, forced_count=5, is_secondary=True)
                    return
                elif no_ask > SECONDARY_PRICE_CENTS and "no" not in sides_used_secondary:
                    print(f"--> SECONDARY TRIGGER HIT! [< {SECONDARY_TIME_LIMIT}m & NO Ask {no_ask}¢ > {SECONDARY_PRICE_CENTS}¢]. Buying 2 more shares...")
                    if no_side_stable() and mood_allows_buy(market_ticker, "no"):
                        execute_order(market_ticker, side="no", price_cents=no_ask, forced_count=5, is_secondary=True)
                    return
            
            print(f"[{local_time_str}] Already traded {market_ticker}. Standing by...")
            return

        # 4. Standard Triggers for Fresh Markets
        is_early_zone = remaining_minutes > STANDARD_MAX_MINUTES
        required_threshold = EARLY_SPIKE_PRICE_CENTS if is_early_zone else NORMAL_TRIGGER_PRICE_CENTS
        zone_label = f"EARLY SPIKE EXCEPTION (Time > {STANDARD_MAX_MINUTES}m)" if is_early_zone else "STANDARD WINDOW"
        
        if yes_ask >= MULTI_SHARE_THRESHOLD:
            print(f"--> TRIGGER HIT! [MULTI-SHARE] YES Ask {yes_ask}¢ >= {MULTI_SHARE_THRESHOLD}¢. Buying {MULTI_SHARE_CONTRACT_COUNT} contracts...")
            if yes_side_stable() and mood_allows_buy(market_ticker, "yes"):
                execute_order(market_ticker, side="yes", price_cents=yes_ask, forced_count=MULTI_SHARE_CONTRACT_COUNT)
        elif no_ask >= MULTI_SHARE_THRESHOLD:
            print(f"--> TRIGGER HIT! [MULTI-SHARE] NO Ask {no_ask}¢ >= {MULTI_SHARE_THRESHOLD}¢. Buying {MULTI_SHARE_CONTRACT_COUNT} contracts...")
            if no_side_stable() and mood_allows_buy(market_ticker, "no"):
                execute_order(market_ticker, side="no", price_cents=no_ask, forced_count=MULTI_SHARE_CONTRACT_COUNT)
        elif yes_ask >= required_threshold:
            print(f"--> TRIGGER HIT! [{zone_label}] YES Ask {yes_ask}¢ >= {required_threshold}¢ target. Executing standard buy...")
            if yes_side_stable() and mood_allows_buy(market_ticker, "yes"):
                execute_order(market_ticker, side="yes", price_cents=yes_ask)
        elif no_ask >= required_threshold:
            print(f"--> TRIGGER HIT! [{zone_label}] NO Ask {no_ask}¢ >= {required_threshold}¢ target. Executing standard buy...")
            if no_side_stable() and mood_allows_buy(market_ticker, "no"):
                execute_order(market_ticker, side="no", price_cents=no_ask)
        else:
            print(f"--> Conditions not met. Standing by...")

    except Exception as e:
        print(f"--> [ERROR] Direct orderbook query failed for {market_ticker}: {e}")

def _position_monitor_loop():
    """Runs on its own clock (POSITION_CHECK_INTERVAL_SECONDS), independent of
    the slower main scan loop, so a losing position doesn't have to wait for
    a full 10-second buy-scan cycle before its stop-loss/take-profit is checked.

    NOTE: POSITION_CHECK_INTERVAL_SECONDS is the SLEEP between cycles, not the
    total cycle time - check_all_autosells() itself makes real HTTP calls, so
    a cycle can easily run several times longer than that sleep value alone.
    This matters directly for STOP_LOSS_CONFIRMATION_SECONDS, which now waits
    on actual elapsed wall-clock time (see check_autosell) rather than a count
    of assumed-0.1s ticks - so it stays accurate regardless of how slow a
    cycle actually runs. We log when a cycle runs unexpectedly slow so that's
    visible instead of silently eating into the confirmation window."""
    while True:
        cycle_start = time.time()
        try:
            check_all_autosells()
        except Exception as e:
            print(f"--> [ERROR] Position monitor thread hit an error (continuing): {e}")
        cycle_elapsed = time.time() - cycle_start
        if cycle_elapsed > POSITION_CHECK_INTERVAL_SECONDS * 3:
            print(f"--> [WARNING] Position check cycle took {cycle_elapsed:.2f}s (expected ~"
                  f"{POSITION_CHECK_INTERVAL_SECONDS:.2f}s) - API latency is eating into how "
                  f"quickly stop-loss/take-profit can react.")
        time.sleep(POSITION_CHECK_INTERVAL_SECONDS)

def _summary_alert_loop():
    """Checks periodically using actual exchange balances so restarts 
    or missed ticks never throw off your hourly/daily totals."""
    global _hourly_checkpoint_pnl, _hourly_checkpoint_time
    global _daily_checkpoint_pnl, _daily_checkpoint_time
    global daily_biggest_win, daily_biggest_win_ticker

    # Initialize checkpoints with actual account balance on startup
    initial_bal = get_kalshi_account_balance()
    if initial_bal is not None:
        _hourly_checkpoint_pnl = initial_bal
        _daily_checkpoint_pnl = initial_bal

    while True:
        try:
            current_bal = get_kalshi_account_balance()
            if current_bal is None:
                time.sleep(SUMMARY_CHECK_INTERVAL_SECONDS)
                continue

            now = time.time()

            # Hourly Check (aligned or rolling)
            if now - _hourly_checkpoint_time >= 3600:
                hourly_delta = current_bal - _hourly_checkpoint_pnl
                sign = "+" if hourly_delta >= 0 else ""
                send_alert(f"\U0001F4B8\U0001F4B8 - HOURLY PROFIT: {sign}${hourly_delta:.2f} | END OF HOUR TOTAL: ${current_bal:.2f}")
                _hourly_checkpoint_pnl = current_bal
                _hourly_checkpoint_time = now

            # Daily Check (24h)
            if now - _daily_checkpoint_time >= 86400:
                daily_delta = current_bal - _daily_checkpoint_pnl
                sign = "+" if daily_delta >= 0 else ""
                window_start_dt = datetime.fromtimestamp(_daily_checkpoint_time)

                with session_pnl_lock:
                    best_win = daily_biggest_win
                    best_win_ticker = daily_biggest_win_ticker

                daily_msg = f"\U0001F3AB\U0001F3AB - DAILY PROFIT: {sign}${daily_delta:.2f} | ON THE DAY TOTAL: ${current_bal:.2f}"
                if best_win > 0:
                    daily_msg += f"\n\U0001F3C6 Biggest win today: +${best_win:.2f} ({best_win_ticker})"
                send_alert(daily_msg)

                chart_path = _build_equity_curve_chart(window_start_dt)
                if chart_path:
                    send_photo(chart_path, caption=f"\U0001F4C8 Equity curve \u2013 {sign}${daily_delta:.2f} on the day")

                _daily_checkpoint_pnl = current_bal
                _daily_checkpoint_time = now

                with session_pnl_lock:
                    daily_biggest_win = 0.0
                    daily_biggest_win_ticker = None

        except Exception as e:
            print(f"--> [ERROR] Summary alert thread hit an error: {e}")
        time.sleep(SUMMARY_CHECK_INTERVAL_SECONDS)

def _get_telegram_updates(offset):
    """Polls Telegram for new messages sent to the bot since `offset`."""
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/getUpdates?offset={offset}&timeout=0"
    req = urllib.request.Request(url, method="GET")
    with urllib.request.urlopen(req, timeout=10) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return data.get("result", []) if data.get("ok") else []

def _build_status_message():
    real_pnl = get_session_pnl()
    with positions_lock:
        positions_snapshot = dict(open_positions)
        held_snapshot = set(held_positions)

    pause_until = _pause_until
    if trading_paused and pause_until is not None:
        resume_at = time.strftime('%I:%M %p', time.localtime(pause_until))
        status_label = f"\u23F8 PAUSED (auto-resumes {resume_at}, {_format_duration(max(0, pause_until - time.time()))} left)"
    elif trading_paused:
        status_label = "\u23F8 PAUSED"
    else:
        status_label = "\u25B6\uFE0F ACTIVE"
    lines = [
        "\U0001F4CA STATUS",
        f"Trading: {status_label}",
        f"Mood: {get_market_mood()}",
        f"Liquidity filter: {'ON' if LIQUIDITY_FILTER_ENABLED else 'OFF'} (min depth {MIN_BOOK_DEPTH_CONTRACTS} contracts, min volume {MIN_MARKET_VOLUME_CONTRACTS} contracts)",
        f"Trailing stop: {'ON' if TRAILING_STOP_ENABLED else 'OFF'} for positions > {TRAILING_STOP_MIN_CONTRACTS} contracts "
        f"(arms at ${TRAILING_STOP_ARM_DOLLARS:.2f}, trails ${TRAILING_STOP_TRAIL_DOLLARS:.2f})",
    ]
    if real_pnl is not None:
        lines.append(f"Session P/L (real balance): ${real_pnl:.2f}")
    else:
        with session_pnl_lock:
            fallback_total = session_realized_pnl
        lines.append(f"Session P/L: ${fallback_total:.2f} (couldn't verify live balance - this figure may be incomplete)")
        real_pnl = fallback_total

    if DAILY_LOSS_LIMIT_ENABLED:
        hit_limit = real_pnl <= -DAILY_LOSS_LIMIT_DOLLARS
        if loss_limit_overridden:
            lines.append("\u26A0\uFE0F Daily loss limit: OVERRIDDEN (safety net bypassed)")
        elif hit_limit:
            lines.append(f"\U0001F6D1 Daily loss limit HIT (-${DAILY_LOSS_LIMIT_DOLLARS:.2f}) - new trades blocked. Send /unlockloss to override.")
    if positions_snapshot:
        lines.append(f"Open positions ({len(positions_snapshot)}):")
        for ticker, pos in positions_snapshot.items():
            held_tag = " \u270B HELD" if ticker in held_snapshot else ""
            lines.append(f"  \u2022 {ticker}: {pos['side'].upper()} x{pos['count']} @ {pos['entry_price_cents']:.1f}\u00a2{held_tag}")
    else:
        lines.append("No open positions.")
    return "\n".join(lines)

def _format_uptime():
    elapsed = time.time() - bot_start_time
    days, remainder = divmod(int(elapsed), 86400)
    hours, remainder = divmod(remainder, 3600)
    minutes, _ = divmod(remainder, 60)
    parts = []
    if days:
        parts.append(f"{days}d")
    if hours:
        parts.append(f"{hours}h")
    parts.append(f"{minutes}m")
    return " ".join(parts)

def _format_duration(seconds):
    if seconds < 60:
        return f"{int(seconds)}s"
    mins = int(round(seconds / 60.0))
    if mins >= 60:
        hours, m = divmod(mins, 60)
        return f"{hours}h {m}m" if m else f"{hours}h"
    return f"{mins}m"

def _parse_duration_minutes(raw_text):
    """'/pausefor 30' -> 30.0, '/pausefor 45m' -> 45.0, '/pausefor 2h' -> 120.0.
    Returns None if missing/unparseable."""
    parts = raw_text.split()
    if len(parts) < 2:
        return None
    arg = parts[1].strip().lower()
    multiplier = 1.0
    if arg.endswith("h"):
        multiplier, arg = 60.0, arg[:-1]
    elif arg.endswith("m"):
        arg = arg[:-1]
    try:
        return float(arg) * multiplier
    except ValueError:
        return None

COINFLIP_WINNING_LINES = [
    "🎯 Mannnn, talk about a certified bucket. Real smooth.",
    "💨 Flew right past 'em like Bankhead traffic on a Friday.",
    "🏆 Mane, you really out here doing numbers. Put that on my mama.",
    "🔥 Whole screen looking like a forest. Straight green.",
    "💎 Shinin' for real. They gotta respect the architect.",
    "📈 Left 'em lookin' stupid out here. Clean work.",
    "🚀 Took off like an SRT on the Connector. Gone.",
    "💼 Real boss behavior. Ain't even gotta brag about it.",
    "⭐ Had that play dialed up better than a Zone 6 cookout.",
    "⚡ Quick bag, no lag. You cooked on that one.",
    "🧊 Glacier status. Didn't even break a sweat.",
    "🏆 They sliding down the charts while you stepping up. Sheesh.",
    "🔥 Bro, you serving these markets back-to-back.",
    "🧢 No cap in the P/L today, only trophies.",
    "💨 Zoomed right past the resistance. Clean getaway.",
    "👑 That's how you step on necks and take names.",
    "🎯 Hit the target so clean it left a echo.",
    "💎 Flawless execution. Put it in the Louvre.",
    "📈 Stacking it up higher than the Peachtree towers.",
    "🚀 Ain't nobody catching you once you get that momentum.",
    "🔥 They down bad trying to figure out your algorithm.",
    "💼 Heavy is the head that carries the bag. Go 'head then.",
    "⭐ Smooth operator. You in your bag for real.",
    "⚡ That was faster than getting through the Five Points station.",
    "🧊 Too cold for 'em. They need a jacket just looking at your screen.",
    "🏆 Another dub in the books. Print it out.",
    "🔥 You got the cheat codes to this shit, I swear.",
    "🎯 Sniper execution. Didn't even blink.",
    "📈 That balance lookin' healthy, mane. Big motion.",
    "👑 Crown stay heavy, wallet stay heavy. Period.",
]
COINFLIP_LOSING_LINES = [
   "🤦‍♂️ Mane, what was that? The market really played in your face.",
    "📉 Took a dirty L on that one. Dust yourself off, big dawg.",
    "🥷 Bro got fleeced by a 15-minute candle. Rough out here.",
    "🧊 Ice cold. That trade got sent straight to the shadow realm.",
    "💀 Market did you dirty, ngl. Take your lick and step.",
    "🌪️ Got spun like you was on a ride at Six Flags over GA.",
    "🛑 That drawdown lookin' nasty. Time to chill for a minute.",
    "👟 Tripped over your own feet on that play. Happens.",
    "🗑️ Toss that trade in the bin and don't look back.",
    "🤡 Market really made a meme out of us on that candle.",
    "🌧️ Rainy day on the portfolio. Grab an umbrella.",
    "🤦‍♂️ Bro stepped right in the pothole. Right in broad daylight.",
    "📉 Tanked harder than the Falcons in the fourth quarter. Sheesh.",
    "🧊 Got put in the freezer on that one. Chill out for a sec.",
    "💀 That trade was dead on arrival, my boy.",
    "🌪️ Swept away by the Feds and the market makers. Damn.",
    "🛑 Pause, reset, and re-evaluate before you do that again.",
    "👟 Stumbled out the blocks. Fix your stance.",
    "🗑️ Put that L in recycling and go watch some anime or something.",
    "🤡 They really ran it up on us. Unbelievable.",
    "🌧️ Dark clouds on the terminal tonight. It be like that.",
    "🤦‍♂️ Mane, you handed 'em that bread on a silver platter.",
    "📉 Redder than a Zone 3 stop sign. Damn.",
    "🧊 Frozen out. The algorithm said 'not today, patna.'",
    "💀 Straight violation by the candles. No Vaseline.",
    "🌪️ Tornado touched down on the account. Hold on tight.",
    "🛑 Sit down somewhere and let the market breathe for a sec.",
    "👟 Tied your shoes together on that one, didn't you?",
    "🗑️ Throw the whole session away. Start fresh tomorrow.",
    "🤡 Clown behavior from the chart. We getting that back though.",
]
COINFLIP_NEUTRAL_LINES = [
    "💤 Dead quiet. Account moving slower than traffic on I-285 at 5 PM.",
    "🛋️ Sitting pretty doing a whole lot of nothing. It's a vibe.",
    "🧊 Lukewarm. Not hot, not cold, just sitting there.",
    "🥱 Chart flatter than a Waffle House parking lot at 3 AM.",
    "🧘‍♂️ Unbothered. Let the candles do whatever they wanna do.",
    "⚖️ Stuck in neutral. Like driving with the emergency brake on.",
    "👀 Just peeping the charts. No moves, just surveillance.",
    "💨 Breezin' by. Zero gains, zero pain.",
    "⏳ Marinating. Good things take time, or whatever.",
    "😴 Bot is sleep. Honestly, me too.",
    "🛋️ Lounging. The market's moving at the speed of a dead snail.",
    "🧊 Ice hasn't even melted. That's how still this line is.",
    "🥱 Yawning at the terminal. Give us some volatility, damn.",
    "🧘‍♂️ Pure zen mode. We ain't forcing shit today.",
    "⚖️ Perfectly balanced on zero. Impressively lazy.",
    "👀 Staring at the screen like it's gon' move on its own.",
    "💨 Just drifting. Floating in the middle lane.",
    "⏳ Waiting for the beat to drop. This intro is taking forever.",
    "😴 Zzz... wake me up when a candle actually does something.",
    "🛋️ Kick your feet up. Nothing to see here.",
    "🧊 Chill mode activated. P/L locked in stasis.",
    "🥱 This market got less energy than a Monday morning class.",
    "🧘‍♂️ Let 'em figure it out. We staying on the porch.",
    "⚖️ Dead center. Not even a blip on the radar.",
    "👀 Watching the paint dry on these 15-minute intervals.",
    "💨 Smooth sailing on a flat lake. Nothing shaking.",
    "⏳ Playing the waiting game. Real mob boss patience.",
    "😴 Even the bot clocked out early on this one.",
    "🛋️ kicked back in the recliner. The numbers are frozen.",
    "🧊 Cold, calm, and completely stuck in place.",
]

HELP_MESSAGE = (
    "\U0001F4CB AVAILABLE COMMANDS\n"
    "/status - open positions + session P/L + mood\n"
    "/balance - live Kalshi account balance\n"
    "/pnl - current session P/L\n"
    "/stats - all-time stats (survives restarts)\n"
    "/mood - current market volatility read\n"
    "/uptime - how long the bot has been running\n"
    "/history - your last 20 completed trades\n"
    "/wins - today's winning trades and how much each paid\n"
    "/expectancy [n] - win rate, avg win/loss, break-even win rate (optionally just the last n trades)\n"
    "/stops - stop-loss post-mortem: would holding have been better?\n"
    "/log - last 20 lines of console output, remotely\n"
    "/coinflip - a random line based on your current P/L, for fun\n"
    "/savepreset <name> - save current config as a named preset\n"
    "/loadpreset <name> - load a saved preset (survives restarts)\n"
    "/presets - list saved preset names\n"
    "/deletepreset <name> - delete a saved preset\n"
    "/settings - current budget/profit/stop-loss/limit config\n"
    "/pause - stop opening new positions (existing ones still managed)\n"
    "/pausefor <time> - timed pause that auto-resumes, e.g. 30, 45m, 2h (max 24h)\n"
    "/resume - resume opening new positions\n"
    "/unlockloss - override a tripped daily loss limit (use with care)\n"
    "/relock - re-arm the daily loss limit after overriding it\n"
    "/sell [ticker] - force-close a position now, any P/L (ticker optional if only one open)\n"
    "/hold [ticker] - exempt one position from auto take-profit/stop-loss\n"
    "/unhold [ticker] - hand a held position back to automation\n"
    "/setbudget <amt> - change budget per trade\n"
    "/setprofit <amt> - change take-profit target\n"
    "/setstoploss <amt> - change stop-loss amount\n"
    "/setlosslimit <amt> - change daily loss limit\n"
    "/setmultishare <count> - change multi-share trigger contract count\n"
    "/setthreshold <name> <value> - change a time/price trigger threshold\n"
    "/autosell on|off - toggle take-profit auto-sell\n"
    "/stoploss on|off - toggle stop-loss (use with care)\n"
    "/nightmode on|off - switch budget/profit/stop-loss/limit/thresholds to night values\n"
    "/help - this message"
)

def _resolve_target_ticker(raw_text):
    """Parses an optional ticker from a command like '/sell TICKER'. If none
    given, defaults to the single open position if there's exactly one.
    Returns (ticker, None) on success, or (None, error_message) on failure.
    Uses the ORIGINAL-case text since Kalshi tickers are uppercase and
    open_positions keys are case-sensitive."""
    parts = raw_text.split()
    if len(parts) >= 2:
        return parts[1].strip(), None
    with positions_lock:
        tickers = list(open_positions.keys())
    if len(tickers) == 1:
        return tickers[0], None
    elif len(tickers) == 0:
        return None, "No open positions right now."
    else:
        ticker_list = "\n".join(f"  \u2022 {t}" for t in tickers)
        return None, f"Multiple open positions - specify which:\n{ticker_list}"

def _parse_float_arg(raw_text):
    parts = raw_text.split()
    if len(parts) < 2:
        return None
    try:
        return float(parts[1])
    except ValueError:
        return None

def _telegram_command_loop():
    """Polls Telegram for incoming messages and handles remote-control
    commands. Only processes messages from TELEGRAM_CHAT_ID - anything else
    is ignored."""
    global trading_paused, loss_limit_overridden, _telegram_update_offset
    global _pause_until, _loss_limit_alerted
    global BUDGET_DOLLARS, PROFIT_TARGET_DOLLARS, STOP_LOSS_DOLLARS, DAILY_LOSS_LIMIT_DOLLARS
    global AUTOSELLING, STOP_LOSS_ENABLED, MULTI_SHARE_CONTRACT_COUNT, night_mode_active

    while True:
        try:
            _auto_resume_if_pause_expired()
            updates = _get_telegram_updates(_telegram_update_offset)
            for update in updates:
                _telegram_update_offset = update["update_id"] + 1
                message = update.get("message", {})
                sender_chat_id = str(message.get("chat", {}).get("id", ""))
                if sender_chat_id != str(TELEGRAM_CHAT_ID):
                    continue  # ignore anyone who isn't the configured owner

                raw_text = (message.get("text") or "").strip()  # original case - needed for tickers
                text = raw_text.lower()  # lowercased - used for command matching only

                if text == "/status":
                    send_alert(_build_status_message())
                elif text == "/balance":
                    balance = get_kalshi_account_balance()
                    if balance is not None:
                        send_alert(f"\U0001F4B5 Kalshi balance: ${balance:.2f}")
                    else:
                        send_alert("\u26A0\uFE0F Couldn't fetch balance right now - try again shortly.")
                elif text == "/pnl":
                    real_pnl = get_session_pnl()
                    if real_pnl is not None:
                        send_alert(f"\U0001F4B0 Session P/L: ${real_pnl:.2f}")
                    else:
                        with session_pnl_lock:
                            fallback = session_realized_pnl
                        send_alert(f"\U0001F4B0 Session P/L: ${fallback:.2f} (fallback - live balance check failed)")
                elif text == "/stats":
                    with stats_lock:
                        s = dict(all_time_stats)
                    win_rate = (s["total_wins"] / s["total_trades"] * 100) if s["total_trades"] > 0 else 0.0
                    stats_msg = (
                        "\U0001F4C8 ALL-TIME STATS\n"
                        f"Lifetime P/L: ${s['lifetime_pnl']:.2f}\n"
                        f"Total trades: {s['total_trades']} | Win rate: {win_rate:.0f}%\n"
                        f"Longest win streak: {s['longest_win_streak']}\n"
                        f"Current streak: {s['current_streak_count']} {s['current_streak_type'] or 'n/a'}"
                    )
                    if s["best_day"]["date"]:
                        stats_msg += f"\nBest day: {s['best_day']['date']} (${s['best_day']['pnl']:.2f})"
                    if s["worst_day"]["date"]:
                        stats_msg += f"\nWorst day: {s['worst_day']['date']} (${s['worst_day']['pnl']:.2f})"
                    send_alert(stats_msg)
                elif text == "/mood":
                    send_alert(f"Market mood: {get_market_mood()}")
                elif text == "/uptime":
                    send_alert(f"\u23B1 Uptime: {_format_uptime()}")

                elif text == "/history":
                    log = _load_trade_log()
                    recent = log[-20:]
                    if not recent:
                        send_alert("No completed trades recorded yet.")
                    else:
                        hist_lines = [f"\U0001F4DC LAST {len(recent)} TRADES"]
                        for entry in reversed(recent):  # most recent first
                            try:
                                t = datetime.fromisoformat(entry["timestamp"]).strftime("%m/%d %I:%M %p")
                            except (ValueError, KeyError):
                                t = "??/?? ??:??"
                            amt = entry.get("amount", 0.0)
                            sign = "+" if amt >= 0 else ""
                            hist_lines.append(f"{t} {sign}${amt:.2f} {entry.get('ticker', '?')}")
                        send_alert("\n".join(hist_lines))

                elif text == "/wins":
                    today_str = datetime.now().strftime("%Y-%m-%d")
                    log = _load_trade_log()
                    todays_wins = [
                        e for e in log
                        if e.get("timestamp", "").startswith(today_str) and e.get("amount", 0) > 0
                    ]
                    if not todays_wins:
                        send_alert("No wins recorded yet today.")
                    else:
                        win_lines = [f"\U0001F3C6 WINS TODAY ({len(todays_wins)})"]
                        total = 0.0
                        for e in todays_wins:
                            try:
                                t = datetime.fromisoformat(e["timestamp"]).strftime("%I:%M %p")
                            except (ValueError, KeyError):
                                t = "??:??"
                            win_lines.append(f"  {t} +${e['amount']:.2f} {e.get('ticker', '?')}")
                            total += e["amount"]
                        win_lines.append(f"Total: +${total:.2f}")
                        send_alert("\n".join(win_lines))

                elif text.startswith("/expectancy"):
                    parts = raw_text.split()
                    last_n = None
                    if len(parts) >= 2:
                        try:
                            last_n = int(parts[1])
                        except ValueError:
                            last_n = 0
                        if last_n <= 0:
                            send_alert("Usage: /expectancy or /expectancy <last N trades>, e.g. /expectancy 50")
                            continue
                    send_alert(_build_expectancy_message(last_n))

                elif text == "/stops":
                    send_alert(_build_stops_message())

                elif text == "/log":
                    with console_log_lock:
                        recent_lines = list(console_log_buffer)[-20:]
                    if not recent_lines:
                        send_alert("No log output captured yet.")
                    else:
                        trimmed = [line[:150] for line in recent_lines]
                        send_alert("\U0001F5A5 LAST 20 LOG LINES\n" + "\n".join(trimmed))

                elif text == "/coinflip":
                    real_pnl = get_session_pnl()
                    if real_pnl is None:
                        with session_pnl_lock:
                            real_pnl = session_realized_pnl
                    if real_pnl > 0.01:
                        line = random.choice(COINFLIP_WINNING_LINES)
                    elif real_pnl < -0.01:
                        line = random.choice(COINFLIP_LOSING_LINES)
                    else:
                        line = random.choice(COINFLIP_NEUTRAL_LINES)
                    send_alert(f"{line}\n(Session P/L: ${real_pnl:.2f})")

                elif text.startswith("/savepreset"):
                    parts = raw_text.split()
                    if len(parts) < 2:
                        send_alert("Usage: /savepreset <name>, e.g. /savepreset aggressive")
                        continue
                    preset_name = parts[1].strip().lower()
                    presets = _load_presets()
                    presets[preset_name] = {field: globals()[field] for field in PRESET_FIELDS}
                    _save_presets(presets)
                    send_alert(f"\U0001F4BE Saved current config as preset '{preset_name}'.")

                elif text.startswith("/loadpreset"):
                    parts = raw_text.split()
                    if len(parts) < 2:
                        send_alert("Usage: /loadpreset <name>, e.g. /loadpreset aggressive")
                        continue
                    preset_name = parts[1].strip().lower()
                    presets = _load_presets()
                    if preset_name not in presets:
                        available = ", ".join(presets.keys()) or "(none saved yet)"
                        send_alert(f"No preset named '{preset_name}'. Available: {available}")
                        continue
                    preset_values = presets[preset_name]
                    for field, value in preset_values.items():
                        globals()[field] = value
                        _save_config_override(field, value)
                    summary = ", ".join(f"{k}={v}" for k, v in preset_values.items())
                    send_alert(f"\U0001F4C2 Loaded preset '{preset_name}'.\n{summary}\nSaved - survives restarts.")

                elif text == "/presets":
                    presets = _load_presets()
                    if not presets:
                        send_alert("No presets saved yet. Use /savepreset <name> to create one.")
                    else:
                        send_alert("\U0001F4C1 Saved presets: " + ", ".join(presets.keys()))

                elif text.startswith("/deletepreset"):
                    parts = raw_text.split()
                    if len(parts) < 2:
                        send_alert("Usage: /deletepreset <name>")
                        continue
                    preset_name = parts[1].strip().lower()
                    presets = _load_presets()
                    if preset_name in presets:
                        del presets[preset_name]
                        _save_presets(presets)
                        send_alert(f"\U0001F5D1 Deleted preset '{preset_name}'.")
                    else:
                        send_alert(f"No preset named '{preset_name}'.")

                elif text == "/settings":
                    night_label = "\U0001F319 ON" if night_mode_active else "\u2600\uFE0F OFF"
                    settings_msg = (
                        "\u2699\uFE0F CURRENT SETTINGS\n"
                        f"Budget per trade: ${BUDGET_DOLLARS:.2f}\n"
                        f"Take-profit target: ${PROFIT_TARGET_DOLLARS:.2f} {'(OFF)' if not AUTOSELLING else ''}\n"
                        f"Stop-loss: ${STOP_LOSS_DOLLARS:.2f} {'(OFF)' if not STOP_LOSS_ENABLED else ''}\n"
                        f"Stop-loss confirmation: {STOP_LOSS_CONFIRMATION_SECONDS}s "
                        f"(if <{STOP_LOSS_CONFIRMATION_TIME_THRESHOLD_MINUTES}m left)\n"
                        f"Daily loss limit: ${DAILY_LOSS_LIMIT_DOLLARS:.2f}"
                        f"{' (OVERRIDDEN)' if loss_limit_overridden else ''}\n"
                        f"Mode: {'DEMO' if DEMO_MODE else 'LIVE'}\n"
                        f"Night mode: {night_label}\n"
                        "--- Triggers ---\n"
                        f"Standard/hard time caps: {STANDARD_MAX_MINUTES}m / {HARD_ABSOLUTE_MAX_MINUTES}m\n"
                        f"Early spike / normal price: {EARLY_SPIKE_PRICE_CENTS}\u00a2 / {NORMAL_TRIGGER_PRICE_CENTS}\u00a2\n"
                        f"Multi-share threshold: {MULTI_SHARE_THRESHOLD}\u00a2 \u2192 {MULTI_SHARE_CONTRACT_COUNT} contracts\n"
                        f"Secondary time/price: <{SECONDARY_TIME_LIMIT}m & {SECONDARY_PRICE_CENTS}\u00a2\n"
                        f"Velocity filter: {'ON' if VELOCITY_FILTER_ENABLED else 'OFF'} (max jump {MAX_PRICE_JUMP_CENTS}\u00a2)"
                    )
                    send_alert(settings_msg)
                elif text in ("/help", "/start"):
                    send_alert(HELP_MESSAGE)
                elif text == "/pause":
                    with _pause_lock:
                        _pause_until = None  # indefinite - cancels any running timer
                        trading_paused = True
                    send_alert("\u23F8 Trading PAUSED - no new positions will be opened. "
                                "Existing positions are still managed normally. Send /resume to continue.")
                elif text.startswith("/pausefor"):
                    minutes = _parse_duration_minutes(raw_text)
                    if minutes is None or not (0 < minutes <= 1440):
                        send_alert("Usage: /pausefor <time>, e.g. /pausefor 30, /pausefor 45m, /pausefor 2h "
                                   "(up to 24h - use /pause for open-ended).")
                        continue
                    with _pause_lock:
                        _pause_until = time.time() + minutes * 60
                        trading_paused = True
                    resume_at = time.strftime('%I:%M %p', time.localtime(_pause_until))
                    send_alert(f"\u23F8 Trading PAUSED for {_format_duration(minutes * 60)} - auto-resumes at {resume_at}. "
                               f"No new positions until then; existing ones are still managed normally. "
                               f"Send /resume to end it early.")
                elif text == "/resume":
                    with _pause_lock:
                        trading_paused = False
                        _pause_until = None
                    send_alert("\u25B6\uFE0F Trading RESUMED.")
                elif text == "/unlockloss":
                    real_pnl = get_session_pnl()
                    pnl_display = f"${real_pnl:.2f}" if real_pnl is not None else "unknown (balance check failed)"
                    loss_limit_overridden = True
                    send_alert(f"\u26A0\uFE0F Daily loss limit OVERRIDDEN. Current session P/L ({pnl_display}) "
                                f"is past the -${DAILY_LOSS_LIMIT_DOLLARS:.2f} limit, but new trades will resume "
                                f"anyway. This bypasses your safety net until you send /relock or restart the bot.")
                elif text == "/relock":
                    loss_limit_overridden = False
                    _loss_limit_alerted = False  # if still past the limit, the alert fires again right away
                    send_alert(f"\U0001F512 Daily loss limit RE-ARMED (-${DAILY_LOSS_LIMIT_DOLLARS:.2f}). "
                                f"New trades will halt again if session P/L is already past it.")

                elif text.startswith("/sell"):
                    ticker, err = _resolve_target_ticker(raw_text)
                    if err:
                        send_alert(err)
                        continue
                    with positions_lock:
                        position = open_positions.get(ticker)
                    if not position:
                        send_alert(f"No open position found for {ticker}.")
                        continue
                    current_bid = get_position_bid_price(ticker, position["side"])
                    if current_bid is None or current_bid <= 0:
                        send_alert(f"\u26A0\uFE0F Couldn't get a live price for {ticker} - try again in a moment.")
                        continue
                    filled = execute_sell_order(ticker, position["side"], current_bid, position["count"])
                    _apply_fill_to_position(ticker, filled, sell_price_cents=current_bid, reason="Manual sell")
                    with positions_lock:
                        held_positions.discard(ticker)
                    if filled and filled > 0:
                        send_alert(f"\U0001F4B8 Manually sold {filled} of {position['count']} {ticker} @ {current_bid}\u00a2 (via /sell).")
                    else:
                        send_alert(f"\u26A0\uFE0F /sell for {ticker} didn't fill (price may have moved) - it'll keep retrying, or send /sell again.")

                elif text.startswith("/unhold"):
                    ticker, err = _resolve_target_ticker(raw_text)
                    if err:
                        send_alert(err)
                        continue
                    with positions_lock:
                        was_held = ticker in held_positions
                        held_positions.discard(ticker)
                    if was_held:
                        send_alert(f"\u2705 {ticker} handed back to automatic take-profit/stop-loss management.")
                    else:
                        send_alert(f"{ticker} wasn't being held.")

                elif text.startswith("/hold"):
                    ticker, err = _resolve_target_ticker(raw_text)
                    if err:
                        send_alert(err)
                        continue
                    with positions_lock:
                        exists = ticker in open_positions
                        if exists:
                            held_positions.add(ticker)
                    if exists:
                        send_alert(f"\u270B Holding {ticker} - automatic stop-loss/take-profit disabled for this "
                                    f"position ONLY. Other positions are unaffected. Send /unhold {ticker} or "
                                    f"/sell {ticker} to end this.")
                    else:
                        send_alert(f"No open position found for {ticker}.")

                elif text.startswith("/setbudget"):
                    val = _parse_float_arg(raw_text)
                    if val is None or val <= 0:
                        send_alert("Usage: /setbudget <amount>, e.g. /setbudget 20")
                    else:
                        BUDGET_DOLLARS = val
                        _save_config_override("BUDGET_DOLLARS", val)
                        send_alert(f"\u2705 Budget per trade set to ${val:.2f}. Applies to future trades only. "
                                    f"Saved - survives restarts.")

                elif text.startswith("/setprofit"):
                    val = _parse_float_arg(raw_text)
                    if val is None or val <= 0:
                        send_alert("Usage: /setprofit <amount>, e.g. /setprofit 2")
                    else:
                        PROFIT_TARGET_DOLLARS = val
                        _save_config_override("PROFIT_TARGET_DOLLARS", val)
                        send_alert(f"\u2705 Take-profit target set to ${val:.2f}. Saved - survives restarts.")

                elif text.startswith("/setstoploss"):
                    val = _parse_float_arg(raw_text)
                    if val is None or val <= 0:
                        send_alert("Usage: /setstoploss <amount>, e.g. /setstoploss 5")
                    else:
                        STOP_LOSS_DOLLARS = val
                        _save_config_override("STOP_LOSS_DOLLARS", val)
                        send_alert(f"\u2705 Stop-loss set to ${val:.2f}. Saved - survives restarts.")

                elif text.startswith("/setlosslimit"):
                    val = _parse_float_arg(raw_text)
                    if val is None or val <= 0:
                        send_alert("Usage: /setlosslimit <amount>, e.g. /setlosslimit 10")
                    else:
                        DAILY_LOSS_LIMIT_DOLLARS = val
                        _save_config_override("DAILY_LOSS_LIMIT_DOLLARS", val)
                        send_alert(f"\u2705 Daily loss limit set to ${val:.2f}. Saved - survives restarts.")

                elif text.startswith("/setmultishare"):
                    val = _parse_float_arg(raw_text)
                    if val is None or val <= 0 or val != int(val):
                        send_alert("Usage: /setmultishare <whole number>, e.g. /setmultishare 25")
                    else:
                        MULTI_SHARE_CONTRACT_COUNT = int(val)
                        _save_config_override("MULTI_SHARE_CONTRACT_COUNT", MULTI_SHARE_CONTRACT_COUNT)
                        send_alert(f"\u2705 Multi-share trigger now buys {MULTI_SHARE_CONTRACT_COUNT} contracts. "
                                    f"Applies to future triggers only, not anything already open. Saved - survives restarts.")

                elif text.startswith("/setthreshold"):
                    parts = raw_text.split()
                    if len(parts) < 3:
                        send_alert("Usage: /setthreshold <name> <value>\nNames (full names also work): " + ", ".join(THRESHOLD_SHORT_NAMES))
                        continue
                    name_key = parts[1].strip().lower()
                    value_str = parts[2].strip()
                    if name_key not in EDITABLE_THRESHOLDS:
                        send_alert(f"Unknown threshold '{name_key}'.\nNames: " + ", ".join(THRESHOLD_SHORT_NAMES))
                        continue
                    global_name = EDITABLE_THRESHOLDS[name_key]
                    if global_name in ("VELOCITY_FILTER_ENABLED", "LIQUIDITY_FILTER_ENABLED", "TRAILING_STOP_ENABLED"):
                        if value_str.lower() in ("on", "true", "1", "yes"):
                            parsed_value = True
                        elif value_str.lower() in ("off", "false", "0", "no"):
                            parsed_value = False
                        else:
                            send_alert(f"{name_key} must be on/off.")
                            continue
                    else:
                        try:
                            parsed_value = float(value_str)
                        except ValueError:
                            send_alert(f"'{value_str}' isn't a valid number.")
                            continue
                    globals()[global_name] = parsed_value
                    _save_config_override(global_name, parsed_value)
                    send_alert(f"\u2705 {global_name} set to {parsed_value}. Applies to future checks only. Saved - survives restarts.")

                elif text == "/autosell on":
                    AUTOSELLING = True
                    _save_config_override("AUTOSELLING", True)
                    send_alert("\u2705 Take-profit auto-sell ENABLED. Saved - survives restarts.")
                elif text == "/autosell off":
                    AUTOSELLING = False
                    _save_config_override("AUTOSELLING", False)
                    send_alert("\u26A0\uFE0F Take-profit auto-sell DISABLED. Winning positions will ride to "
                                "expiration instead of being sold early. Saved - survives restarts.")

                elif text == "/stoploss on":
                    STOP_LOSS_ENABLED = True
                    _save_config_override("STOP_LOSS_ENABLED", True)
                    send_alert("\u2705 Stop-loss ENABLED. Saved - survives restarts.")
                elif text == "/stoploss off":
                    STOP_LOSS_ENABLED = False
                    _save_config_override("STOP_LOSS_ENABLED", False)
                    send_alert("\u26A0\uFE0F Stop-loss DISABLED. Losing positions will have NO downside "
                                "protection and can ride to a full loss. This removes your safety net. "
                                "Saved - survives restarts.")

                elif text == "/nightmode on":
                    night_mode_active = True
                    for gname, pair in DAY_NIGHT_VALUES.items():
                        globals()[gname] = pair["night"]
                        _save_config_override(gname, pair["night"])
                    _save_config_override("night_mode_active", True)
                    summary = ", ".join(f"{n}={p['night']}" for n, p in DAY_NIGHT_VALUES.items())
                    send_alert(f"\U0001F319 Night mode ON.\n{summary}\nSaved - survives restarts.")

                elif text == "/nightmode off":
                    night_mode_active = False
                    for gname, pair in DAY_NIGHT_VALUES.items():
                        globals()[gname] = pair["day"]
                        _save_config_override(gname, pair["day"])
                    _save_config_override("night_mode_active", False)
                    summary = ", ".join(f"{n}={p['day']}" for n, p in DAY_NIGHT_VALUES.items())
                    send_alert(f"\u2600\uFE0F Night mode OFF (day settings).\n{summary}\nSaved - survives restarts.")

        except Exception as e:
            print(f"--> [ERROR] Telegram command thread hit an error (continuing): {e}")
        time.sleep(TELEGRAM_COMMAND_POLL_INTERVAL_SECONDS)

if __name__ == "__main__":
    _apply_saved_overrides()

    print(f"Kalshi Bot Online | Mode: {'DEMO/SANDBOX' if DEMO_MODE else 'LIVE TRADING'} | Target Per Trade: ${BUDGET_DOLLARS:.2f}")
    if DAILY_LOSS_LIMIT_ENABLED:
        print(f"--> Session loss limit: -${DAILY_LOSS_LIMIT_DOLLARS:.2f} (new positions halt if hit; open positions still managed)")

    session_start_balance = get_kalshi_account_balance()
    if session_start_balance is not None:
        print(f"--> Starting balance captured: ${session_start_balance:.2f} (used as the real baseline for session P/L)")
    else:
        print("--> [WARNING] Could not fetch starting balance - session P/L reporting will fall back to the internal tracker until this succeeds.")

    monitor_thread = threading.Thread(target=_position_monitor_loop, daemon=True)
    monitor_thread.start()
    print(f"--> Position monitor thread started (checking open positions every {POSITION_CHECK_INTERVAL_SECONDS}s).")

    if ALERTS_ENABLED:
        push_thread = threading.Thread(target=_push_alert_worker, daemon=True)
        push_thread.start()
        print("--> Push alerts enabled (buys, take-profit, stop-loss, settlements, loss-limit trip).")

        summary_thread = threading.Thread(target=_summary_alert_loop, daemon=True)
        summary_thread.start()
        print("--> Hourly/daily P/L summary alerts enabled.")

        command_thread = threading.Thread(target=_telegram_command_loop, daemon=True)
        command_thread.start()
        print("--> Telegram remote control enabled (/status, /pause, /resume).")

        send_alert(f"\U0001F4B0\U0001F4B3 - Started Trading | Mode: {'DEMO' if DEMO_MODE else 'LIVE'} | Current Budget: ${BUDGET_DOLLARS:.2f}")
    try:
        #transfer_shard_funds()
        while True:
            now_utc = datetime.now(pytz.UTC)
            market_ticker = None

            if (_active_market_cache["ticker"] and _active_market_cache["close_time"]
                    and now_utc < _active_market_cache["close_time"]):
                # Still the same active market as last cycle - skip re-resolving
                # the event/market ticker entirely and go straight to the price check.
                market_ticker = _active_market_cache["ticker"]
            else:
                event_ticker = get_current_event_ticker()
                resolved_ticker, close_time_hint = get_active_market_strike_ticker(event_ticker)
                if resolved_ticker:
                    close_time = _get_cached_close_time(resolved_ticker, close_time_hint)
                    market_ticker = resolved_ticker
                    _active_market_cache["ticker"] = resolved_ticker
                    _active_market_cache["close_time"] = close_time

            if market_ticker:
                check_market_and_trade(market_ticker)
            else:
                local_time_str = time.strftime('%I:%M:%S %p')
                print(f"[{local_time_str}] Looking up active market for event {event_ticker}...")

            time.sleep(0.5)
            
    except KeyboardInterrupt:
        final_pnl = get_session_pnl()
        pnl_display = f"${final_pnl:.2f}" if final_pnl is not None else f"${session_realized_pnl:.2f} (internal tracker - balance check failed)"
        print(f"\nBot shut down safely. Final session P/L: {pnl_display}")