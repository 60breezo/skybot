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
import math
from collections import deque
import threading
import queue
warnings.filterwarnings("ignore", category=Warning)

import time
import uuid
from datetime import datetime, timedelta
from decimal import Decimal
import urllib.request
import urllib.error
import urllib.parse
import http.client
import ssl
import gzip
import io
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
try:
    import websocket as _ws_lib   # pip package: websocket-client. Only needed for the Pyth metals/natgas feed below -
    _WS_LIB_ERROR = None          # everything else in this file (orders, CF Benchmarks) is plain REST and doesn't need it.
except ImportError as _e:
    _ws_lib = None
    _WS_LIB_ERROR = str(_e)

# --- MY API CREDENTIALS ---
KEY_ID = "YOUR_KALSHI_API_KEY_ID"
# --- CONSOLE OUTPUT CAPTURE (for /log) ---
# Mirrors everything printed to the terminal into a rolling in-memory buffer,
# so /log can send recent output over Telegram without needing SSH/terminal
# access to the machine at all.
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

# --- QUIET LOGGING ---
# The scan loops run every ~0.5s, so a plain print() floods the console with the
# same line over and over. log_smart() prints a line only when something about it
# actually changed (sig), or at most every `interval` seconds as a heartbeat.
# min_gap rate-limits change-triggered prints so a flickering price can't spam.
_log_state = {}
_log_state_lock = threading.Lock()

def log_smart(key, msg, sig=None, interval=15.0, min_gap=0.0):
    now = time.time()
    sig = msg if sig is None else sig
    with _log_state_lock:
        last = _log_state.get(key)
        if last is not None:
            last_sig, last_ts = last
            elapsed = now - last_ts
            if sig == last_sig and elapsed < interval:
                return False
            if sig != last_sig and elapsed < min_gap:
                return False
        _log_state[key] = (sig, now)
        if len(_log_state) > 500:
            for k in [k for k, v in _log_state.items() if now - v[1] > 600]:
                _log_state.pop(k, None)
    print(msg)
    return True
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
# CENTS-BASED take-profit (0 = OFF). Sells the whole position the moment the bid
# on the side you hold reaches this many cents and you're not under water.
# WHY IT EXISTS: PROFIT_TARGET_DOLLARS can't fire on entries near 98-99c - the
# bid tops out at 99c, so the most a position can make BEFORE settlement is
# (99 - entry) x contracts. At ~98.2c entry x 25 contracts that's $0.20, so a
# $0.28 target is mathematically unreachable and the position just rides to
# settlement. A cents trigger fits the price range these trades live in.
# Trade-off: you give up the last ~1c, but you stop carrying the reversal risk
# (holding a 99c bid only pays if it wins >99% of the time). /tpbid <cents|off>
TAKE_PROFIT_BID_CENTS = 0

# For LARGE positions only, use a trailing stop instead of the fixed
# PROFIT_TARGET_DOLLARS above: once profit reaches the arm level, track the
# best profit seen and sell if it pulls back by the trail amount, rather than
# selling flat the instant the target is first touched. Small positions are
# unaffected and keep the exact fixed-target behavior above.
TRAILING_STOP_ENABLED = False
TRAILING_STOP_MIN_CONTRACTS = 20  # only positions with MORE than this many contracts use the trailing stop; count is checked live, so a position that grows past this via a multi-share/secondary add picks it up automatically
TRAILING_STOP_ARM_DOLLARS = 0.28  # unrealized profit at which trailing takes over (starts equal to PROFIT_TARGET_DOLLARS's current default; tune independently)
TRAILING_STOP_TRAIL_DOLLARS = 0.22  # how far profit can fall back from its peak before selling - untested starting guess, tune against logged data

# METALS/CRYPTO/ENERGY MODE SWITCH - exactly one series trades at a time.
# Default is Bitcoin; /goldmode, /silvermode, /platinummode, /palladiummode, /ethereummode
# (or /ethmode), /solanamode (or /solmode), /naturalgasmode (or /gasmode,
# /natgasmode) - each on|off - switch which one.
# Turning one ON turns the others OFF, so there's never ambiguity about which
# series is active. All series share the same KX{NAME}15M-{date}{time} ticker
# format, so one ACTIVE_SERIES_TICKER variable drives market lookup everywhere
# (see get_current_event_ticker). Every series listed in ALL_SERIES_TICKERS is
# also a candidate for the cross-series early-resolve hop (see
# find_cross_series_candidate).
SERIES_TICKER_BTC = "KXBTC15M"
SERIES_TICKER_ETH = "KXETH15M"
SERIES_TICKER_GOLD = "KXGOLD15M"
SERIES_TICKER_SILVER = "KXSILVER15M"   # silver (settles on Pyth's Metal.XAG/USD)
SERIES_TICKER_SOL = "KXSOL15M"   # Solana
SERIES_TICKER_NATGAS = "KXNATGAS15M"   # natural gas (settles on Pyth's 24/7 NATGAS index)
SERIES_TICKER_PLATINUM = "KXPLATINUM15M"
SERIES_TICKER_PALLADIUM = "KXPALLADIUM15M"
NATGAS_ENABLED = True   # set False to drop natural gas everywhere (rotation, neutral mode, early-resolve hop, /natgasmode)
ALL_SERIES_TICKERS = tuple(t for t in (SERIES_TICKER_BTC, SERIES_TICKER_ETH, SERIES_TICKER_GOLD, SERIES_TICKER_SILVER, SERIES_TICKER_SOL,
                                       SERIES_TICKER_NATGAS, SERIES_TICKER_PLATINUM, SERIES_TICKER_PALLADIUM)
                           if NATGAS_ENABLED or t != SERIES_TICKER_NATGAS)
ACTIVE_SERIES_TICKER = SERIES_TICKER_BTC  # changed only via the mode commands below, never edited directly
SILVER_MODE_ENABLED = False
GOLD_MODE_ENABLED = False          # kept for backward compatibility with any saved config override
PLATINUM_MODE_ENABLED = False
PALLADIUM_MODE_ENABLED = False
ETH_MODE_ENABLED = False
SOL_MODE_ENABLED = False
NATGAS_MODE_ENABLED = False
NEUTRAL_MODE_ENABLED = False   # auto-picks the most "stable" series every 15-min window (see NEUTRAL MODE block below); /neutralmode on|off
MODE_FLAG_NAMES = ("GOLD_MODE_ENABLED", "SILVER_MODE_ENABLED", "PLATINUM_MODE_ENABLED", "PALLADIUM_MODE_ENABLED",
                   "ETH_MODE_ENABLED", "SOL_MODE_ENABLED", "NATGAS_MODE_ENABLED", "NEUTRAL_MODE_ENABLED")
# command name (no slash) -> (series ticker, label, flag variable). Aliases share a tuple.
_ETH_MODE = (SERIES_TICKER_ETH, "\u039E ETHEREUM MODE", "ETH_MODE_ENABLED")
_SOL_MODE = (SERIES_TICKER_SOL, "\u25CE SOLANA MODE", "SOL_MODE_ENABLED")
_NATGAS_MODE = (SERIES_TICKER_NATGAS, "\U0001F525 NATURAL GAS MODE", "NATGAS_MODE_ENABLED")
MODE_COMMANDS = {
    "goldmode": (SERIES_TICKER_GOLD, "\U0001F7E1 GOLD MODE", "GOLD_MODE_ENABLED"),
    "silvermode": (SERIES_TICKER_SILVER, "\U0001F948 SILVER MODE", "SILVER_MODE_ENABLED"),
    "platinummode": (SERIES_TICKER_PLATINUM, "\u26AA PLATINUM MODE", "PLATINUM_MODE_ENABLED"),
    "palladiummode": (SERIES_TICKER_PALLADIUM, "\u2B55 PALLADIUM MODE", "PALLADIUM_MODE_ENABLED"),
    "ethereummode": _ETH_MODE, "ethmode": _ETH_MODE,
    "solanamode": _SOL_MODE, "solmode": _SOL_MODE,
    "naturalgasmode": _NATGAS_MODE, "gasmode": _NATGAS_MODE, "natgasmode": _NATGAS_MODE,
}
if not NATGAS_ENABLED:
    for _k in ("naturalgasmode", "gasmode", "natgasmode"):
        MODE_COMMANDS.pop(_k, None)
SERIES_STATUS_LABELS = {
    SERIES_TICKER_BTC: "\u20BF Bitcoin",
    SERIES_TICKER_ETH: "\u039E Ethereum mode",
    SERIES_TICKER_GOLD: "\U0001F7E1 Gold mode",
    SERIES_TICKER_SOL: "\u25CE Solana mode",
    SERIES_TICKER_NATGAS: "\U0001F525 Natural gas mode",
    SERIES_TICKER_SILVER: "\U0001F948 Silver mode",
    SERIES_TICKER_PLATINUM: "\u26AA Platinum mode",
    SERIES_TICKER_PALLADIUM: "\u2B55 Palladium mode",
}

def _current_mode_text():
    """Plain-English description of what's being traded right now, for the 'already on/off' replies."""
    if NEUTRAL_MODE_ENABLED:
        return "neutral mode"
    return SERIES_STATUS_LABELS.get(ACTIVE_SERIES_TICKER, ACTIVE_SERIES_TICKER)
# when its, any open position that reaches STOP_LOSS_DOLLARS or more in
# losses (total) will be automatically sold to
# cut downsides instead of holding forver.
STOP_LOSS_ENABLED = True
STOP_LOSS_DOLLARS = 4 # set to $20.00 on the day, 5 at night

# How often the dedicated position-monitoring thread checks open positions for
# stop-loss/take-profit, independent of the slower main scan loop (which only
# looks for new buy opportunities). Lower = faster loss detection, more API calls.
POSITION_CHECK_INTERVAL_SECONDS = 0.1

# Late in a market's life, a single large order (a "whale") can spike the
# quoted price hard against a held position and hold it there for a while
# before reverting - not necessarily a genuine reversal. Below this much time
# remaining, require the stop-loss condition to hold for a sustained duration
# before actually selling, so a temporary spike doesn't stop out a trade that
# recovers. Check count is derived from the duration so it stays correct if
# POSITION_CHECK_INTERVAL_SECONDS ever changes.
STOP_LOSS_CONFIRMATION_TIME_THRESHOLD_MINUTES = 2
STOP_LOSS_CONFIRMATION_SECONDS = 4.25

# Session-level circuit breaker: once cumulative REALIZED losses for this run
# hit this amount, stop opening any NEW positions (including secondary adds)
# for the rest of the session. Already-open positions still get managed
# normally to their own take-profit/stop-loss - this only blocks new risk.
# This is the one guard that caps how bad an entire unattended session can
# get, independent of which specific trade pattern causes the next loss.
DAILY_LOSS_LIMIT_ENABLED = True
DAILY_LOSS_LIMIT_DOLLARS = 3 # set to 15 on the day, 6 at night
# ------------------------

# --- PROFIT SWEEP (bank profit on exchange shard 0 so you can withdraw it yourself) ---
# Once UNSWEPT session profit reaches PROFIT_SWEEP_THRESHOLD_DOLLARS, the bot
# transfers that profit from the trading shard back to shard 0 and keeps
# trading with the original bankroll. Toggle/changed live via Telegram:
#   /sweep on|off   /setsweep <amount>   /sweepnow [amount]
# NOTE: Kalshi's intra_exchange_instance_transfer endpoint takes its amount in
# CENTICENTS (1/100 of a cent, so $1 = 10,000) per their docs - test with
# /sweepnow 0.10 first and confirm shard 0 shows +$0.10 before trusting it.
PROFIT_SWEEP_ENABLED = True
PROFIT_SWEEP_THRESHOLD_DOLLARS = 5
TRADING_SHARD = 2      # shard the bot trades on (transfer_shard_funds() below moves money 0 -> 2)
WITHDRAW_SHARD = 0     # shard 0 = where you check/withdraw from
TRANSFER_UNITS_PER_DOLLAR = 10000  # centicents
PROFIT_SWEEP_CHECK_INTERVAL_SECONDS = 10
SWEEP_STABLE_SECONDS = 30  # cash balance must sit unchanged this long (and no positions open/settling) before an auto-sweep is allowed
SWEEP_CONFIRM_TIMEOUT_SECONDS = 120  # if the balance hasn't dropped by then, auto-sweep switches itself OFF rather than risk sending twice
# --------------------------------------------------------------------------------------

# --- CROSS-SERIES EARLY-RESOLVE SWITCH ---
# When the current market resolves early and the SAME series has no other open
# window (normal - each 15m series only has one open at a time), hop to a
# market in any of the other series that still has a live two-sided book and
# passes the liquidity floor. Once that market closes, the bot returns to
# ACTIVE_SERIES_TICKER on its own.
CROSS_SERIES_SWITCH_ENABLED = True
CROSS_SERIES_SCAN_COOLDOWN_SECONDS = 3
EXHAUSTED_TICKER_TTL_SECONDS = 30
# -----------------------------------------

# --- TRIGGER THRESHOLDS (editable live via Telegram: /setthreshold, /setmultishare) ---
STANDARD_MAX_MINUTES = 2
HARD_ABSOLUTE_MAX_MINUTES = 3
PRICE_DROP_EXIT_ENABLED = False  # toggle via Telegram: /pricedropexit on|off
PRICE_DROP_EXIT_CENTS = 2  # sell immediately once the bid falls this many cents below entry - e.g. bought at 98c, drops to 96c -> sell. Independent of STOP_LOSS_DOLLARS: no confirmation delay, no dollar/size math, just raw cents moved against you.
EARLY_RESOLVE_ASK_THRESHOLD_CENTS = 1  # either ask at/below this means that side's book is empty - market's already decided, no edge left (only checked once we're already past HARD_ABSOLUTE_MAX_MINUTES - see check_market_and_trade)
EARLY_RESOLVE_MIN_SECONDS_LEFT = 30  # don't bother switching away if we're already inside the last 30s - a real market pins to an extreme right before it settles anyway, so that's not a genuine "early" resolve worth chasing
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
LIQUIDITY_FILTER_EXEMPT_SERIES = {"KXPLATINUM15M", "KXPALLADIUM15M"}  # thin markets - depth/volume floors would skip almost everything, so the filter just doesn't apply to these two
MIN_BOOK_DEPTH_CONTRACTS = 10  # skip a buy trigger if fewer than this many contracts are resting at the top-of-book price you'd fill against
MIN_MARKET_VOLUME_CONTRACTS = 500  # skip a market entirely if its total traded volume is below this
VOLUME_CACHE_TTL_SECONDS = 15  # how often to re-fetch a market's volume (avoids an extra API call every 0.5s loop cycle)
# --------------------------

EDITABLE_THRESHOLDS = {
    # readable aliases (use these day-to-day) - no underscores, but spelled
    # out enough to tell what each one actually does at a glance
    "stdmaxmin": "STANDARD_MAX_MINUTES",
    "hardmaxmin": "HARD_ABSOLUTE_MAX_MINUTES",
    "earlyspike": "EARLY_SPIKE_PRICE_CENTS",
    "normaltrigger": "NORMAL_TRIGGER_PRICE_CENTS",
    "multishare": "MULTI_SHARE_THRESHOLD",
    "secondarytime": "SECONDARY_TIME_LIMIT",
    "secondaryprice": "SECONDARY_PRICE_CENTS",
    "velocityfilter": "VELOCITY_FILTER_ENABLED",
    "maxpricejump": "MAX_PRICE_JUMP_CENTS",
    "liquidityfilter": "LIQUIDITY_FILTER_ENABLED",
    "minbookdepth": "MIN_BOOK_DEPTH_CONTRACTS",
    "minvolume": "MIN_MARKET_VOLUME_CONTRACTS",
    "trailingstop": "TRAILING_STOP_ENABLED",
    "trailingmincontracts": "TRAILING_STOP_MIN_CONTRACTS",
    "trailingarm": "TRAILING_STOP_ARM_DOLLARS",
    "trailingtrail": "TRAILING_STOP_TRAIL_DOLLARS",
    "stoplossconfirm": "STOP_LOSS_CONFIRMATION_SECONDS",
    "pricedropexit": "PRICE_DROP_EXIT_CENTS",
    # old 3-letter codes still work too, for muscle memory
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
    "pdc": "PRICE_DROP_EXIT_CENTS",
    # full snake_case names still work too
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
    "price_drop_exit_cents": "PRICE_DROP_EXIT_CENTS",
}
# shown in the /setthreshold usage message - the readable names, front and center
THRESHOLD_SHORT_NAMES = ["stdmaxmin", "hardmaxmin", "earlyspike", "normaltrigger", "multishare",
                         "secondarytime", "secondaryprice", "velocityfilter", "maxpricejump",
                         "liquidityfilter", "minbookdepth", "minvolume", "trailingstop",
                         "trailingmincontracts", "trailingarm", "trailingtrail", "stoplossconfirm",
                         "pricedropexit"]

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
# --- P/L "IN FLIGHT" GUARD ---
# Balance-based P/L is only trustworthy when no money is mid-transit. While a
# buy/sell is being processed, or a settled market's payout hasn't necessarily
# landed yet, cash and the open-position cost basis disagree for a moment:
# that reads as a fake LOSS (cost left cash but isn't counted as open) or a
# fake GAIN (payout landed but the position still counts as open). During
# those windows P/L is reported as "unknown" instead of a wrong number.
PAYOUT_GRACE_SECONDS = 60   # after a market settles/voids
ORDER_GRACE_SECONDS = 5     # after a buy/sell order
_pnl_quiet_until = 0.0

def _mark_pnl_unstable(seconds):
    global _pnl_quiet_until
    _pnl_quiet_until = max(_pnl_quiet_until, time.time() + seconds)

def _pnl_in_flight():
    if time.time() < _pnl_quiet_until:
        return True
    now_utc = datetime.now(pytz.UTC)
    with positions_lock:
        tickers = list(open_positions.keys())
    for t in tickers:
        ct = _market_close_time_cache.get(t)
        if ct and now_utc >= ct:
            return True  # market is closed but the position isn't resolved yet - payout may or may not have landed
    return False
# -----------------------------

swept_total_dollars = 0.0  # cumulative profit moved to WITHDRAW_SHARD this run - added back into session P/L so a sweep doesn't look like a loss
_sweep_lock = threading.Lock()
_sweep_state = {"unconfirmed": False, "pre_balance": 0.0, "amount": 0.0, "sent_at": 0.0, "last_bal": None, "stable_since": None}
_exhausted_tickers = {}  # ticker -> epoch seconds it was seen early-resolved, so skip-ahead never bounces back to a dead market
_last_cross_series_scan = 0.0
session_start_balance = None  # captured once at startup - real account balance, used as the authoritative source for session P/L (session_realized_pnl misses trades whose settlement result isn't available yet - see get_session_pnl)

# --- TELEGRAM ALERTS: HOURLY / DAILY P/L SUMMARY ---
# Sends a message to your phone (via Telegram) with how much you've made in
# the last hour and the last day, so you can check in without opening logs.
#
TELEGRAM_BOT_TOKEN = "YOUR_TELEGRAM_BOT_TOKEN"   # from @BotFather
TELEGRAM_CHAT_ID = "YOUR_TELEGRAM_CHAT_ID"
ALERTS_ENABLED = True
SUMMARY_CHECK_INTERVAL_SECONDS = 60  # how often the summary thread checks whether an hour/day has elapsed
# ----------------------------------------------------

_hourly_checkpoint_pnl = None  # set on the first clean equity reading
_hourly_checkpoint_time = time.time()
_daily_checkpoint_pnl = None
_daily_checkpoint_time = time.time()
_hourly_checkpoint_swept = 0.0  # swept_total_dollars at the last hourly/daily checkpoint, so money moved to shard 0 isn't reported as a loss
_daily_checkpoint_swept = 0.0

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
    lines = [f"\U0001F4CA EXPECTANCY ({scope})",
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
        return "\u23F3 Not enough data yet"
    avg_jump = sum(jumps) / len(jumps)
    if mood == "choppy":
        return f"\U0001F7E0 CHOPPY (avg swing {avg_jump:.1f}\u00a2/check)"
    return f"\U0001F7E2 CALM (avg swing {avg_jump:.1f}\u00a2/check)"
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
    # A series that has since been removed from the rotation (e.g. WTI) must not
    # survive in a saved override - otherwise the bot would keep trading it after a restart.
    if ACTIVE_SERIES_TICKER not in ALL_SERIES_TICKERS:
        print(f"--> [CONFIG] Saved series {ACTIVE_SERIES_TICKER} is no longer in the rotation - falling back to {SERIES_TICKER_BTC}.")
        globals()["ACTIVE_SERIES_TICKER"] = SERIES_TICKER_BTC
        _save_config_override("ACTIVE_SERIES_TICKER", SERIES_TICKER_BTC)
        for _flag in MODE_FLAG_NAMES:
            if _flag != "NEUTRAL_MODE_ENABLED":
                globals()[_flag] = False
                _save_config_override(_flag, False)
    # retire the old oil flag from the saved file so it can't linger
    if "OIL_MODE_ENABLED" in overrides:
        try:
            ov = _load_config_overrides()
            ov.pop("OIL_MODE_ENABLED", None)
            with open(CONFIG_OVERRIDES_FILE, "w") as f:
                json.dump(ov, f, indent=2)
        except Exception as e:
            print(f"--> [WARNING] Could not clean old oil flag from overrides: {e}")
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
    "MULTI_SHARE_CONTRACT_COUNT", "AUTOSELLING", "STOP_LOSS_ENABLED", "SOURCE_MODE_ENABLED", "SOURCE_MODE_AUTOSELL", "SOURCE_MODE_BUY_PROB", "SOURCE_MODE_SELL_PROB",
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

_private_key_cache = {}   # path -> loaded key. Re-reading/validating the PEM on every API call was pure overhead.

def load_private_key():
    """uses my rsa priv key for signing request (loaded once per path, then reused)"""
    path = PRIVATE_KEY_PATH
    key = _private_key_cache.get(path)
    if key is None:
        with open(path, "rb") as key_file:
            key = load_pem_private_key(key_file.read(), password=None)
        _private_key_cache[path] = key
    return key

TELEGRAM_MAX_CHARS = 4096   # Telegram's hard per-message limit - anything over this gets rejected with a 400

TELEGRAM_PREFIX_RESERVE = 16   # headroom for the "(N/N)\n" numbering prefix send_alert adds to multi-part messages

def _split_for_telegram(message, limit=TELEGRAM_MAX_CHARS - TELEGRAM_PREFIX_RESERVE):
    """Splits a message into chunks Telegram will actually accept, breaking on
    line boundaries where possible so a command/sentence doesn't get cut mid-word.
    This is why /help (and anything else that grows past 4096 chars, like a long
    /neutralrank or /history) was silently failing before - sendMessage was
    rejecting the whole thing and send_alert just logged the warning and moved on."""
    if len(message) <= limit:
        return [message]
    chunks, current = [], ""
    for line in message.split("\n"):
        candidate = current + ("\n" if current else "") + line
        if len(candidate) <= limit:
            current = candidate
        else:
            if current:
                chunks.append(current)
            # a single line longer than the limit (shouldn't normally happen) - hard-split it
            while len(line) > limit:
                chunks.append(line[:limit])
                line = line[limit:]
            current = line
    if current:
        chunks.append(current)
    return chunks

def _send_telegram_text(message):
    """One raw sendMessage call. Raises on failure - callers handle/log it."""
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    payload = json.dumps({"chat_id": TELEGRAM_CHAT_ID, "text": message}).encode("utf-8")
    req = urllib.request.Request(
        url, data=payload, headers={"Content-Type": "application/json"}, method="POST"
    )
    urllib.request.urlopen(req, timeout=10)

def send_alert(message):
    """Sends a Telegram message. Never raises - a failed alert should never
    take down the trading loop. Messages over Telegram's 4096-char limit are
    split into multiple messages instead of being rejected outright."""
    if not ALERTS_ENABLED:
        return
    if "PASTE_YOUR" in TELEGRAM_BOT_TOKEN or "PASTE_YOUR" in TELEGRAM_CHAT_ID:
        print("--> [WARNING] ALERTS_ENABLED is True but TELEGRAM_BOT_TOKEN/CHAT_ID aren't set yet.")
        return
    chunks = _split_for_telegram(message)
    for i, chunk in enumerate(chunks):
        try:
            prefix = f"({i + 1}/{len(chunks)})\n" if len(chunks) > 1 else ""
            _send_telegram_text(prefix + chunk)
        except Exception as e:
            print(f"--> [WARNING] Telegram alert failed to send (part {i + 1}/{len(chunks)}): {e}")

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

# --- KEEP-ALIVE HTTP TRANSPORT ---
# kalshi_request used to open a brand-new TCP+TLS connection for EVERY call
# (urllib.urlopen has no connection reuse), which added a few round trips of
# handshake to every orderbook read, index read and sell order. Now each thread
# keeps one persistent HTTPS connection and reuses it.
#  - Connections idle longer than HTTP_IDLE_RECONNECT_SECONDS are replaced before use
#    (servers silently close idle sockets; this avoids most stale-socket errors).
#  - If a reused socket turns out to be dead, we retry ONCE on a fresh connection - but
#    only for GETs and for orders carrying a client_order_id (Kalshi de-duplicates those,
#    so a resend can't double-fill). Other POSTs (e.g. fund transfers) are never resent.
#  - gzip is requested: the CF Benchmarks index call returns up to an hour of 1s values.
#  - Requests now time out after HTTP_TIMEOUT_SECONDS (before, a hung call could block forever).
_API_URL = urllib.parse.urlparse(HOST)
_http_local = threading.local()
HTTP_TIMEOUT_SECONDS = 10
HTTP_IDLE_RECONNECT_SECONDS = 20
_HTTP_STALE_ERRORS = (http.client.RemoteDisconnected, http.client.CannotSendRequest,
                      http.client.ResponseNotReady, http.client.BadStatusLine,
                      BrokenPipeError, ConnectionResetError, ConnectionAbortedError,
                      ssl.SSLEOFError, ssl.SSLZeroReturnError)   # what a dead TLS socket raises

def _new_https_conn():
    return http.client.HTTPSConnection(_API_URL.hostname, _API_URL.port or 443, timeout=HTTP_TIMEOUT_SECONDS)

def _drop_http_conn():
    conn = getattr(_http_local, "conn", None)
    _http_local.conn = None
    if conn is not None:
        try:
            conn.close()
        except Exception:
            pass

def _get_http_conn(fresh=False):
    conn = getattr(_http_local, "conn", None)
    idle = time.time() - getattr(_http_local, "last_used", 0.0)
    if conn is not None and (fresh or idle > HTTP_IDLE_RECONNECT_SECONDS):
        _drop_http_conn()
        conn = None
    if conn is None:
        conn = _new_https_conn()
        _http_local.conn = conn
    return conn

def kalshi_request(method, endpoint, payload=None):
    """authenticated REST requests to Kalshi V2 endpoints."""
    # Kalshi verifies the signature over the path WITHOUT the query string.
    # The URL we call keeps "?id=BRTI" etc., but the signed string must not -
    # signing it with the query makes authenticated endpoints reject the
    # request (public market-data calls never check the signature, which is
    # why queries only broke on the CF Benchmarks index endpoint).
    sign_path = f"/trade-api/v2{endpoint.split('?', 1)[0]}"
    full_path = f"{_API_URL.path}{endpoint}"
    data = json.dumps(payload).encode("utf-8") if payload else None
    retry_ok = method == "GET" or (isinstance(payload, dict) and "client_order_id" in payload)

    for attempt in (0, 1):
        timestamp_str = str(int(time.time() * 1000))   # re-signed on a retry so the timestamp is fresh
        sig = sign_request(load_private_key(), timestamp_str, method, sign_path)
        headers = {
            "Content-Type": "application/json",
            "Accept": "application/json",
            "Accept-Encoding": "gzip",
            "KALSHI-ACCESS-KEY": KEY_ID,
            "KALSHI-ACCESS-TIMESTAMP": timestamp_str,
            "KALSHI-ACCESS-SIGNATURE": sig
        }
        conn = _get_http_conn(fresh=(attempt == 1))
        try:
            conn.request(method, full_path, body=data, headers=headers)
            resp = conn.getresponse()
            raw = resp.read()
        except _HTTP_STALE_ERRORS:
            _drop_http_conn()
            if attempt == 0 and retry_ok:
                continue
            raise
        except Exception:
            _drop_http_conn()
            raise
        _http_local.last_used = time.time()
        if (resp.getheader("Content-Encoding") or "").lower() == "gzip":
            raw = gzip.decompress(raw)
        if resp.status >= 300:
            error_body = raw.decode("utf-8", errors="replace")
            print(f"--> [HTTP {resp.status}] Full Server Response: {error_body}")
            raise urllib.error.HTTPError(f"{HOST}{endpoint}", resp.status, resp.reason, resp.msg, io.BytesIO(raw))
        return json.loads(raw.decode())

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

def get_all_exchange_balances():
    """Returns (total_dollars, {exchange_index: dollars}) by reading the
    balance_breakdown field Kalshi already includes on every /portfolio/balance
    response (get_kalshi_account_balance() was only reading the aggregate
    'balance' field and discarding this). Returns (None, {}) on failure."""
    try:
        data = kalshi_request("GET", "/portfolio/balance")
        total_cents = data.get("balance") or data.get("cash_balance") or 0
        total = float(total_cents) / 100.0
        breakdown = {}
        for entry in data.get("balance_breakdown", []) or []:
            idx = entry.get("exchange_index")
            bal = entry.get("balance")
            if idx is None or bal is None:
                continue
            try:
                breakdown[int(idx)] = float(bal)  # per Kalshi's docs, balance_breakdown's "balance" is already a dollar string, not cents
            except (TypeError, ValueError):
                continue
        return total, breakdown
    except Exception as e:
        print(f"--> [WARNING] Failed to fetch exchange balance breakdown: {e}")
        return None, {}

def get_exchange_balance(exchange_index):
    """Convenience wrapper: balance of just one exchange shard, or None if
    it can't be fetched or that shard doesn't appear in the breakdown."""
    _, breakdown = get_all_exchange_balances()
    return breakdown.get(exchange_index)

def fund_trading_shard(amount_dollars):
    """Manually moves amount_dollars from WITHDRAW_SHARD (0) into
    TRADING_SHARD (2) - the reverse direction of _sweep_funds, for topping up
    the trading shard rather than pulling profit out of it. Takes a plain
    dollar amount; Kalshi's intra_exchange_instance_transfer endpoint wants
    the amount in CENTICENTS (1/100 of a cent, so $1.00 = 10,000), converted
    here via TRANSFER_UNITS_PER_DOLLAR so you never have to do that math by
    hand. Returns (True, transfer_id) on success, (False, reason) otherwise."""
    amount_dollars = round(amount_dollars, 2)
    if amount_dollars <= 0:
        return False, "amount must be positive"

    source_balance = get_exchange_balance(WITHDRAW_SHARD)
    if source_balance is not None and amount_dollars > source_balance:
        return False, f"${amount_dollars:.2f} is more than the ${source_balance:.2f} sitting on exchange {WITHDRAW_SHARD}"

    payload = {
        "amount": int(round(amount_dollars * TRANSFER_UNITS_PER_DOLLAR)),
        "source": "event_contract",
        "destination": "event_contract",
        "source_exchange_shard": WITHDRAW_SHARD,
        "destination_exchange_shard": TRADING_SHARD,
        "source_subaccount": 0,
        "destination_subaccount": 0,
    }
    try:
        response = kalshi_request("POST", "/portfolio/intra_exchange_instance_transfer", payload=payload)
    except Exception as e:
        print(f"--> [FUND] Transfer FAILED: {e}")
        return False, str(e)

    transfer_id = (response or {}).get("transfer_id")
    print(f"--> [FUND] Sent ${amount_dollars:.2f} exchange {WITHDRAW_SHARD} -> exchange {TRADING_SHARD}. Transfer ID: {transfer_id}")
    return True, transfer_id

def _sweep_funds(amount_dollars, reason):
    """Moves amount_dollars from TRADING_SHARD to WITHDRAW_SHARD. Caller must
    hold _sweep_lock. Returns True only if Kalshi accepted the request."""
    global swept_total_dollars
    amount_dollars = math.floor(round(amount_dollars * 100, 6)) / 100.0  # whole cents, always rounded DOWN
    if amount_dollars <= 0:
        return False
    pre_balance = get_kalshi_account_balance()
    if pre_balance is None:
        print("--> [SWEEP] Skipped - couldn't read balance to verify funds.")
        return False
    if amount_dollars > pre_balance:
        print(f"--> [SWEEP] Skipped - ${amount_dollars:.2f} is more than the ${pre_balance:.2f} cash balance right now.")
        return False

    payload = {
        "amount": int(round(amount_dollars * TRANSFER_UNITS_PER_DOLLAR)),
        "source": "event_contract",
        "destination": "event_contract",
        "source_exchange_shard": TRADING_SHARD,
        "destination_exchange_shard": WITHDRAW_SHARD,
        "source_subaccount": 0,
        "destination_subaccount": 0,
    }
    try:
        response = kalshi_request("POST", "/portfolio/intra_exchange_instance_transfer", payload=payload)
    except Exception as e:
        print(f"--> [SWEEP] Transfer FAILED: {e}")
        push_alert(f"\u26A0\uFE0F Profit sweep of ${amount_dollars:.2f} FAILED: {e}")
        return False

    swept_total_dollars = round(swept_total_dollars + amount_dollars, 2)
    # The transfer is processed asynchronously, so don't sweep again until the
    # balance actually shows the money has left (see _check_and_sweep_profit).
    _sweep_state.update({"unconfirmed": True, "pre_balance": pre_balance,
                         "amount": amount_dollars, "sent_at": time.time()})
    transfer_id = (response or {}).get("transfer_id")
    print(f"--> [SWEEP] Sent ${amount_dollars:.2f} shard {TRADING_SHARD} -> shard {WITHDRAW_SHARD} ({reason}). Transfer ID: {transfer_id}")
    push_alert(f"\U0001F3E6 Swept ${amount_dollars:.2f} to exchange {WITHDRAW_SHARD} ({reason}).\n"
               f"Total swept this session: ${swept_total_dollars:.2f}")
    return True

def _safe_sweepable_amount(require_stable=True):
    """The ONLY place that decides how much profit may be swept. Returns
    (amount_dollars, reason). amount is None when sweeping isn't safe right now.

    Safety rules - each one exists to make it impossible to sweep money that
    is merely in transit (cash spent on open contracts, or a payout that
    hasn't been paired with its position yet):
      1. No money in flight: no recent orders, no settling/just-settled markets.
      2. FLAT: zero open positions, so cash balance is the whole truth.
      3. (auto only) the cash balance has sat unchanged for SWEEP_STABLE_SECONDS.
      4. Amount = the SMALLER of (cash balance - starting balance) and the
         bot's own realized-P/L tally minus what's already swept. A phantom
         gain can inflate one number but not both, and the cash can never be
         taken below where the session started.
    """
    if session_start_balance is None:
        return None, "starting balance unknown"
    if _pnl_in_flight():
        _sweep_state["stable_since"] = None
        return None, "an order or payout is still settling"
    with positions_lock:
        has_open = bool(open_positions)
    if has_open:
        _sweep_state["stable_since"] = None
        return None, "positions are open (cash isn't the full picture until flat)"

    bal = get_kalshi_account_balance()
    if bal is None:
        return None, "couldn't read balance"
    if require_stable:
        last = _sweep_state.get("last_bal")
        if last is None or abs(bal - last) > 0.005 or _sweep_state.get("stable_since") is None:
            _sweep_state["last_bal"] = bal
            _sweep_state["stable_since"] = time.time()
            return None, "waiting for balance to stay steady"
        if time.time() - _sweep_state["stable_since"] < SWEEP_STABLE_SECONDS:
            return None, "waiting for balance to stay steady"

    balance_profit = bal - session_start_balance
    with session_pnl_lock:
        realized_unswept = session_realized_pnl - swept_total_dollars
    amount = min(balance_profit, realized_unswept)
    if amount <= 0:
        return None, f"no confirmed profit (cash +${balance_profit:.2f}, tracked +${realized_unswept:.2f})"
    return amount, f"cash +${balance_profit:.2f}, tracked +${realized_unswept:.2f}"

def _check_and_sweep_profit():
    """Called periodically by the sweep thread. Sweeps confirmed profit once
    it reaches PROFIT_SWEEP_THRESHOLD_DOLLARS (see _safe_sweepable_amount)."""
    global PROFIT_SWEEP_ENABLED
    with _sweep_lock:
        if _sweep_state["unconfirmed"]:
            bal = get_kalshi_account_balance()
            if bal is None:
                return
            if bal <= _sweep_state["pre_balance"] - 0.5 * _sweep_state["amount"]:
                _sweep_state["unconfirmed"] = False
                _sweep_state["last_bal"] = None
                _sweep_state["stable_since"] = None
                print(f"--> [SWEEP] Confirmed - balance dropped to ${bal:.2f}.")
            elif time.time() - _sweep_state["sent_at"] > SWEEP_CONFIRM_TIMEOUT_SECONDS:
                PROFIT_SWEEP_ENABLED = False
                _save_config_override("PROFIT_SWEEP_ENABLED", False)
                _sweep_state["unconfirmed"] = False
                push_alert(f"\U0001F6D1 Auto-sweep switched OFF: balance never dropped after the last "
                           f"${_sweep_state['amount']:.2f} transfer. Check exchange {WITHDRAW_SHARD} manually, "
                           f"then /sweep on to re-enable.")
            return

        amount, why = _safe_sweepable_amount(require_stable=True)
        if amount is not None and amount >= PROFIT_SWEEP_THRESHOLD_DOLLARS:
            _sweep_funds(amount, f"auto - confirmed profit hit ${PROFIT_SWEEP_THRESHOLD_DOLLARS:.2f} ({why})")

def _profit_sweep_loop():
    while True:
        try:
            if PROFIT_SWEEP_ENABLED:
                _check_and_sweep_profit()
        except Exception as e:
            print(f"--> [ERROR] Profit sweep thread hit an error (continuing): {e}")
        time.sleep(PROFIT_SWEEP_CHECK_INTERVAL_SECONDS)

def get_candidate_event_tickers():
    """Returns EVERY currently-open, not-yet-closed event ticker for the
    active series, sorted soonest-closing first - not just the one we'd
    normally pick. Used both for normal resolution (take the first) and for
    the early-resolve skip-ahead logic in the main loop (try the next one if
    the first has already resolved early due to a spike). Returns [] on any
    API failure so callers can fall back to the calculated-ticker guess."""
    active_series = ACTIVE_SERIES_TICKER
    try:
        endpoint = f"/markets?series_ticker={active_series}&status=open"
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
                return [(m.get("event_ticker"), ct) for m, ct in valid_markets if m.get("event_ticker")]

    except Exception as e:
        print(f"--> [WARNING] Production event lookup via API failed: {e}")
    return []

def _calculate_fallback_event_ticker():
    """Guesses the current window's event ticker from the clock alone, for
    when the API lookup above fails entirely."""
    eastern = pytz.timezone('US/Eastern')
    now_et = datetime.now(eastern)
    minutes_to_add = 15 - (now_et.minute % 15)
    expiration_time = now_et + timedelta(minutes=minutes_to_add)

    year_str = expiration_time.strftime("%y")
    month_str = expiration_time.strftime("%b")
    day_str = expiration_time.strftime("%d")
    time_str = expiration_time.strftime("%H%M")

    calculated_ticker = f"{ACTIVE_SERIES_TICKER}-{year_str}{month_str}{day_str}{time_str}"
    print(f"--> [LIVE FALLBACK] Calculated expected ticker: {calculated_ticker}")
    return calculated_ticker

def get_current_event_ticker():
    """Figures out the active current event ticker for whichever series is
    live right now - Bitcoin (KXBTC15M) normally, or a metal series when one
    of the metal modes is on. Checked fresh each call so a Telegram toggle
    takes effect on the very next scan, not on next restart. Thin wrapper
    around get_candidate_event_tickers() - just takes the soonest-closing one."""
    candidates = get_candidate_event_tickers()
    if candidates:
        resolved_event_ticker = candidates[0][0]
        log_smart(("event",), f"--> [LIVE] Active event: {resolved_event_ticker}", sig=resolved_event_ticker, interval=3600)
        return resolved_event_ticker
    return _calculate_fallback_event_ticker()

def _series_of(market_ticker):
    """'KXGOLD15M-26OCT021430-T123' -> 'KXGOLD15M'"""
    return market_ticker.split("-")[0]

def _mark_exhausted(market_ticker):
    _exhausted_tickers[market_ticker] = time.time()

def _is_recently_exhausted(market_ticker):
    ts = _exhausted_tickers.get(market_ticker)
    if ts is None:
        return False
    if time.time() - ts > EXHAUSTED_TICKER_TTL_SECONDS:
        _exhausted_tickers.pop(market_ticker, None)
        return False
    return True

def _book_snapshot(market_ticker):
    """Returns (yes_ask, no_ask, yes_ask_depth, no_ask_depth) in cents/contracts,
    parsed exactly like check_market_and_trade does, or None on failure."""
    def top(bids):
        if not bids:
            return 0, 0
        entry = bids[-1] if isinstance(bids, list) else bids
        if isinstance(entry, list):
            price_val = entry[0]
            size_val = entry[1] if len(entry) > 1 else 0
        else:
            price_val, size_val = entry, 0
        if isinstance(price_val, str) or float(price_val) <= 1.0:
            cents = int(round(float(price_val) * 100))
        else:
            cents = int(round(float(price_val)))
        try:
            size = int(round(float(size_val)))
        except (TypeError, ValueError):
            size = 0
        return cents, size
    try:
        data = kalshi_request("GET", f"/markets/{market_ticker}/orderbook")
        ob = data.get("orderbook_fp") or data.get("orderbook") or data
        yes_bid, yes_bid_size = top(ob.get("yes_dollars") or ob.get("yes") or [])
        no_bid, no_bid_size = top(ob.get("no_dollars") or ob.get("no") or [])
        yes_ask = (100 - no_bid) if no_bid > 0 else 0
        no_ask = (100 - yes_bid) if yes_bid > 0 else 0
        return yes_ask, no_ask, no_bid_size, yes_bid_size
    except Exception as e:
        print(f"--> [WARNING] Cross-series book check failed for {market_ticker}: {e}")
        return None

def find_cross_series_candidate(exclude_ticker):
    """Looks across ALL series (not just ACTIVE_SERIES_TICKER) for an open
    market that's worth switching to after an early resolve: inside the
    tradable time window, not itself early-resolved, a live two-sided book,
    and (for non-exempt series) above the volume floor. Picks the one with
    the deepest top-of-book. Returns (ticker, close_time) or (None, None)."""
    now_utc = datetime.now(pytz.UTC)
    best = None  # (score, ticker, close_time, close_str, series)
    for series in ALL_SERIES_TICKERS:
        try:
            data = kalshi_request("GET", f"/markets?series_ticker={series}&status=open")
        except Exception as e:
            print(f"--> [WARNING] Cross-series lookup failed for {series}: {e}")
            continue
        for m in data.get("markets", []):
            ticker = m.get("ticker")
            if not ticker or ticker == exclude_ticker or _is_recently_exhausted(ticker):
                continue
            close_str = m.get("close_time") or m.get("expiration_time")
            if not close_str:
                continue
            try:
                close_time = datetime.fromisoformat(close_str.replace("Z", "+00:00"))
            except ValueError:
                continue
            remaining_min = (close_time - now_utc).total_seconds() / 60.0
            if remaining_min > HARD_ABSOLUTE_MAX_MINUTES or remaining_min * 60 <= EARLY_RESOLVE_MIN_SECONDS_LEFT:
                continue  # can't trade it yet / too close to settling to be worth a switch

            exempt = (not LIQUIDITY_FILTER_ENABLED) or series in LIQUIDITY_FILTER_EXEMPT_SERIES
            if not exempt:
                vol = m.get("volume")
                vol = int(vol) if vol is not None else get_market_volume(ticker)
                if vol is not None and vol < MIN_MARKET_VOLUME_CONTRACTS:
                    continue

            snap = _book_snapshot(ticker)
            if snap is None:
                continue
            yes_ask, no_ask, yes_depth, no_depth = snap
            if yes_ask <= EARLY_RESOLVE_ASK_THRESHOLD_CENTS or no_ask <= EARLY_RESOLVE_ASK_THRESHOLD_CENTS:
                continue  # empty/decided book on either side - same test the early-resolve check uses
            if NEUTRAL_MODE_ENABLED and _neutral_floor_check(_neutral_get_hist(series), max(0, yes_ask + no_ask - 100),
                                                             min(yes_depth, no_depth)):
                continue  # neutral mode never hops into a series that fails the floors
            score = yes_depth + no_depth
            if best is None or score > best[0]:
                best = (score, ticker, close_time, close_str, series)

    if best is None:
        return None, None
    _, ticker, close_time, close_str, series = best
    _get_cached_close_time(ticker, close_str)
    return ticker, close_time

# --- SOURCE CHECK (start) ---
# Independent second opinion on the SETTLEMENT SOURCE. BTC/ETH/SOL 15-minute
# markets settle like this: YES wins if the simple average of the 60 one-second
# CF Benchmarks index prints before CLOSE is >= the same 60-second average
# before OPEN (the "strike"). Kalshi passes that exact index through its API
# (GET /cfbenchmarks/values?id=...), which returns up to an hour of 1-second
# values - so from ONE call we can see (a) the part of the settlement average
# that has already happened, (b) the strike, and (c) how jumpy the index is.
#
# Before any buy, we project the final 60s average and ask: given how jumpy the
# index is and how much time is left, how many standard deviations (z) is the
# side we're about to buy ahead? The book can say 98c while the real index
# average is sitting right on the strike - this catches that.
#     projected avg = (already-observed part + current value x time left) / 60
#     z = (projected avg - strike) / (sigma x sqrt(variance-time left))   [side-adjusted]
# A buy is vetoed when z < SOURCE_CHECK_MIN_Z or the margin is under
# SOURCE_CHECK_MIN_MARGIN_BPS. FAILS OPEN: if the feed is unavailable (it needs
# an account entitlement), stale, unparseable, or the series has no public
# index (gold, natgas, platinum, palladium), the buy is allowed and the reason
# is logged - this check can only ever remove trades, never add them.
# Telegram: /sourcecheck [on|off|shadow|status], /setsource z|margin <value>
SOURCE_CHECK_ENABLED = True
SOURCE_CHECK_SHADOW = False             # True = log "would have vetoed" but still allow the buy (to watch it before trusting it)
SOURCE_CHECK_MIN_Z = 2.0                # ~2.3% chance the leading side still loses if the random-walk model holds
SOURCE_CHECK_MIN_MARGIN_BPS = 1.0       # absolute floor on the projected lead, in basis points of price
SOURCE_CHECK_INDEX_IDS = {
    "KXBTC15M": "BRTI", "KXETH15M": "ETHUSD_RTI", "KXSOL15M": "SOLUSD_RTI",   # CF Benchmarks, via REST (confirmed working)
    "KXGOLD15M": "Metal.XAU/USD", "KXSILVER15M": "Metal.XAG/USD", "KXPLATINUM15M": "Metal.XPT/USD", "KXPALLADIUM15M": "Metal.XPD/USD",  # Pyth, via websocket below
    # KXNATGAS15M deliberately omitted: natural gas on Pyth uses a rolling futures contract code (e.g.
    # "Commodities.NGDQ6/USD") that changes over time, not a fixed ticker like the metals above. Rather than
    # hardcode a code that will go stale, _pyth_note_natgas() below spots the live one from the Pyth stream and adds it here.
}
SOURCE_CHECK_DEFAULT_SIGMA_BPS = {"BRTI": 0.8, "ETHUSD_RTI": 1.1, "SOLUSD_RTI": 1.6,
                                  "Metal.XAU/USD": 0.3, "Metal.XAG/USD": 0.5, "Metal.XPT/USD": 0.5, "Metal.XPD/USD": 0.6}   # bps per sqrt(second); metals are calmer than crypto, guessed low until measured
SOURCE_CHECK_SIGMA_FLOOR_FRACTION = 0.6 # never trust a calm stretch more than 60% of the default vol (vol spikes without warning)
SOURCE_CHECK_VOL_LOOKBACK_SECONDS = 180
SOURCE_CHECK_CACHE_SECONDS = 1.5        # each index call costs 5x a normal read (50 tokens); reuse it between scans
SOURCE_CHECK_MAX_AGE_SECONDS = 8        # newest index print older than this = stale feed -> fail open
SOURCE_CHECK_MAX_STRIKE_GAP_PCT = 2.0   # strike vs index further apart than this = looks like a units/parse problem -> fail open

_source_state = {"cache": {}, "backoff_until": 0.0, "unavailable_reason": None, "last_shape": "",
                 "market_info": {}, "alerted": set(), "logged": set(),
                 "stats": {"checks": 0, "allowed": 0, "vetoed": 0, "would_veto": 0, "failopen": 0}}

def _parse_ts(t):
    """Epoch seconds from ms/seconds numbers, numeric strings, or ISO strings."""
    try:
        if isinstance(t, (int, float)):
            x = float(t)
        elif isinstance(t, str) and t.replace(".", "", 1).isdigit():
            x = float(t)
        elif isinstance(t, str):
            return datetime.fromisoformat(t.replace("Z", "+00:00")).timestamp()
        else:
            return None
        return x / 1000.0 if x > 1e11 else x
    except (ValueError, TypeError):
        return None

def _parse_index_points(resp):
    """Pulls every {time, value} pair out of a CF Benchmarks response, wherever it
    sits in the envelope, as a time-sorted [(epoch_seconds, value)]. Deliberately
    tolerant of shape - the passthrough wraps the raw upstream payload."""
    pts = {}
    def walk(o):
        if isinstance(o, dict):
            if "value" in o and ("time" in o or "timestamp" in o):
                ts = _parse_ts(o.get("time", o.get("timestamp")))
                try:
                    v = float(o["value"])
                except (TypeError, ValueError):
                    v = None
                if ts is not None and v is not None and v > 0:
                    pts[round(ts, 3)] = v
                return
            for x in o.values():
                walk(x)
        elif isinstance(o, list):
            for x in o:
                walk(x)
    walk(resp)
    return sorted(pts.items())

# --- PYTH WEBSOCKET FEED (start) ---
# Gold/platinum/palladium settle on Pyth, and the only Kalshi endpoint that
# carries Pyth prices is the authenticated `pyth_value` WEBSOCKET channel -
# there is no REST passthrough for it the way there is for CF Benchmarks.
# This runs a persistent background connection and feeds the SAME
# (timestamp, value) point format _get_index_points() returns for CF
# Benchmarks, so _source_check_eval()'s math is reused unchanged.
#
# UNVERIFIED AGAINST LIVE KALSHI: I still don't have network access to test
# this myself. PYTH_WS_PATH/the connection URL are now confirmed correct
# against Kalshi's own docs (wss://external-api-ws.kalshi.com/trade-api/ws/v2,
# first fixed from a 404 that showed the old path was wrong). What's still
# unverified: the pyth_value message/subscribe shapes below, and whether this
# account's key is entitled to the channel. Run /pythfeed after restarting -
# a 401/403 now would mean an entitlement problem; anything else, paste it.
#
# Needs the `websocket-client` package: pip install websocket-client --break-system-packages
PYTH_FEED_ENABLED = True
PYTH_WS_HOST = "external-api-ws.kalshi.com"
PYTH_WS_PATH = "/trade-api/ws/v2"          # confirmed from Kalshi's websocket docs - the connection URL IS this path too (unlike REST, no "/trade-api/v2" prefix in front of it)
PYTH_UNDERLYING_TICKERS = {
    "KXGOLD15M": "Metal.XAU/USD",
    "KXSILVER15M": "Metal.XAG/USD",
    "KXPLATINUM15M": "Metal.XPT/USD",
    "KXPALLADIUM15M": "Metal.XPD/USD",
}
PYTH_NATGAS_MATCH = ("NATGAS", "NGD", "HENRY")   # substrings used to spot the natural-gas ticker in the stream
PYTH_NATGAS_TICKER_OVERRIDE = None   # if /pythfeed shows the right natgas ticker but auto-detect picks wrong/nothing, put it here, e.g. "Commodities.NGDQ6/USD"
PYTH_NATGAS_DEFAULT_SIGMA_BPS = 1.5  # natgas is much choppier than metals; guessed until measured (the floor logic keeps this conservative)
PYTH_SEEN_MAX = 400                  # cap on distinct ticker names remembered for /pythfeed diagnostics
PYTH_BUFFER_SECONDS = 300         # how much tick history to keep per underlying
PYTH_RECONNECT_BACKOFF_SECONDS = (2, 5, 10, 30, 60)   # grows on repeated failures, caps at 60s
PYTH_STALE_SECONDS = 15           # no tick in this long -> treat the feed as down for that underlying

_pyth_state = {
    "connected": False, "ws": None, "thread": None, "stop": False,
    "buffers": {},              # underlying_ticker -> [(epoch_seconds, value), ...], newest last
    "lock": threading.Lock(),
    "natgas_ticker": None,      # resolved from the live stream / underlying list once connected
    "seen": {},                 # every underlying ticker name seen on the stream -> tick count (diagnostics)
    "last_error": None,
    "connect_attempts": 0,
    "last_msg_at": 0.0,
}

def _pyth_ws_auth_headers():
    """Same KALSHI-ACCESS-* scheme as REST, signed over PYTH_WS_PATH (no query string -
    see the CF Benchmarks fix above for why query strings must be excluded)."""
    ts = str(int(time.time() * 1000))
    key = load_private_key()
    sig = sign_request(key, ts, "GET", PYTH_WS_PATH)
    return [f"KALSHI-ACCESS-KEY: {KEY_ID}", f"KALSHI-ACCESS-TIMESTAMP: {ts}", f"KALSHI-ACCESS-SIGNATURE: {sig}"]

def _pyth_record_tick(underlying_ticker, value, ts):
    with _pyth_state["lock"]:
        buf = _pyth_state["buffers"].setdefault(underlying_ticker, [])
        buf.append((ts, value))
        cutoff = ts - PYTH_BUFFER_SECONDS
        i = 0
        while i < len(buf) and buf[i][0] < cutoff:
            i += 1
        if i:
            del buf[:i]
        _pyth_state["last_msg_at"] = time.time()

def _pyth_looks_like_natgas(name):
    if PYTH_NATGAS_TICKER_OVERRIDE:
        return name == PYTH_NATGAS_TICKER_OVERRIDE
    up = name.upper()
    if any(k in up for k in PYTH_NATGAS_MATCH):
        return True
    # Pyth futures-style codes, e.g. "Commodities.NGQ6/USD" - symbol part starting with NG
    sym = up.split(".")[-1].split("/")[0]
    return up.startswith("COMMODITIES.") and sym.startswith("NG") and len(sym) <= 6

def _pyth_note_natgas(name):
    """Called whenever a ticker name is seen. Wires natural gas into the source check the moment its
    (rolling) Pyth ticker shows up, and re-wires if the contract rolls to a new code."""
    if not _pyth_looks_like_natgas(name) or _pyth_state["natgas_ticker"] == name:
        return
    old = _pyth_state["natgas_ticker"]
    _pyth_state["natgas_ticker"] = name
    PYTH_UNDERLYING_TICKERS["KXNATGAS15M"] = name
    SOURCE_CHECK_INDEX_IDS["KXNATGAS15M"] = name
    SOURCE_CHECK_DEFAULT_SIGMA_BPS.setdefault(name, PYTH_NATGAS_DEFAULT_SIGMA_BPS)
    print(f"--> [PYTH] Natural gas {'resolved to' if not old else 'rolled from ' + old + ' to'} '{name}' - now included in the source check.")

def _pyth_wanted(name):
    return name in PYTH_UNDERLYING_TICKERS.values()

def _pyth_handle_message(raw):
    """Parses one websocket text frame. Returns True if it was a price tick."""
    try:
        msg = json.loads(raw)
    except (TypeError, ValueError):
        return False
    mtype = msg.get("type")
    if mtype == "pyth_value":
        m = msg.get("msg") or {}
        ticker = m.get("underlying_ticker")
        try:
            value = float(m.get("value_usd"))
        except (TypeError, ValueError):
            return False
        ts_ms = m.get("source_ts_ms") or m.get("received_at")
        ts = (ts_ms / 1000.0) if ts_ms else time.time()
        if not ticker or value <= 0:
            return False
        seen = _pyth_state["seen"]
        if ticker in seen or len(seen) < PYTH_SEEN_MAX:
            seen[ticker] = seen.get(ticker, 0) + 1
        _pyth_note_natgas(ticker)
        if _pyth_wanted(ticker):   # we subscribe to "all" (so natgas's unknown code streams), but only buffer what we use
            _pyth_record_tick(ticker, value, ts)
            return True
    elif mtype in ("pyth_value_underlying_list", "ok"):
        raw_msg = msg.get("msg")
        if isinstance(raw_msg, dict):
            names = raw_msg.get("underlying_tickers") or []
        elif isinstance(raw_msg, list):
            names = raw_msg
        else:
            names = []
        for n in (names or []):
            if isinstance(n, str):
                _pyth_state["seen"].setdefault(n, 0)
                _pyth_note_natgas(n)
    elif mtype == "error":
        _pyth_state["last_error"] = str(msg.get("msg"))
    return False

def _pyth_connection_loop():
    """Owns one persistent connection: connects, subscribes, reads frames, and
    reconnects with backoff on any drop. Runs for the life of the process."""
    attempt = 0
    while not _pyth_state["stop"]:
        if _ws_lib is None:
            _pyth_state["last_error"] = f"websocket-client not installed ({_WS_LIB_ERROR})"
            time.sleep(30)
            continue
        try:
            headers = _pyth_ws_auth_headers()
            ws = _ws_lib.create_connection(f"wss://{PYTH_WS_HOST}{PYTH_WS_PATH}", header=headers, timeout=10)
            _pyth_state["ws"] = ws
            # Kalshi's docs: underlying_tickers ["all"] streams every available underlying. Natural gas's
            # ticker is a rolling futures code we can't hardcode, so the old explicit-list subscribe never
            # included it. We take everything and only buffer the tickers we actually use.
            underlyings = ["all"]
            sub = {"id": 1, "cmd": "subscribe", "params": {"channels": ["pyth_value"], "underlying_tickers": underlyings}}
            ws.send(json.dumps(sub))
            # Also ask what's currently streaming (reply type pyth_value_underlying_list).
            ws.send(json.dumps({"id": 2, "cmd": "update_subscription", "params": {"sid": 1, "action": "underlying_list"}}))
            _pyth_state["connected"] = True
            _pyth_state["connect_attempts"] = 0
            attempt = 0
            print(f"--> [PYTH] Connected, subscribed to {underlyings or '(default)'}.")
            while not _pyth_state["stop"]:
                raw = ws.recv()
                if not raw:
                    break
                _pyth_handle_message(raw)
        except Exception as e:
            _pyth_state["last_error"] = str(e)
        _pyth_state["connected"] = False
        _pyth_state["connect_attempts"] += 1
        try:
            if _pyth_state["ws"]:
                _pyth_state["ws"].close()
        except Exception:
            pass
        if _pyth_state["stop"]:
            break
        wait = PYTH_RECONNECT_BACKOFF_SECONDS[min(attempt, len(PYTH_RECONNECT_BACKOFF_SECONDS) - 1)]
        attempt += 1
        time.sleep(wait)

def _pyth_get_points(underlying_ticker):
    """Same contract as _get_index_points: (points, None) or (None, reason)."""
    if _ws_lib is None:
        return None, f"websocket-client isn't installed on this machine ({_WS_LIB_ERROR}) - run: pip install websocket-client"
    if not PYTH_FEED_ENABLED:
        return None, "the Pyth feed is turned off (PYTH_FEED_ENABLED = False)"
    if not _pyth_state["connected"]:
        return None, f"not connected to the Pyth feed yet{' - last error: ' + _pyth_state['last_error'] if _pyth_state['last_error'] else ''}"
    with _pyth_state["lock"]:
        pts = list(_pyth_state["buffers"].get(underlying_ticker, []))
    if not pts:
        return None, f"connected, but no ticks received yet for {underlying_ticker}"
    if time.time() - pts[-1][0] > PYTH_STALE_SECONDS:
        return None, f"last {underlying_ticker} tick is {time.time() - pts[-1][0]:.0f}s old (feed looks stalled)"
    return pts, None

def _start_pyth_feed():
    if not PYTH_FEED_ENABLED or _pyth_state["thread"]:
        return
    t = threading.Thread(target=_pyth_connection_loop, daemon=True)
    _pyth_state["thread"] = t
    t.start()

def _format_pyth_status():
    lines = ["\U0001F6F0\uFE0F PYTH FEED (gold/silver/platinum/palladium" +
             (f"/{_pyth_state['natgas_ticker']}" if _pyth_state["natgas_ticker"] else ", natgas not yet found") + ")"]
    if _ws_lib is None:
        lines.append(f"\u274C Not running: websocket-client isn't installed ({_WS_LIB_ERROR}).")
        lines.append("Run: pip install websocket-client --break-system-packages, then restart the bot.")
        return "\n".join(lines)
    if not PYTH_FEED_ENABLED:
        lines.append("Off (PYTH_FEED_ENABLED = False).")
        return "\n".join(lines)
    lines.append("\u2705 Connected" if _pyth_state["connected"] else f"\u274C Not connected (attempt #{_pyth_state['connect_attempts']})")
    if _pyth_state["last_error"]:
        lines.append(f"Last error: {_pyth_state['last_error'][:200]}")
    with _pyth_state["lock"]:
        bufs = {k: len(v) for k, v in _pyth_state["buffers"].items()}
    if bufs:
        for k, n in bufs.items():
            with _pyth_state["lock"]:
                last = _pyth_state["buffers"][k][-1] if _pyth_state["buffers"][k] else None
            age = f"{time.time() - last[0]:.0f}s old" if last else "no ticks"
            lines.append(f"\u2022 {k}: {n} ticks buffered, newest {age}")
    else:
        lines.append("No ticks received yet.")
    if _pyth_state["natgas_ticker"]:
        lines.append(f"\u2022 natural gas ticker in use: {_pyth_state['natgas_ticker']}")
    elif PYTH_FEED_ENABLED and _pyth_state["connected"]:
        cand = sorted(k for k in _pyth_state["seen"] if not k.startswith("Metal."))[:25]
        lines.append(f"\u26A0\uFE0F Natural gas ticker not found among {len(_pyth_state['seen'])} streamed tickers.")
        if cand:
            lines.append("Non-metal tickers seen: " + ", ".join(cand))
            lines.append("If one of those is natural gas, set PYTH_NATGAS_TICKER_OVERRIDE to it.")
    return "\n".join(lines)
# --- PYTH WEBSOCKET FEED (end) ---

_index_fetch_locks = {}   # index_id -> Lock, so the prefetch thread and a decision never double-fetch

def _get_index_points(index_id, max_age=None):
    """Cached index history. Returns (points, None) or (None, reason).
    max_age overrides SOURCE_CHECK_CACHE_SECONDS for this call (the prefetch thread passes a short one).
    index_id starting with a known prefix (e.g. "Metal.") is a Pyth underlying
    ticker and comes from the websocket feed below; everything else is a CF
    Benchmarks id and comes from the REST passthrough, as before."""
    if index_id in PYTH_UNDERLYING_TICKERS.values() or index_id.startswith(("Metal.", "Commodities.")):
        return _pyth_get_points(index_id)
    ttl = SOURCE_CHECK_CACHE_SECONDS if max_age is None else max_age
    now = time.time()
    c = _source_state["cache"].get(index_id)
    if c and now - c[0] < ttl:
        return c[1], None
    with _index_fetch_locks.setdefault(index_id, threading.Lock()):
        # Someone else may have just refreshed it while we waited for the lock.
        now = time.time()
        c = _source_state["cache"].get(index_id)
        if c and now - c[0] < ttl:
            return c[1], None
        return _fetch_index_points_locked(index_id, now)

def _fetch_index_points_locked(index_id, now):
    if now < _source_state["backoff_until"]:
        return None, _source_state["unavailable_reason"] or "backing off after an earlier error"
    try:
        resp = kalshi_request("GET", f"/cfbenchmarks/values?id={index_id}")
    except Exception as e:
        msg = str(e)
        low = msg.lower()
        if any(k in low for k in ("403", "401", "forbidden", "unauthor", "entitle", "not authorized")):
            reason = (f"the index request was rejected as unauthorized ({msg[:120]}) - Kalshi says this endpoint is "
                      f"already enabled on the account, so this is a request-signing/credentials problem")
            _source_state["backoff_until"] = now + 30
        else:
            reason = f"index request failed ({msg[:120]})"
            _source_state["backoff_until"] = now + 2     # was 10s: a single network blip used to blind the panic exit that long
        _source_state["unavailable_reason"] = reason
        return None, reason
    pts = _parse_index_points(resp)
    try:
        _source_state["last_shape"] = (json.dumps(resp)[:300] if not pts else f"{len(pts)} values parsed")
    except Exception:
        _source_state["last_shape"] = str(type(resp))
    if not pts:
        reason = "index response contained no readable {time, value} pairs"
        _source_state["unavailable_reason"] = reason
        _source_state["backoff_until"] = now + 5
        return None, reason
    _source_state["unavailable_reason"] = None
    _source_state["cache"][index_id] = (now, pts)
    return pts, None

def _get_market_info(market_ticker):
    """(close_ts, floor_strike, strike_type) for a market, cached - they never change once the market exists."""
    info = _source_state["market_info"].get(market_ticker)
    if info:
        return info
    m = (kalshi_request("GET", f"/markets/{market_ticker}") or {}).get("market") or {}
    close_ts = None
    ct = _market_close_time_cache.get(market_ticker)
    if ct:
        close_ts = ct.timestamp()
    elif m.get("close_time"):
        close_ts = _parse_ts(m["close_time"])
    try:
        floor_strike = float(m["floor_strike"]) if m.get("floor_strike") is not None else None
    except (TypeError, ValueError):
        floor_strike = None
    info = {"close_ts": close_ts, "floor_strike": floor_strike, "strike_type": m.get("strike_type")}
    if len(_source_state["market_info"]) > 100:
        _source_state["market_info"].clear()
    _source_state["market_info"][market_ticker] = info
    return info

# While a source-mode position is open, keep its index fresh in the background so the
# panic check just reads memory instead of waiting on a REST call. Polls only while
# holding (each index call costs 5x a normal read), so idle token use is unchanged.
SOURCE_PREFETCH_SECONDS = 0.5

SOURCE_PREFETCH_BUY_WINDOW_SECONDS = 1.0   # index refresh cadence while a market is inside the source-mode buy window
_source_mode_watch = {}                     # index_id -> last time a market using it was scanned inside the buy window

def _source_mode_watch_index(market_ticker):
    """Called by the buy scan: marks this market's index as 'needs fresh data' for the prefetch thread."""
    idx = SOURCE_CHECK_INDEX_IDS.get(_series_of(market_ticker))
    if idx:
        _source_mode_watch[idx] = time.time()

def _source_prefetch_loop():
    while True:
        try:
            if SOURCE_MODE_ENABLED:
                wanted = {}   # index_id -> max_age to refresh at
                now = time.time()
                for idx, seen in list(_source_mode_watch.items()):
                    if now - seen < 5.0:                       # a buy-window market scanned in the last few seconds
                        wanted[idx] = SOURCE_PREFETCH_BUY_WINDOW_SECONDS
                with positions_lock:
                    held = [t for t in open_positions if t in _source_mode_positions]
                for idx in {SOURCE_CHECK_INDEX_IDS.get(_series_of(t)) for t in held} - {None}:
                    wanted[idx] = SOURCE_PREFETCH_SECONDS      # holding -> fastest
                for idx, age in wanted.items():
                    _get_index_points(idx, max_age=age)
        except Exception as e:
            print(f"--> [WARNING] Source prefetch error (continuing): {e}")
        time.sleep(0.1)

def _realized_sigma_bps(pts, now_ts, idx, lookback=None):
    """Realized vol in bps per sqrt(second) from recent 1s ticks (RMS of normalized log returns), floored.
    lookback overrides SOURCE_CHECK_VOL_LOOKBACK_SECONDS (source mode uses a short one to spot sudden chop)."""
    default = SOURCE_CHECK_DEFAULT_SIGMA_BPS.get(idx, 1.0)
    recent = [p for p in pts if p[0] >= now_ts - (lookback or SOURCE_CHECK_VOL_LOOKBACK_SECONDS)]
    rets = []
    for (t0, v0), (t1, v1) in zip(recent, recent[1:]):
        dt = t1 - t0
        if 0.2 < dt <= 3.0 and v0 > 0 and v1 > 0:
            rets.append(math.log(v1 / v0) * 1e4 / math.sqrt(dt))
    realized = math.sqrt(sum(x * x for x in rets) / len(rets)) if len(rets) >= 15 else None
    if realized is None:
        return default, None
    return max(realized, SOURCE_CHECK_SIGMA_FLOOR_FRACTION * default), realized

def _source_check_eval(market_ticker, side, now_ts=None):
    """Verdict for buying `side` ('yes'/'no') of this market. Returns a dict;
    out['verdict'] is True (passes), False (veto) or None (couldn't judge -> fail open)."""
    side = side.lower()
    out = {"verdict": None, "reason": "", "side": side}
    series = _series_of(market_ticker)
    idx = SOURCE_CHECK_INDEX_IDS.get(series)
    if not idx:
        out["reason"] = f"{series} has no public index to check against"
        return out
    pts, err = _get_index_points(idx)
    if pts is None:
        out["reason"] = f"index feed unavailable: {err}"
        out["feed_error"] = True
        return out
    now = now_ts if now_ts is not None else time.time()
    latest_ts, V = pts[-1]
    out.update(index=idx, V=V, age=now - latest_ts, n_points=len(pts))
    if now - latest_ts > SOURCE_CHECK_MAX_AGE_SECONDS:
        out["reason"] = f"index is stale (newest print {now - latest_ts:.0f}s old)"
        out["feed_error"] = True
        return out
    try:
        info = _get_market_info(market_ticker)
    except Exception as e:
        out["reason"] = f"couldn't read market details ({e})"
        return out
    close_ts = info["close_ts"]
    if not close_ts:
        out["reason"] = "market close time unknown"
        return out
    if info["strike_type"] not in (None, "greater", "greater_or_equal"):
        out["reason"] = f"unsupported strike type '{info['strike_type']}'"
        return out
    r = close_ts - now
    out["remaining"] = r
    if r <= 0:
        out["reason"] = "market already closed"
        return out

    # Strike: Kalshi's floor_strike, else the 60s index average before OPEN (= 15 min before close).
    window_open = close_ts - 900
    open_pts = [v for (t, v) in pts if window_open - 60 <= t <= window_open]
    computed_K = (sum(open_pts) / len(open_pts)) if len(open_pts) >= 45 else None
    K = info["floor_strike"] if info["floor_strike"] else computed_K
    out["strike_source"] = "kalshi floor_strike" if info["floor_strike"] else "computed from index history"
    if K is None or K <= 0:
        out["reason"] = "couldn't determine the strike"
        return out
    if info["floor_strike"] and computed_K:
        out["strike_vs_computed_bps"] = (info["floor_strike"] - computed_K) / computed_K * 1e4
    if abs(K - V) / V * 100.0 > SOURCE_CHECK_MAX_STRIKE_GAP_PCT:
        out["reason"] = (f"strike {K:,.2f} and index {V:,.2f} are {abs(K - V) / V * 100:.1f}% apart - "
                         f"looks like a data/units problem, not vetoing")
        return out

    # Project the final 60s average. Part of it may already have happened.
    L = 60.0
    if r >= L:
        projected = V
        var_secs = (r - L) + L / 3.0
    else:
        done = [v for (t, v) in pts if close_ts - L <= t <= now]
        covered = L - r
        obs_mean = (sum(done) / len(done)) if (covered >= 1 and len(done) >= 0.5 * covered) else V
        projected = (obs_mean * covered + V * r) / L
        var_secs = (r ** 3) / (3.0 * L * L)
    sigma, realized = _realized_sigma_bps(pts, now, idx)
    # How choppy is it RIGHT NOW vs this index's normal? Uses the larger of the slow (3m) and fast
    # (SOURCE_MODE_ADAPT_FAST_LOOKBACK_SECONDS) realized vol, so a sudden spike registers quickly while
    # a sustained choppy stretch keeps registering. 1.0 = normal. None = not enough ticks to say.
    _, fast_realized = _realized_sigma_bps(pts, now, idx, lookback=SOURCE_MODE_ADAPT_FAST_LOOKBACK_SECONDS)
    _vols = [v for v in (realized, fast_realized) if v is not None]
    vol_ratio = (max(_vols) / SOURCE_CHECK_DEFAULT_SIGMA_BPS.get(idx, 1.0)) if _vols else None
    std_bps = max(sigma * math.sqrt(max(var_secs, 0.0)), 0.05)
    margin_yes_bps = (projected - K) / K * 1e4
    margin_bps = margin_yes_bps if side == "yes" else -margin_yes_bps
    z = margin_bps / std_bps
    out.update(K=K, projected=projected, sigma=sigma, realized_sigma=realized, std_bps=std_bps,
               margin_bps=margin_bps, z=z, vol_ratio=vol_ratio)
    if margin_bps < SOURCE_CHECK_MIN_MARGIN_BPS or z < SOURCE_CHECK_MIN_Z:
        out["verdict"] = False
        out["reason"] = (f"{idx} average projects {margin_bps:+.1f}bps vs the strike for {side.upper()} "
                         f"(z={z:.1f}, need >= {SOURCE_CHECK_MIN_Z:g} and >= {SOURCE_CHECK_MIN_MARGIN_BPS:g}bps; "
                         f"{r:.0f}s left)")
    else:
        out["verdict"] = True
        out["reason"] = f"{idx} average projects {margin_bps:+.1f}bps (z={z:.1f}) for {side.upper()}"
    return out

def _source_check_allows(market_ticker, side):
    """Called from the buy path. True = go ahead. See the block comment above."""
    st = _source_state["stats"]
    try:
        res = _source_check_eval(market_ticker, side)
    except Exception as e:
        res = {"verdict": None, "reason": f"source check error: {e}"}
    st["checks"] += 1
    if res["verdict"] is True:
        st["allowed"] += 1
        return True
    if res["verdict"] is None:
        st["failopen"] += 1
        key = (market_ticker, res["reason"][:60])
        if key not in _source_state["logged"]:
            if len(_source_state["logged"]) > 300:
                _source_state["logged"].clear()
            _source_state["logged"].add(key)
            print(f"--> [SOURCE CHECK] Not judging {market_ticker} ({res['reason']}) - allowing the buy.")
        if res.get("feed_error") and res["reason"][:40] not in _source_state["alerted"]:
            _source_state["alerted"].add(res["reason"][:40])
            push_alert(f"\U0001F6E1\uFE0F Source check can't verify right now: {res['reason']}.\n"
                       f"Buys are NOT being checked against the index until this clears. /sourcecheck shows details.")
        return True
    # verdict False
    if SOURCE_CHECK_SHADOW:
        st["would_veto"] += 1
        print(f"--> [SOURCE CHECK - SHADOW] Would have vetoed {side.upper()} on {market_ticker}: {res['reason']}")
        if market_ticker not in _source_state["alerted"]:
            _source_state["alerted"].add(market_ticker)
            push_alert(f"\U0001F6E1\uFE0F Source check (shadow) WOULD have blocked {side.upper()} on {market_ticker}:\n{res['reason']}")
        return True
    st["vetoed"] += 1
    print(f"--> [SOURCE CHECK] Vetoing {side.upper()} buy on {market_ticker}: {res['reason']}")
    if market_ticker not in _source_state["alerted"]:
        _source_state["alerted"].add(market_ticker)
        if len(_source_state["alerted"]) > 300:
            _source_state["alerted"].clear()
        push_alert(f"\U0001F6E1\uFE0F Source check BLOCKED {side.upper()} on {market_ticker}:\n{res['reason']}")
    return False

def _norm_cdf(z):
    """Chance a standard bell-curve variable lands below z (used to turn a z-score into a win chance)."""
    return 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))

def _fmt_dur(seconds):
    seconds = max(0, int(round(seconds)))
    return f"{seconds // 60}m {seconds % 60:02d}s" if seconds >= 60 else f"{seconds}s"

def _fmt_usd(x, signed=False):
    sign = ("+" if x >= 0 else "-") if signed else ("-" if x < 0 else "")
    return f"{sign}${abs(x):,.2f}"

def _fmt_chance(p):
    return "99.9%+" if p > 0.9995 else (f"{p * 100:.0f}%" if p < 0.995 else f"{p * 100:.1f}%")

def _win_phrase(p):
    return "win chance over 99.9%" if p > 0.9995 else f"win chance about {_fmt_chance(p)}"

def _format_source_check_status():
    """/sourcecheck: a plain-English read of the live index vs the strike, and what the bot would do with a YES or NO buy right now."""
    st = _source_state["stats"]
    need_prob = _norm_cdf(SOURCE_CHECK_MIN_Z)
    if not SOURCE_CHECK_ENABLED:
        mode = "OFF - buys are not being checked"
    elif SOURCE_CHECK_SHADOW:
        mode = f"SHADOW - tells you what it WOULD block (needs {_fmt_chance(need_prob)} win chance), but lets buys through"
    else:
        mode = f"ON - blocks any buy the real index says is under {_fmt_chance(need_prob)} likely to win"
    lines = ["\U0001F6E1\uFE0F SOURCE CHECK", mode, ""]

    ticker = _active_market_cache.get("ticker")
    if not ticker:
        try:
            data = kalshi_request("GET", f"/markets?series_ticker={ACTIVE_SERIES_TICKER}&status=open")
            ms = sorted(data.get("markets", []), key=lambda m: m.get("close_time") or "")
            ticker = ms[0]["ticker"] if ms else None
        except Exception:
            ticker = None
    if not ticker:
        lines.append("No open market to test against right now.")
        return "\n".join(lines)

    res = {}
    for sd in ("yes", "no"):
        try:
            res[sd] = _source_check_eval(ticker, sd)
        except Exception as e:
            res[sd] = {"verdict": None, "reason": f"error: {e}"}
    r = res["yes"]
    lines.append(f"\U0001F4CD {ticker}")

    if "V" not in r and not r.get("feed_error"):
        # By this point only natgas should land here (before its rolling Pyth ticker is
        # discovered) - gold/platinum/palladium now have real index ids, same as BTC/ETH/SOL.
        lines += ["", f"\u2796 {_series_name(_series_of(ticker))} has no settlement index to check against yet "
                      f"(run /pythfeed to see why) - buys go through as normal."]
    elif "V" not in r:  # couldn't read the index (CF Benchmarks REST error, or Pyth websocket down/no ticks)
        why = r["reason"].replace("index feed unavailable: ", "")
        lines += ["", f"\u26A0\uFE0F Can't read the index right now: {why}",
                  "Buys are NOT being checked at the moment - they go through as normal."]
        if _source_state.get("last_shape"):
            lines.append(f"What Kalshi sent back: {_source_state['last_shape']}")
    else:
        if "remaining" in r:
            lines.append(f"\u23F1 {_fmt_dur(r['remaining'])} left")
        lines.append("")
        lines.append(f"\U0001F4E1 {r['index']} is {_fmt_usd(r['V'])} ({'live' if r['age'] <= 3 else 'delayed'}, {r['age']:.0f}s old)")
        if "K" in r:
            lead_yes = r["projected"] - r["K"]
            lines.append(f"\U0001F3AF Strike to beat: {_fmt_usd(r['K'])}")
            lines.append(f"\U0001F4C8 Projected final average: {_fmt_usd(r['projected'])} "
                         f"({_fmt_usd(lead_yes, True)} vs the strike)")
            need_bps = max(SOURCE_CHECK_MIN_MARGIN_BPS, SOURCE_CHECK_MIN_Z * r["std_bps"])
            need_usd = need_bps / 1e4 * r["K"]
            lines.append(f"\U0001F4CF Lead needed to pass right now: {_fmt_usd(need_usd, True)} "
                         f"(bigger early on, shrinks as the clock runs down)")
            lines.append("")
            for sd in ("yes", "no"):
                x = res[sd]
                label = f"BUY {sd.upper()}"
                lead = lead_yes if sd == "yes" else -lead_yes
                if x["verdict"] is None:
                    lines.append(f"\u2796 {label}: not checked - {x['reason']}")
                elif x["verdict"] is True:
                    lines.append(f"\u2705 {label}: OK - lead {_fmt_usd(lead, True)} beats the {_fmt_usd(need_usd, True)} needed "
                                 f"({_win_phrase(_norm_cdf(x['z']))})")
                elif lead < 0:
                    lines.append(f"\u26D4 {label}: BLOCKED - the index is on the wrong side of the strike ({_fmt_usd(lead, True)})")
                else:
                    lines.append(f"\u26D4 {label}: BLOCKED - lead is only {_fmt_usd(lead, True)}, needs {_fmt_usd(need_usd, True)} "
                                 f"({_win_phrase(_norm_cdf(x['z']))})")
        else:
            lines += ["", f"\u2796 Not checked: {r['reason']}"]

        detail = []
        if "K" in r:
            detail.append(f"strike from {r['strike_source']}")
            sig = f"{r['sigma']:.2f}"
            detail.append(f"price jumpiness {sig} bps/\u221as ({'measured' if r.get('realized_sigma') else 'default, too few ticks'})")
        detail.append(f"{r['n_points']} index prints")
        lines += ["", "Details: " + " \u00b7 ".join(detail)]
        if abs(r.get("strike_vs_computed_bps", 0.0)) > 0.5:
            lines.append(f"\u26A0\uFE0F Kalshi's strike differs from the index-computed one by {r['strike_vs_computed_bps']:+.1f} bps.")

    lines += ["", f"Since start: {st['checks']} checked \u00b7 {st['vetoed']} blocked \u00b7 "
                  f"{st['would_veto']} shadow-blocked \u00b7 {st['failopen']} couldn't check",
              f"Tune: /setsource z <n> (now {SOURCE_CHECK_MIN_Z:g} = {_fmt_chance(need_prob)})  \u00b7  /sourcecheck shadow | off | on"]
    return "\n".join(lines)
# --- SOURCE CHECK (end) ---

# --- SOURCE MODE (start) ---
# A separate way of trading: instead of your price triggers, buy/sell decisions
# come straight from the source check's win-probability. Only covers BTC/ETH/SOL
# (the series with a public settlement index - see SOURCE_CHECK_INDEX_IDS).
# Gold/platinum/palladium/natgas settle on Pyth, and Kalshi only exposes Pyth
# data over an authenticated WEBSOCKET, not the REST API this bot polls - I
# could not confirm a REST endpoint for it, so they're NOT included here.
# Commands: /sourcemode on|off, /sourcemode autosell on|off, /setsourcemode buy|sell <pct>
SOURCE_MODE_ENABLED = False
SOURCE_MODE_WINDOW_MINUTES = 5.0     # only active inside the last N minutes of a window
SOURCE_MODE_BUY_PROB = 0.87          # buy whichever side's win chance is >= this
SOURCE_MODE_SELL_PROB = 0.05         # panic-sell the held side once its win chance drops BELOW this
SOURCE_MODE_AUTOSELL = True          # if False, normal take-profit (PROFIT_TARGET_DOLLARS/TAKE_PROFIT_BID_CENTS) is skipped for source-mode positions - only the panic-exit and stop-loss still protect them
SOURCE_MODE_MIN_SELL_SECONDS_LEFT = 3   # don't bother panic-selling in literally the last few seconds - nothing left to execute against

_source_mode_positions = set()   # tickers opened BY source mode, so the autosell toggle only affects those
_source_mode_alerted = set()

def _source_mode_read_full(market_ticker, side):
    """dict(p, vol_ratio, feed_error, reason). p is None when the win chance can't be judged;
    feed_error says whether that's because the data feed is down/stale (vs. e.g. an unsupported market)."""
    out = {"p": None, "vol_ratio": None, "feed_error": False, "reason": ""}
    try:
        r = _source_check_eval(market_ticker, side)
    except Exception as e:
        out.update(reason=f"check error: {e}", feed_error=True)
        return out
    out["reason"] = r.get("reason", "")
    out["feed_error"] = bool(r.get("feed_error"))
    if "z" in r:
        out["p"] = _norm_cdf(r["z"])
        out["vol_ratio"] = r.get("vol_ratio")
    return out

def _source_mode_read(market_ticker, side):
    """(win chance 0-1, vol_ratio) for `side` right now, or (None, None) if it can't be
    judged (feed down, no public index, market closed, etc). vol_ratio is how choppy the
    index is vs its normal (1.0 = normal), or None if there weren't enough ticks."""
    r = _source_mode_read_full(market_ticker, side)
    return r["p"], r["vol_ratio"]

def _source_mode_prob(market_ticker, side):
    """Win chance (0-1) for `side` right now, or None if it can't be judged."""
    return _source_mode_read(market_ticker, side)[0]

# --- ADAPTIVE PANIC-SELL LINE ---
# When the index gets choppy, the panic-sell line is raised for THAT market only (so it sells
# sooner), then relaxes back to your normal SOURCE_MODE_SELL_PROB on its own once things calm.
# Nothing is ever written to your saved setting: the effective line is recomputed on every
# check from live volatility, so a crash/restart mid-chop can't leave a raised value stuck.
#   vol <= START_RATIO x normal      -> your normal line
#   vol >= FULL_RATIO  x normal      -> MAX_SELL_PROB (never above buy line - 2 pts)
#   in between                       -> scaled linearly
# Once raised, it stays at least that high for HOLD_SECONDS after the last choppy reading
# (so one calm tick in the middle of a flip doesn't relax it), then snaps back.
# Trade-off: a higher line also sells some positions that would have recovered. It is
# deliberately mild by default - tune with /setsourcemode tight <pct>, or /sourcemode adapt off.
SOURCE_MODE_ADAPT_ENABLED = True
SOURCE_MODE_ADAPT_MAX_SELL_PROB = 0.91
SOURCE_MODE_ADAPT_START_RATIO = 1.5
SOURCE_MODE_ADAPT_FULL_RATIO = 3.0
SOURCE_MODE_ADAPT_HOLD_SECONDS = 90
SOURCE_MODE_ADAPT_FAST_LOOKBACK_SECONDS = 30

# --- VOLATILITY-SCALED BUY / SELL LINES ("scale mode") ---
# Both lines follow how choppy the index is RIGHT NOW (vol ratio: 1.0 = that index's normal; uses the faster of
# the 30s and 3m measures so it reacts quickly). Calm market -> buy earlier and keep the panic line tight under
# it; wild market -> demand more certainty to buy and give the panic line more room. Straight-line blend
# between the two anchors; the narrow ratio range (0.7x..2.0x by default) is what makes it "sensitive".
#   calm (vol <= CALM_RATIO):  buy >= CALM_BUY,  panic below CALM_SELL      (default 90% / 88%  -> 2-point window)
#   wild (vol >= HOT_RATIO):   buy >= HOT_BUY,   panic below HOT_SELL       (default 97% / 90%)
# The panic line can only RATCHET UP during a hold (SOURCE_MODE_ADAPT_HOLD_SECONDS after the last time it was
# that high) so one calm tick mid-flip can't relax it. If volatility can't be measured, your saved buy/sell
# lines are used. When scale mode is ON it replaces the older "adaptive sell line" and your saved buy/sell.
SOURCE_MODE_SCALE_ENABLED = False
SOURCE_MODE_SCALE_CALM_BUY = 0.90
SOURCE_MODE_SCALE_CALM_SELL = 0.88
SOURCE_MODE_SCALE_HOT_BUY = 0.97
SOURCE_MODE_SCALE_HOT_SELL = 0.90
SOURCE_MODE_SCALE_CALM_RATIO = 0.7
SOURCE_MODE_SCALE_HOT_RATIO = 2.0
SOURCE_MODE_SCALE_MIN_GAP = 0.01     # panic line always at least this far below the buy line
_source_mode_scale_hold = {}         # market_ticker -> {"sell": line, "until": epoch}

def _source_mode_scaled_lines(vol_ratio):
    """(buy, sell) for this volatility, or None if scale mode is off or volatility is unknown."""
    if not SOURCE_MODE_SCALE_ENABLED or vol_ratio is None:
        return None
    span = max(SOURCE_MODE_SCALE_HOT_RATIO - SOURCE_MODE_SCALE_CALM_RATIO, 1e-9)
    t = min(1.0, max(0.0, (vol_ratio - SOURCE_MODE_SCALE_CALM_RATIO) / span))
    buy = SOURCE_MODE_SCALE_CALM_BUY + t * (SOURCE_MODE_SCALE_HOT_BUY - SOURCE_MODE_SCALE_CALM_BUY)
    sell = SOURCE_MODE_SCALE_CALM_SELL + t * (SOURCE_MODE_SCALE_HOT_SELL - SOURCE_MODE_SCALE_CALM_SELL)
    buy = min(buy, 0.999)
    return buy, min(sell, buy - SOURCE_MODE_SCALE_MIN_GAP)

def _source_mode_buy_line(market_ticker, vol_ratio):
    s = _source_mode_scaled_lines(vol_ratio)
    return s[0] if s else SOURCE_MODE_BUY_PROB

def _source_mode_sell_line(market_ticker, vol_ratio):
    """The panic-sell line in effect for this market right now."""
    if not SOURCE_MODE_SCALE_ENABLED:
        _source_mode_scale_hold.pop(market_ticker, None)
        return _source_mode_effective_sell_prob(market_ticker, vol_ratio)
    s = _source_mode_scaled_lines(vol_ratio)
    if s is None:
        return _source_mode_effective_sell_prob(market_ticker, None)    # can't measure vol -> your saved line
    now, sell = time.time(), s[1]
    held = _source_mode_scale_hold.get(market_ticker)
    if held and now < held["until"]:
        if sell >= held["sell"]:
            _source_mode_scale_hold[market_ticker] = {"sell": sell, "until": now + SOURCE_MODE_ADAPT_HOLD_SECONDS}
        else:
            sell = held["sell"]
    else:
        if len(_source_mode_scale_hold) > 100:
            _source_mode_scale_hold.clear()
        _source_mode_scale_hold[market_ticker] = {"sell": sell, "until": now + SOURCE_MODE_ADAPT_HOLD_SECONDS}
    return sell

_source_mode_tight = {}   # market_ticker -> {"prob": raised line, "until": epoch}

def _source_mode_tight_summary():
    """' | raised now: TICKER 88% (45s left)' for any market currently tightened, else ''."""
    now = time.time()
    live = [f"{k} {v['prob']:.0%} ({v['until'] - now:.0f}s left)" for k, v in list(_source_mode_tight.items()) if v["until"] > now]
    return (" | raised now: " + ", ".join(live)) if live else ""

def _source_mode_effective_sell_prob(market_ticker, vol_ratio):
    """The panic-sell line to use for this market right now (see block comment above)."""
    base = SOURCE_MODE_SELL_PROB
    if not SOURCE_MODE_ADAPT_ENABLED:
        _source_mode_tight.pop(market_ticker, None)
        return base
    ceiling = min(SOURCE_MODE_ADAPT_MAX_SELL_PROB, SOURCE_MODE_BUY_PROB - 0.02)
    now = time.time()
    if len(_source_mode_tight) > 100:   # housekeeping: drop long-expired entries from old markets
        for k in [k for k, v in _source_mode_tight.items() if now > v["until"] + 3600]:
            _source_mode_tight.pop(k, None)
    state = _source_mode_tight.get(market_ticker)
    if state is not None and now >= state["until"]:
        print(f"--> [SOURCE MODE] {market_ticker}: calm again - panic-sell line back to {base:.0%} (was {state['prob']:.0%}).")
        _source_mode_tight.pop(market_ticker, None)
        state = None

    if vol_ratio is not None and ceiling > base and vol_ratio > SOURCE_MODE_ADAPT_START_RATIO:
        span = max(SOURCE_MODE_ADAPT_FULL_RATIO - SOURCE_MODE_ADAPT_START_RATIO, 1e-9)
        frac = min(1.0, (vol_ratio - SOURCE_MODE_ADAPT_START_RATIO) / span)
        target = base + frac * (ceiling - base)
        if state is None:
            _source_mode_tight[market_ticker] = {"prob": target, "until": now + SOURCE_MODE_ADAPT_HOLD_SECONDS}
            print(f"--> [SOURCE MODE] {market_ticker}: CHOPPY (vol {vol_ratio:.1f}x normal) - panic-sell line raised "
                  f"{base:.0%} -> {target:.0%} for at least {SOURCE_MODE_ADAPT_HOLD_SECONDS}s.")
            push_alert(f"\U0001F30A SOURCE MODE: {market_ticker} is choppy (vol {vol_ratio:.1f}x normal). Panic-sell line "
                       f"raised {base:.0%} \u2192 {target:.0%}; it relaxes back to {base:.0%} after "
                       f"{SOURCE_MODE_ADAPT_HOLD_SECONDS}s of calm.")
            return target
        state["prob"] = max(state["prob"], target)          # only ratchets UP while active
        state["until"] = now + SOURCE_MODE_ADAPT_HOLD_SECONDS  # still choppy -> keep holding
        return state["prob"]
    return state["prob"] if state is not None else base

# --- MOMENTUM-PROOF ENTRY ---
# Problem this fixes: the old entry was a GOOD-TILL-CANCELED limit order pinned at the ask the bot saw
# a moment earlier, and the market was marked "traded" before anyone knew whether it filled. When the
# price ran (exactly when win chance climbs fast), the ask moved above the order, the order just sat
# there unfilled, the market was burned for good - and the stale order could even fill LATER on a
# reversal, i.e. at the worst possible moment.
# Now: the entry is an IMMEDIATE-OR-CANCEL order priced a few cents ABOVE the ask (you still fill at the
# best available prices first - the extra only matters if the ask really moved), chased only while the
# price is at or below the model's own win chance. A miss leaves nothing resting, re-reads the book and
# win chance, and tries again within the same scan; the market is only marked traded once something fills.
SOURCE_MODE_CHASE_ENABLED = True
SOURCE_MODE_CHASE_CENTS = 3                  # max cents above the seen ask the entry may pay
SOURCE_MODE_MAX_BUY_CENTS = 99               # never pay above this (99 = no extra cap vs. before)
SOURCE_MODE_ENTRY_ATTEMPTS = 3               # IOC tries per scan cycle (each re-reads book + win chance)
SOURCE_MODE_MAX_ENTRY_TRIES_PER_MARKET = 12  # total misses tolerated per market before giving up on it
SOURCE_MODE_IOC_ENTRY = True                 # auto-flips to False if Kalshi rejects IOC buys (falls back to the old resting order)
_source_mode_entry_tries = {}                # market_ticker -> number of entry orders sent

def _source_mode_fetch_ask(market_ticker, side):
    """Current ask in cents for BUYING `side` (100 - best opposite bid), or None."""
    try:
        book = kalshi_request("GET", f"/markets/{market_ticker}/orderbook")
        ob = (book or {}).get("orderbook_fp") or (book or {}).get("orderbook") or book or {}
        def top_bid_cents(bids):
            if not bids: return None
            e = bids[-1] if isinstance(bids, list) else bids
            v = e[0] if isinstance(e, list) else e
            return float(v) * 100.0 if (isinstance(v, str) or float(v) <= 1.0) else float(v)
        opposite_key = "no_dollars" if side == "yes" else "yes_dollars"
        opposite_legacy = "no" if side == "yes" else "yes"
        opp_bid = top_bid_cents(ob.get(opposite_key) or ob.get(opposite_legacy))
        return None if opp_bid is None else 100.0 - opp_bid
    except Exception as e:
        print(f"--> [WARNING] Source mode couldn't read the book for {market_ticker}: {e}")
        return None

def _source_mode_entry_limit(ask, p):
    """Limit price (cents) for an entry: the ask we saw, plus up to CHASE_CENTS of slack - but the slack
    never takes the price above the model's own win chance (don't chase into negative EV) or MAX_BUY_CENTS.
    The ask itself is always allowed (as before), unless it's above MAX_BUY_CENTS -> None."""
    base = int(math.ceil(ask))
    if base > SOURCE_MODE_MAX_BUY_CENTS:
        return None
    if not (SOURCE_MODE_CHASE_ENABLED and SOURCE_MODE_IOC_ENTRY):
        return base   # chasing needs IOC (a resting order with slack could fill later on a reversal)
    return max(base, min(base + SOURCE_MODE_CHASE_CENTS, int(p * 100), SOURCE_MODE_MAX_BUY_CENTS))

def _source_mode_scan(market_ticker, remaining_minutes, yes_ask=None, no_ask=None):
    """Called from the scan loop. Buys whichever side clears SOURCE_MODE_BUY_PROB,
    using the normal order path (so sizing/budget/fees/logging are unchanged).
    yes_ask/no_ask: the asks the caller just read, so the first attempt needs no extra orderbook call."""
    global SOURCE_MODE_IOC_ENTRY
    if remaining_minutes > SOURCE_MODE_WINDOW_MINUTES or remaining_minutes < 0.05:
        return False
    if market_ticker in traded_tickers:
        return False
    _source_mode_watch_index(market_ticker)   # keep this market's index fresh in the background
    if _source_mode_entry_tries.get(market_ticker, 0) >= SOURCE_MODE_MAX_ENTRY_TRIES_PER_MARKET:
        return False
    best_side, best_p, vol_ratio = None, 0.0, None
    for side in ("yes", "no"):
        p, v = _source_mode_read(market_ticker, side)
        if p is not None and p > best_p:
            best_side, best_p, vol_ratio = side, p, v
    buy_line = _source_mode_buy_line(market_ticker, vol_ratio)
    if best_side is None or best_p < buy_line:
        return False

    p = best_p
    ask = yes_ask if best_side == "yes" else no_ask
    for attempt in range(max(1, SOURCE_MODE_ENTRY_ATTEMPTS)):
        if attempt > 0 or not ask or ask <= 0:
            ask = _source_mode_fetch_ask(market_ticker, best_side)          # fresh book
        if attempt > 0:
            p2, v2 = _source_mode_read(market_ticker, best_side)             # fresh win chance
            buy_line = _source_mode_buy_line(market_ticker, v2)
            vol_ratio = v2
            if p2 is None or p2 < buy_line:
                print(f"--> [SOURCE MODE] {market_ticker}: win chance no longer clears the buy line "
                      f"({'n/a' if p2 is None else format(p2, '.1%')}) - standing down.")
                return False
            p = p2
        if ask is None or ask <= 0 or ask >= 100:
            return False
        limit = _source_mode_entry_limit(ask, p)
        if limit is None:
            print(f"--> [SOURCE MODE] {market_ticker}: ask {ask:g}\u00a2 is above the {SOURCE_MODE_MAX_BUY_CENTS}\u00a2 buy cap - skipping.")
            return False

        use_ioc = SOURCE_MODE_CHASE_ENABLED and SOURCE_MODE_IOC_ENTRY
        _source_mode_entry_tries[market_ticker] = _source_mode_entry_tries.get(market_ticker, 0) + 1
        if len(_source_mode_entry_tries) > 200:
            _source_mode_entry_tries.clear()
        local_time_str = time.strftime('%I:%M:%S %p')
        print(f"[{local_time_str}] [SOURCE MODE] {market_ticker}: {best_side.upper()} win chance "
              f"{p:.1%} >= {buy_line:.0%}{'' if vol_ratio is None else f' (vol {vol_ratio:.1f}x)'} - buying (ask {ask:g}\u00a2, limit {limit}\u00a2"
              f"{', IOC' if use_ioc else ''}, try {attempt + 1}/{SOURCE_MODE_ENTRY_ATTEMPTS})")
        response = execute_order(market_ticker, best_side, limit,
                                 tif="immediate_or_cancel" if use_ioc else "good_till_canceled")

        if response is None:
            err = (_last_order_error or "").lower()
            if use_ioc and ("time_in_force" in err or "immediate_or_cancel" in err):
                SOURCE_MODE_IOC_ENTRY = False
                print("--> [SOURCE MODE] [WARNING] Kalshi rejected an IOC entry order - falling back to the old "
                      "resting-order entry for this session. (Entries still work, but won't chase.)")
                continue
            # Any other failure: we can't be sure whether an order reached the exchange, so keep the old
            # conservative behavior - mark the market traded and don't resend blindly.
            traded_tickers.add(market_ticker)
            return True

        with positions_lock:
            filled = market_ticker in open_positions
        if filled:
            traded_tickers.add(market_ticker)
            _source_mode_positions.add(market_ticker)
            push_alert(f"\U0001F6F0\uFE0F SOURCE MODE buy: {market_ticker} {best_side.upper()} "
                       f"(win chance {p:.0%})")
            return True
        if not use_ioc:
            # Old-style resting order: it may still fill later, so the market stays marked as traded.
            traded_tickers.add(market_ticker)
            _source_mode_positions.add(market_ticker)
            return True
        # IOC miss: the price ran. Nothing is resting; loop and try again against a fresh book.
    return False   # not marked traded -> the next scan cycle tries again (up to the per-market cap)

SOURCE_MODE_SWEEP_CENTS = 12        # panic sells are limit orders this far below the reference bid; IOC fills the best bids first, so this only caps how deep it may reach
SOURCE_MODE_BID_MAX_AGE_SECONDS = 3 # a bid older than this isn't trusted as the reference for the first attempt
_source_mode_panic_tries = {}       # ticker -> number of panic attempts so far

SOURCE_MODE_BLIND_SECONDS = 5       # index unreadable this long while holding -> fall back to the market price
SOURCE_MODE_BLIND_MARGIN = 0.03     # ...and sell if the held side's bid-implied win chance is this far below the panic line
_source_mode_blind = {}             # market_ticker -> {"since": epoch, "alerted": bool}
_source_mode_nobid_log = {}         # market_ticker -> last time we logged "no bids"

def _source_mode_check_panic_exit(market_ticker, position, remaining_seconds):
    """Called from check_autosell BEFORE the normal exits. Sells immediately if the held side's win
    chance has dropped below the panic line (SOURCE_MODE_SELL_PROB, or the volatility-scaled line).

    Speed: the first attempt skips the orderbook round trip and reuses the bid check_autosell recorded
    a moment ago, selling with a limit SOURCE_MODE_SWEEP_CENTS below it (price improvement still applies).
    If that doesn't fully fill, retries read the live book, so a stale reference can't repeat.

    Never blind: if the index can't be read for SOURCE_MODE_BLIND_SECONDS (feed down/stale, auth error,
    anything) on a source-mode position or a supported market, the market's own bid stands in for the win
    chance, so a dead data feed can't leave a position unprotected."""
    if not SOURCE_MODE_ENABLED or remaining_seconds < SOURCE_MODE_MIN_SELL_SECONDS_LEFT:
        return False
    r = _source_mode_read_full(market_ticker, position["side"])
    p, vol_ratio = r["p"], r["vol_ratio"]
    sell_line = _source_mode_sell_line(market_ticker, vol_ratio)
    now = time.time()
    ref_bid = None
    blind = False
    if p is None:
        if not (r["feed_error"] or market_ticker in _source_mode_positions):
            return False                       # e.g. a market source mode doesn't cover at all - not our job
        st = _source_mode_blind.setdefault(market_ticker, {"since": now, "alerted": False})
        if now - st["since"] < SOURCE_MODE_BLIND_SECONDS:
            return False
        if not st["alerted"]:
            st["alerted"] = True
            print(f"--> [SOURCE MODE] BLIND on {market_ticker} for {now - st['since']:.0f}s ({r['reason'][:100]}) - "
                  f"protecting the position with the market price instead.")
            push_alert(f"\u26A0\uFE0F Source mode can't read the index for {market_ticker} ({r['reason'][:80]}). "
                       f"Protecting your position with the market price until it's back.")
        known = last_known_bid.get(market_ticker)
        if known and known[0] and known[0] > 0 and (now - known[1]) <= SOURCE_MODE_BID_MAX_AGE_SECONDS:
            ref_bid = known[0]
        else:
            ref_bid = get_position_bid_price(market_ticker, position["side"])
        if ref_bid is None or ref_bid <= 0:
            return False
        p = ref_bid / 100.0
        if p >= sell_line - SOURCE_MODE_BLIND_MARGIN:
            return False
        blind = True
    else:
        _source_mode_blind.pop(market_ticker, None)
        if p >= sell_line:
            return False

    tries = _source_mode_panic_tries.get(market_ticker, 0)
    if ref_bid is None and tries == 0:
        known = last_known_bid.get(market_ticker)
        if known and known[0] and known[0] > 0 and (now - known[1]) <= SOURCE_MODE_BID_MAX_AGE_SECONDS:
            ref_bid = known[0]
    if ref_bid is None:
        ref_bid = get_position_bid_price(market_ticker, position["side"])
    if ref_bid is None or ref_bid <= 0:
        if now - _source_mode_nobid_log.get(market_ticker, 0) > 5:
            _source_mode_nobid_log[market_ticker] = now
            print(f"--> [SOURCE MODE] {market_ticker}: panic condition is met (win chance {p:.1%} < {sell_line:.0%}) "
                  f"but there are NO bids to sell into right now - retrying every cycle.")
        return False
    _source_mode_panic_tries[market_ticker] = tries + 1

    count = position["count"]
    sweep_price = max(1, int(ref_bid) - SOURCE_MODE_SWEEP_CENTS)
    if blind:
        why = f"BLIND - index unavailable, market bid implies {p:.1%}"
    elif SOURCE_MODE_SCALE_ENABLED and vol_ratio is not None:
        why = f"volatility-scaled line, vol {vol_ratio:.1f}x"
    elif sell_line > SOURCE_MODE_SELL_PROB + 1e-9:
        why = f"raised from {SOURCE_MODE_SELL_PROB:.0%} - choppy"
    else:
        why = "normal line"
    print(f"--> [SOURCE MODE] PANIC EXIT: {market_ticker} {position['side'].upper()} win chance fell to "
          f"{p:.1%} (< {sell_line:.0%}, {why}). Selling {count} now (ref bid {ref_bid}\u00a2, "
          f"limit {sweep_price}\u00a2, attempt {tries + 1}), before settlement.")
    filled = execute_sell_order(market_ticker, position["side"], sweep_price, count)
    _apply_fill_to_position(market_ticker, filled, sell_price_cents=ref_bid, reason="Source mode panic exit")

    with positions_lock:
        still_open = market_ticker in open_positions
    if not still_open:
        _source_mode_positions.discard(market_ticker)
        _source_mode_panic_tries.pop(market_ticker, None)
        _source_mode_tight.pop(market_ticker, None)
        _source_mode_scale_hold.pop(market_ticker, None)
        _source_mode_blind.pop(market_ticker, None)
    if filled and filled > 0 and market_ticker not in _source_mode_alerted:
        _source_mode_alerted.add(market_ticker)
        push_alert(f"\U0001F6D1 SOURCE MODE panic-sold {market_ticker} {position['side'].upper()} - "
                   f"win chance {p:.0%} < {sell_line:.0%} ({why}).")
    return True
# --- SOURCE MODE (end) ---

# --- SATELLITE MODE (start) ---
# /satellite [ticker] streams that ticker's source-check reading to the
# console EVERY SECOND until /satellite stop. Telegram gets a start/stop
# confirmation only, plus one update every SATELLITE_TELEGRAM_INTERVAL_SECONDS
# - a message a second would hit Telegram's rate limit almost immediately and
# bury everything else the bot sends.
SATELLITE_TELEGRAM_INTERVAL_SECONDS = 7
SATELLITE_TICK_SECONDS = 1.0
# Only ONE satellite can exist. Each run owns its own stop-Event; /satellite stop sets it and clears the
# state in the same locked step, so (a) a second /satellite is refused while one is running, (b) restarting
# right after a stop can't revive the old run (the old behaviour: a shared "stop" flag got reset before the
# old thread noticed, leaving two streams), and (c) nothing - console or Telegram - is emitted by a stopped
# run: every print/push is gated on the run's own Event.
_satellite_lock = threading.Lock()
_satellite_state = {"active": False, "ticker": None, "event": None}

def _satellite_start(ticker, on_started=None):
    """(True, ticker) if started, or (False, running_ticker) if one is already running."""
    with _satellite_lock:
        if _satellite_state["active"]:
            return False, _satellite_state["ticker"]
        ev = threading.Event()
        _satellite_state.update(active=True, ticker=ticker, event=ev)
    if on_started:
        try:
            on_started()
        except Exception:
            pass
    threading.Thread(target=_satellite_loop, args=(ticker, ev), daemon=True).start()
    return True, ticker

def _satellite_stop():
    """Stops the running satellite. Returns its ticker, or None if none was running."""
    with _satellite_lock:
        if not _satellite_state["active"]:
            return None
        ticker, ev = _satellite_state["ticker"], _satellite_state["event"]
        ev.set()
        _satellite_state.update(active=False, ticker=None, event=None)
    return ticker

def _satellite_loop(ticker, stop_ev):
    last_tg = 0.0
    while not stop_ev.is_set():
        line_parts = [time.strftime('%I:%M:%S %p')]
        for side in ("yes", "no"):
            try:
                r = _source_check_eval(ticker, side)
            except Exception as e:
                line_parts.append(f"{side.upper()}: error ({e})")
                continue
            if "z" in r:
                line_parts.append(f"{side.upper()} {_norm_cdf(r['z']) * 100:.1f}%")
            else:
                line_parts.append(f"{side.upper()}: {r['reason']}")
        with _satellite_lock:
            if stop_ev.is_set():
                return
            print(f"[SATELLITE] {ticker} | " + " | ".join(line_parts))
        if time.time() - last_tg >= SATELLITE_TELEGRAM_INTERVAL_SECONDS:
            with _satellite_lock:
                if stop_ev.is_set():
                    return
            last_tg = time.time()
            push_alert(f"\U0001F6F0\uFE0F SATELLITE {ticker}\n" + "\n".join(line_parts[1:]))
        stop_ev.wait(SATELLITE_TICK_SECONDS)
# --- SATELLITE MODE (end) ---



# --- NEUTRAL MODE (start) ---
# Instead of you choosing a series, the bot ranks every series in
# ALL_SERIES_TICKERS once per 15-minute window and trades whichever scores as
# the most STABLE. "Stable" is a blend of three things, each scaled 0-1 across
# the series that are tradable right now (1 = best):
#   1. LATE REVERSALS - of the recent settled windows that already looked
#      decided with ~3 min left (price >= NEUTRAL_DECIDED_CENTS either way),
#      how often did the leader still lose? Lower is better. (Smoothed so a
#      series with little history doesn't look perfect off one lucky window.)
#   2. SWINGS - average cent move per minute inside recent windows. Lower is better.
#   3. LIQUIDITY - live book right now: tight spread + deep thin-side. Better is better.
# The pick STARTS HARD_ABSOLUTE_MAX_MINUTES + NEUTRAL_PICK_EXTRA_LEAD_MINUTES
# before each window closes (just before the bot is allowed to buy) and is then
# RE-RUN every NEUTRAL_REPICK_SECONDS until the window closes, so each buy check
# trades whichever series scores best against the live books right then. Once a
# position is open in the current window the pick freezes (no second position in
# another series). Open positions in a previous series keep being managed normally.
NEUTRAL_WEIGHT_REVERSALS = 0.40
NEUTRAL_WEIGHT_SWINGS = 0.30
NEUTRAL_WEIGHT_LIQUIDITY = 0.30
NEUTRAL_LOOKBACK_WINDOWS = 8            # settled windows per series used for history
NEUTRAL_MIN_HISTORY_WINDOWS = 3         # fewer than this -> history is "unknown" (scored as middle, flagged)
NEUTRAL_DECIDED_CENTS = 75              # "looked decided" = yes-mid >= 75 or <= 25 at the check point
NEUTRAL_REVERSAL_LOOKAHEAD_MINUTES = 3  # where in the window "looked decided" is judged (minutes before close)
NEUTRAL_REVERSAL_PRIOR = (1.0, 10.0)    # (reversals, windows) pseudo-counts: a series with no evidence reads as 10% reversals
NEUTRAL_PICK_EXTRA_LEAD_MINUTES = 1     # pick this many minutes before the buy window opens
NEUTRAL_MAX_REMAINING_MINUTES = 16      # ignore open markets further out than this (pre-listed future windows)
NEUTRAL_SWITCH_MARGIN = 0.03            # challenger must beat the current series by this much (stops flip-flopping on noise)
NEUTRAL_CHECK_INTERVAL_SECONDS = 5
NEUTRAL_REPICK_SECONDS = 10             # once the pick window opens, re-rank this often until the market closes (so the buy lands on whatever is best RIGHT NOW)
_neutral_last_pick_ts = 0.0
NEUTRAL_SMOOTH_SECONDS = 60             # spread/depth used for ranking = MEDIAN of this many seconds of book readings, so one thin snapshot can't rule a series out
_neutral_book_samples = {}              # market ticker -> deque of (ts, spread, depth, buy_yes_depth, buy_no_depth)
_neutral_samples_lock = threading.Lock()

# --- ABSOLUTE FLOORS ---
# The 0-1 ranking above is RELATIVE (best of whatever is live - a lone series
# always scores 0.50). These floors are ABSOLUTE: a series that fails any of
# them is never picked AND the bot refuses to open new positions in it while
# neutral mode is on, even if it's the only one available. Neutral mode would
# rather sit a window out than trade junk. Checked again at buy time against
# the live book, since the book can change between the pick and the trigger.
# Tune live: /setneutral <reversal|swing|depth|spread> <value>, /neutralfloors on|off
NEUTRAL_FLOORS_ENABLED = True
NEUTRAL_MAX_REVERSAL_RATE = 0.15        # smoothed late-reversal rate (see NEUTRAL_REVERSAL_PRIOR); 2 of 5 decided windows flipping = 20% -> fails
NEUTRAL_MAX_SWING_CENTS = 9.0           # average cents moved per minute inside recent windows
NEUTRAL_MIN_DEPTH_CONTRACTS = 30        # FULL-SIZE depth: at/above this the bot trades its normal size. Thin side of the book - must absorb our size AND an exit.
# --- THIN-BOOK SIZING (instead of skipping thin series outright) ---
# A series whose depth is below the full-size line above but at/above the hard minimum
# below is still tradable - the bot just buys FEWER contracts: at most
# NEUTRAL_DEPTH_SIZE_FRACTION x the depth it can see (e.g. depth 22 -> 13 contracts).
# Below the hard minimum it's skipped as before. Applies to every buy type (standard,
# multi-share, secondary). /neutralsize on|off, /setneutral mindepth <n>, /setneutral sizefrac <pct>
NEUTRAL_REDUCE_SIZE_ENABLED = True
NEUTRAL_REDUCED_MIN_DEPTH_CONTRACTS = 12   # hard minimum when sizing down (depth below this = skip)
NEUTRAL_DEPTH_SIZE_FRACTION = 0.6          # never take more than this share of the visible depth
_neutral_size_caps = {}                    # (market ticker, side) -> (max contracts, epoch seconds) - set by the buy gate, read by execute_order
NEUTRAL_MAX_SPREAD_CENTS = 3            # yes ask + no ask - 100
NEUTRAL_HIST_TTL_SECONDS = 600          # history only changes when a window settles, so cache it between picks

_neutral_window_cache = {}   # settled market ticker -> {"swing","decided","reversed"} (settled windows never change, so fetch once)
_neutral_last_pick_boundary = None
_neutral_force_pick = False
_neutral_last_ranking = {"ts": 0.0, "rows": []}
_neutral_hist_cache = {}        # series -> (epoch seconds, history dict or None)
_neutral_sitting_out = False    # True while no series passes the floors (for the one-time alert on state change)
_neutral_skip_alerted = set()   # market tickers already announced as skipped (one alert per market, not per second)

def _neutral_get_hist(series):
    """History for a series, cached for the current 15-minute period (it only
    changes when a window settles). A FAILED lookup is only cached for 30s so one
    API hiccup can't blank a series for a whole window."""
    period = int(time.time() // 900)
    cached = _neutral_hist_cache.get(series)
    if cached:
        ts, hist, cached_period = cached
        if cached_period == period and (hist is not None or time.time() - ts < 30):
            return hist
    hist = _series_history(series, time.time())
    _neutral_hist_cache[series] = (time.time(), hist, period)
    return hist

def _neutral_depth_floor():
    """Hard minimum depth: the reduced-size minimum when thin-book sizing is on, else the full-size line."""
    if NEUTRAL_REDUCE_SIZE_ENABLED:
        return min(NEUTRAL_REDUCED_MIN_DEPTH_CONTRACTS, NEUTRAL_MIN_DEPTH_CONTRACTS)
    return NEUTRAL_MIN_DEPTH_CONTRACTS

def _neutral_size_cap(depth):
    """Max contracts for a book this deep, or None when it's deep enough for normal size."""
    if not (NEUTRAL_FLOORS_ENABLED and NEUTRAL_REDUCE_SIZE_ENABLED) or depth is None:
        return None
    if depth >= NEUTRAL_MIN_DEPTH_CONTRACTS:
        return None
    return max(1, int(depth * NEUTRAL_DEPTH_SIZE_FRACTION))

def _neutral_cap_for(ticker, side):
    """The cap the buy gate just computed for this exact buy (fresh within 5s), else None."""
    entry = _neutral_size_caps.pop((ticker, side), None)
    if entry and time.time() - entry[1] <= 5:
        return entry[0]
    return None

def _neutral_floor_check(hist, spread, depth):
    """Returns a list of human-readable reasons this series FAILS the absolute
    floors (empty list = passes). hist may be None (not enough history)."""
    if not NEUTRAL_FLOORS_ENABLED:
        return []
    fails = []
    if hist is None:
        fails.append("not enough settled history to verify it")
    else:
        if hist["rev_rate"] > NEUTRAL_MAX_REVERSAL_RATE:
            fails.append(f"late reversals {hist['reversals']}/{hist['decided']} "
                         f"({hist['rev_rate']:.0%} > {NEUTRAL_MAX_REVERSAL_RATE:.0%} max)")
        if hist["swing"] > NEUTRAL_MAX_SWING_CENTS:
            fails.append(f"swing {hist['swing']:.1f}\u00a2/min > {NEUTRAL_MAX_SWING_CENTS:.1f} max")
    if spread is None or spread > NEUTRAL_MAX_SPREAD_CENTS:
        fails.append(f"spread {'n/a' if spread is None else str(spread) + chr(162)} > {NEUTRAL_MAX_SPREAD_CENTS}\u00a2 max")
    depth_floor = _neutral_depth_floor()
    if depth is None or depth < depth_floor:
        fails.append(f"depth {0 if depth is None else int(depth)} < {depth_floor} min")
    return fails

def _neutral_buy_allowed(market_ticker, yes_ask, no_ask, yes_depth, no_depth, side=None):
    """Called from the buy path (every trigger type, including multi-share and
    secondary adds) while neutral mode is on. Blocks the buy if the series or
    its live book fails the absolute floors."""
    series = _series_of(market_ticker)
    hist = _neutral_get_hist(series)
    spread = max(0, yes_ask + no_ask - 100) if (yes_ask > 0 and no_ask > 0) else None
    depth = min(yes_depth, no_depth)
    fails = _neutral_floor_check(hist, spread, depth)
    if not fails:
        if side:
            cap = _neutral_size_cap(depth)
            if cap is None:
                _neutral_size_caps.pop((market_ticker, side), None)
            else:
                _neutral_size_caps[(market_ticker, side)] = (cap, time.time())
        return True
    reason = "; ".join(fails)
    log_smart(("nfloor", market_ticker), f"--> [NEUTRAL FLOOR] Skipping buy on {market_ticker}: {reason}", sig=reason, interval=30)
    if market_ticker not in _neutral_skip_alerted:
        _neutral_skip_alerted.add(market_ticker)
        if len(_neutral_skip_alerted) > 200:
            _neutral_skip_alerted.clear()
        push_alert(f"\U0001F9ED Neutral mode SKIPPED {market_ticker} - not stable enough to trade:\n{reason}")
    return False

def _candle_cents(side):
    """One OHLC side of a Kalshi candlestick -> close price in cents (or None).
    Prefers close_dollars; falls back to close (cents, or dollars if <= 1.0)."""
    if not isinstance(side, dict):
        return None
    try:
        v = side.get("close_dollars")
        if v is not None:
            return float(v) * 100.0
        c = side.get("close")
        if c is None:
            return None
        c = float(c) if not isinstance(c, str) else float(c)
        return c * 100.0 if (isinstance(side.get("close"), str) or c <= 1.0) else c
    except (TypeError, ValueError):
        return None

def _candle_mid_cents(candle):
    bid = _candle_cents(candle.get("yes_bid"))
    ask = _candle_cents(candle.get("yes_ask"))
    if bid is not None and ask is not None and ask > 0:
        return (bid + ask) / 2.0
    return _candle_cents(candle.get("price"))

def _analyze_settled_window(series, market):
    """Swing + 'did the leader hold?' for one settled 15-min window, from 1-minute
    candles. Returns None if the result or candles aren't usable."""
    ticker = market.get("ticker")
    result = (market.get("result") or "").lower()
    if not ticker or result not in ("yes", "no"):
        return None
    if ticker in _neutral_window_cache:
        return _neutral_window_cache[ticker]
    close_str = market.get("close_time") or market.get("expiration_time")
    if not close_str:
        return None
    close_ts = int(datetime.fromisoformat(close_str.replace("Z", "+00:00")).timestamp())
    data = kalshi_request("GET", f"/series/{series}/markets/{ticker}/candlesticks"
                                 f"?start_ts={close_ts - 15 * 60 - 60}&end_ts={close_ts}&period_interval=1")
    pts = []
    for c in (data.get("candlesticks") or []):
        ts = c.get("end_period_ts")
        mid = _candle_mid_cents(c)
        if ts is not None and mid is not None:
            pts.append((int(ts), mid))
    pts.sort()
    if len(pts) < 8:
        return None
    moves = [abs(pts[i][1] - pts[i - 1][1]) for i in range(1, len(pts))]
    swing = sum(moves) / len(moves)
    target = close_ts - NEUTRAL_REVERSAL_LOOKAHEAD_MINUTES * 60
    at = min(pts, key=lambda p: abs(p[0] - target))
    decided = reversed_ = False
    if abs(at[0] - target) <= 90:
        if at[1] >= NEUTRAL_DECIDED_CENTS:
            decided, reversed_ = True, (result != "yes")
        elif at[1] <= 100 - NEUTRAL_DECIDED_CENTS:
            decided, reversed_ = True, (result != "no")
    out = {"swing": swing, "decided": decided, "reversed": reversed_}
    _neutral_window_cache[ticker] = out
    return out

def _series_history(series, now_ts):
    """Recent-window stability stats for one series, or None if there's too little history."""
    try:
        data = kalshi_request("GET", f"/markets?series_ticker={series}&status=settled&limit=60"
                                     f"&min_close_ts={int(now_ts - (NEUTRAL_LOOKBACK_WINDOWS + 3) * 900)}")
    except Exception as e:
        print(f"--> [NEUTRAL] History lookup failed for {series}: {e}")
        return None
    def close_key(m):
        return m.get("close_time") or m.get("expiration_time") or ""
    markets = sorted(data.get("markets", []), key=close_key, reverse=True)[:NEUTRAL_LOOKBACK_WINDOWS]
    swings, decided, reversals = [], 0, 0
    for m in markets:
        try:
            a = _analyze_settled_window(series, m)
        except Exception as e:
            print(f"--> [NEUTRAL] Couldn't analyze {m.get('ticker')}: {e}")
            a = None
        if not a:
            continue
        swings.append(a["swing"])
        if a["decided"]:
            decided += 1
            reversals += 1 if a["reversed"] else 0
    if len(swings) < NEUTRAL_MIN_HISTORY_WINDOWS:
        return None
    prior_rev, prior_n = NEUTRAL_REVERSAL_PRIOR
    return {"swing": sum(swings) / len(swings),
            "rev_rate": (reversals + prior_rev) / (decided + prior_n),
            "decided": decided, "reversals": reversals, "n": len(swings)}

def _median(vals):
    s = sorted(vals)
    n = len(s)
    if n == 0:
        return None
    return s[n // 2] if n % 2 else (s[n // 2 - 1] + s[n // 2]) / 2.0

def _neutral_record_sample(ticker, spread, depth, yes_depth, no_depth):
    now = time.time()
    with _neutral_samples_lock:
        dq = _neutral_book_samples.setdefault(ticker, deque(maxlen=60))
        dq.append((now, spread, depth, yes_depth, no_depth))
        if len(_neutral_book_samples) > 40:  # drop markets that closed a while ago
            for t in [t for t, d in _neutral_book_samples.items() if not d or now - d[-1][0] > 1800]:
                _neutral_book_samples.pop(t, None)

def _neutral_smoothed(ticker):
    """Median spread/depth over the last NEUTRAL_SMOOTH_SECONDS (plus min/max depth for display)."""
    cutoff = time.time() - NEUTRAL_SMOOTH_SECONDS
    with _neutral_samples_lock:
        recent = [s for s in _neutral_book_samples.get(ticker, ()) if s[0] >= cutoff]
    if not recent:
        return None
    depths = [s[2] for s in recent]
    return {"spread": _median([s[1] for s in recent]), "depth": _median(depths),
            "depth_min": min(depths), "depth_max": max(depths), "samples": len(recent)}

def _live_liquidity(series):
    """Live book for the series' current window: spread (cents) and thin-side depth."""
    data = kalshi_request("GET", f"/markets?series_ticker={series}&status=open")
    now = datetime.now(pytz.UTC)
    best = None
    for m in data.get("markets", []):
        cs = m.get("close_time") or m.get("expiration_time")
        if not cs or not m.get("ticker") or _is_recently_exhausted(m["ticker"]):
            continue
        try:
            ct = datetime.fromisoformat(cs.replace("Z", "+00:00"))
        except ValueError:
            continue
        secs = (ct - now).total_seconds()
        if secs <= EARLY_RESOLVE_MIN_SECONDS_LEFT or secs / 60.0 > NEUTRAL_MAX_REMAINING_MINUTES:
            continue
        if best is None or ct < best[1]:
            best = (m["ticker"], ct)
    if not best:
        return None
    snap = _book_snapshot(best[0])
    if snap is None:
        return None
    yes_ask, no_ask, yes_depth, no_depth = snap
    if yes_ask <= EARLY_RESOLVE_ASK_THRESHOLD_CENTS or no_ask <= EARLY_RESOLVE_ASK_THRESHOLD_CENTS:
        return None  # one-sided or already decided - not tradable
    raw_spread = max(0, yes_ask + no_ask - 100)
    raw_depth = min(yes_depth, no_depth)
    _neutral_record_sample(best[0], raw_spread, raw_depth, yes_depth, no_depth)
    sm = _neutral_smoothed(best[0]) or {"spread": raw_spread, "depth": raw_depth, "depth_min": raw_depth,
                                        "depth_max": raw_depth, "samples": 1}
    return {"ticker": best[0], "spread": sm["spread"], "depth": sm["depth"],
            "raw_depth": raw_depth, "buy_yes_depth": yes_depth, "buy_no_depth": no_depth,
            "depth_min": sm["depth_min"], "depth_max": sm["depth_max"], "samples": sm["samples"]}

def _scale01(values, higher_is_better):
    """Min-max scale to 0-1 (1 = best). None -> 0.5; all-equal -> 0.5."""
    known = [v for v in values if v is not None]
    out = []
    lo = min(known) if known else 0
    hi = max(known) if known else 0
    for v in values:
        if v is None or hi == lo:
            out.append(0.5)
        else:
            x = (v - lo) / (hi - lo)
            out.append(x if higher_is_better else 1.0 - x)
    return out

def _rank_series():
    """Scores every series that is tradable right now. Returns rows sorted best-first."""
    now_ts = time.time()
    rows = []
    for series in ALL_SERIES_TICKERS:
        try:
            live = _live_liquidity(series)
        except Exception as e:
            print(f"--> [NEUTRAL] Live lookup failed for {series}: {e}")
            live = None
        if not live:
            continue
        hist = _neutral_get_hist(series)  # cached per 15-min period, so re-ranking every few seconds stays cheap
        rows.append({"series": series, "live": live, "hist": hist,
                     "fails": _neutral_floor_check(hist, live["spread"], live["depth"])})
    if not rows:
        return []
    rev = _scale01([r["hist"]["rev_rate"] if r["hist"] else None for r in rows], higher_is_better=False)
    swg = _scale01([r["hist"]["swing"] if r["hist"] else None for r in rows], higher_is_better=False)
    dep = _scale01([math.log1p(r["live"]["depth"]) for r in rows], higher_is_better=True)
    spr = _scale01([r["live"]["spread"] for r in rows], higher_is_better=False)
    wsum = NEUTRAL_WEIGHT_REVERSALS + NEUTRAL_WEIGHT_SWINGS + NEUTRAL_WEIGHT_LIQUIDITY
    for i, r in enumerate(rows):
        liq = 0.5 * dep[i] + 0.5 * spr[i]
        r["score"] = (NEUTRAL_WEIGHT_REVERSALS * rev[i] + NEUTRAL_WEIGHT_SWINGS * swg[i]
                      + NEUTRAL_WEIGHT_LIQUIDITY * liq) / wsum
    rows.sort(key=lambda r: r["score"], reverse=True)
    _neutral_last_ranking["ts"] = now_ts
    _neutral_last_ranking["rows"] = rows
    return rows

_SERIES_FRIENDLY = {"KXBTC15M": "Bitcoin", "KXETH15M": "Ethereum", "KXSOL15M": "Solana", "KXGOLD15M": "Gold", "KXSILVER15M": "Silver",
                    "KXNATGAS15M": "Natural gas", "KXPLATINUM15M": "Platinum", "KXPALLADIUM15M": "Palladium"}

def _series_name(series):
    return _SERIES_FRIENDLY.get(series, series.replace("KX", "").replace("15M", "").title())

def _format_neutral_ranking(rows):
    """/neutralrank: who passes the safety floors (ranked), who's skipped and why, and what the bot will do."""
    if not rows:
        return ("\U0001F9ED NEUTRAL MODE\nNo market has a live, two-sided book right now "
                "(markets closed, or between windows).")
    ok_rows = [r for r in rows if not r.get("fails")]
    bad_rows = [r for r in rows if r.get("fails")]
    lines = ["\U0001F9ED NEUTRAL MODE - who to trade right now", ""]

    if ok_rows:
        lines.append("\u2705 OK TO TRADE (best first)")
        for i, r in enumerate(ok_rows, 1):
            h, lv = r["hist"], r["live"]
            tag = "   \u25C0 trading now" if r["series"] == ACTIVE_SERIES_TICKER else ""
            lines.append(f"{i}. {_series_name(r['series'])} - {int(round(r['score'] * 100))}/100{tag}")
            if h:
                lines.append(f"   Steadiness: {h['reversals']} of {h['decided']} decided windows flipped late, "
                             f"price moves {h['swing']:.1f}\u00a2/min")
            else:
                lines.append("   Steadiness: not enough settled windows yet (counted as average)")
            book = f"   Book: {lv['spread']:g}\u00a2 spread, about {lv['depth']:g} contracts deep"
            cap = _neutral_size_cap(lv["depth"])
            lines.append(book + (f"  \u26A0 thin - buys capped at ~{cap}" if cap else ""))
        lines.append("")
    if bad_rows:
        lines.append("\u26D4 SKIPPED (won't trade these)")
        for r in bad_rows:
            tag = "  \u25C0 trading now" if r["series"] == ACTIVE_SERIES_TICKER else ""
            lines.append(f"\u2022 {_series_name(r['series'])}{tag}")
            for reason in r["fails"]:
                lines.append(f"    - {reason}")
        lines.append("")

    if ok_rows:
        best = ok_rows[0]["series"]
        if best == ACTIVE_SERIES_TICKER:
            lines.append(f"\u27A1 Result: trading {_series_name(best)} (best right now)")
        else:
            lines.append(f"\u27A1 Result: {_series_name(best)} is best right now - the bot switches to it at its next "
                         f"check (currently on {_series_name(ACTIVE_SERIES_TICKER)})")
    elif NEUTRAL_FLOORS_ENABLED:
        lines.append("\u27A1 Result: nothing passes - sitting this window out (no new buys)")

    if NEUTRAL_FLOORS_ENABLED:
        floor = _neutral_depth_floor()
        depth_txt = (f"depth \u2265 {floor} ({NEUTRAL_MIN_DEPTH_CONTRACTS}+ = full size)"
                     if floor < NEUTRAL_MIN_DEPTH_CONTRACTS else f"depth \u2265 {floor}")
        lines += ["", f"Rules to be tradable: late flips \u2264 {NEUTRAL_MAX_REVERSAL_RATE:.0%} \u00b7 "
                      f"swings \u2264 {NEUTRAL_MAX_SWING_CENTS:g}\u00a2/min \u00b7 {depth_txt} \u00b7 spread \u2264 {NEUTRAL_MAX_SPREAD_CENTS}\u00a2"]
    else:
        lines += ["", "\u26A0 Safety rules are OFF (/neutralfloors on) - it will trade the top score even if it's junk."]
    wsum = NEUTRAL_WEIGHT_REVERSALS + NEUTRAL_WEIGHT_SWINGS + NEUTRAL_WEIGHT_LIQUIDITY
    lines.append(f"Score = {NEUTRAL_WEIGHT_REVERSALS / wsum:.0%} late flips + {NEUTRAL_WEIGHT_SWINGS / wsum:.0%} "
                 f"price moves + {NEUTRAL_WEIGHT_LIQUIDITY / wsum:.0%} book. It only ranks the tradable ones - "
                 f"the \u2705/\u26D4 is the real safety check.")
    return "\n".join(lines)

def _neutral_position_open_in_current_window():
    """True while we hold a position in a market that hasn't closed yet. The pick
    is frozen then, so a re-check can't open a SECOND position in a different
    series inside the same 15-minute window."""
    now_utc = datetime.now(pytz.UTC)
    with positions_lock:
        tickers = list(open_positions.keys())
    for t in tickers:
        ct = _market_close_time_cache.get(t)
        if ct and ct > now_utc:
            return True
    return False

def _neutral_pick_and_apply(reason, force=False):
    """Ranks every series against the LIVE books right now, then points
    ACTIVE_SERIES_TICKER at the winner (with a small stickiness margin so
    near-ties don't flip-flop between re-checks)."""
    global ACTIVE_SERIES_TICKER, _neutral_sitting_out
    if not force and _neutral_position_open_in_current_window():
        return
    all_rows = _rank_series()
    if not all_rows:
        log_smart(("neutral", "none"), f"--> [NEUTRAL] No series has a live two-sided book - keeping {ACTIVE_SERIES_TICKER}.", interval=60)
        return
    rows = [r for r in all_rows if not r.get("fails")]
    if not rows:
        # Nothing is good enough. Don't switch, and the buy gate blocks trading
        # in whatever is active - sit this window out.
        log_smart(("neutral", "out"), "--> [NEUTRAL] Nothing passes the floors - sitting out. " +
                  " | ".join(f"{r['series']}: {'; '.join(r['fails'])}" for r in all_rows), sig="out", interval=60)
        if not _neutral_sitting_out:
            _neutral_sitting_out = True
            push_alert("\U0001F9ED Neutral mode: NOTHING is stable enough right now - sitting out (no new buys) until something passes. "
                       "/neutralrank shows why each series failed.")
        return
    if _neutral_sitting_out:
        _neutral_sitting_out = False
        push_alert("\U0001F9ED Neutral mode: a series passes the floors again - trading resumes.")
    best = rows[0]
    chosen = best
    cur = next((r for r in rows if r["series"] == ACTIVE_SERIES_TICKER), None)
    if cur and best["series"] != cur["series"] and (best["score"] - cur["score"]) < NEUTRAL_SWITCH_MARGIN:
        chosen = cur
    log_smart(("neutral", "rank"),
              f"--> [NEUTRAL] ({reason}) " + " > ".join(f"{r['series']}={r['score']:.2f}" for r in rows) + f" -> {chosen['series']}",
              sig=(chosen["series"], tuple(r["series"] for r in rows)), interval=60)
    if chosen["series"] != ACTIVE_SERIES_TICKER:
        previous = ACTIVE_SERIES_TICKER
        ACTIVE_SERIES_TICKER = chosen["series"]
        _save_config_override("ACTIVE_SERIES_TICKER", ACTIVE_SERIES_TICKER)
        _active_market_cache["ticker"] = None
        _active_market_cache["close_time"] = None
        push_alert(f"\U0001F9ED Neutral mode: {previous} \u2192 {ACTIVE_SERIES_TICKER} (score {chosen['score']:.2f}, "
                   f"{len(rows)} series live). /neutralrank for the full table.")

def _neutral_mode_loop():
    """From the moment the pick window opens (just before buying is allowed)
    until the market closes, re-rank every NEUTRAL_REPICK_SECONDS so the bot is
    always pointed at the best series AT THE TIME OF EACH CHECK - not whichever
    one looked best once, minutes before the buy."""
    global _neutral_force_pick, _neutral_last_pick_ts
    while True:
        try:
            if NEUTRAL_MODE_ENABLED:
                now = time.time()
                boundary = math.ceil(now / 900.0) * 900
                lead = (HARD_ABSOLUTE_MAX_MINUTES + NEUTRAL_PICK_EXTRA_LEAD_MINUTES) * 60
                in_lead = (boundary - now) <= lead
                forced = _neutral_force_pick
                if forced:
                    _neutral_force_pick = False
                if forced or (in_lead and now - _neutral_last_pick_ts >= NEUTRAL_REPICK_SECONDS):
                    _neutral_last_pick_ts = now
                    _neutral_pick_and_apply("manual start" if forced else "recheck", force=forced)
        except Exception as e:
            print(f"--> [ERROR] Neutral mode thread hit an error (continuing): {e}")
        time.sleep(NEUTRAL_CHECK_INTERVAL_SECONDS)
# --- NEUTRAL MODE (end) ---

def _signed_money(amount):
    amount = round(amount, 2)
    if amount == 0:
        return "$0.00"
    return f"{'+' if amount > 0 else '-'}${abs(amount):.2f}"

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

_last_order_error = ""   # why the most recent execute_order() returned None (source mode reads this)

def execute_order(*args, **kwargs):
    """Buy entry point. Marks the ticker busy so position reconcile never races the bot's own recording."""
    t = args[0] if args else kwargs.get("ticker")
    _ticker_busy_begin(t)
    try:
        return _execute_order_impl(*args, **kwargs)
    finally:
        _ticker_busy_end(t)

def _execute_order_impl(ticker, side, price_cents, budget_dollars=None, forced_count=None, is_secondary=False,
                  tif="good_till_canceled"):
    """Executes a V2 order via native authenticated HTTP POST.
    tif="immediate_or_cancel" makes the order fill what it can RIGHT NOW and cancel the rest, so a
    missed fill (price ran away) leaves nothing resting on the book and the ticker is NOT marked traded.
    Every existing caller keeps the default (good_till_canceled), so their behavior is unchanged."""
    global _last_order_error
    _last_order_error = ""
    if price_cents <= 0:
        print("--> [ERROR] Invalid price cents for order execution.")
        _last_order_error = "invalid price"
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
            _last_order_error = "budget"
            return None

    if NEUTRAL_MODE_ENABLED:
        cap = _neutral_cap_for(ticker, side.lower())
        if cap is not None and count > cap:
            print(f"--> [NEUTRAL SIZE] {ticker}: thin book - sizing down {count} -> {cap} contract(s) "
                  f"(max {NEUTRAL_DEPTH_SIZE_FRACTION:.0%} of visible depth)")
            count = cap

    client_order_id = str(uuid.uuid4())
    _mark_pnl_unstable(ORDER_GRACE_SECONDS)

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
        "time_in_force": tif,
        "self_trade_prevention_type": "taker_at_cross"
    }

    order_ts = time.time()
    try:
        response = kalshi_request("POST", endpoint, payload=payload)
        if tif == "immediate_or_cancel":
            # Record first: only a real fill marks the ticker traded / sends the buy alert.
            recorded = _record_entry_from_fills(ticker, side.lower(), price_cents, count, response, order_ts, ioc=True)
            _mark_pnl_unstable(ORDER_GRACE_SECONDS)
            if not recorded:
                print(f"--> [ENTRY] {ticker}: IOC buy (limit {price_cents}\u00a2) got no fill - price moved away. "
                      f"Nothing is resting on the book.")
                return response
            if is_secondary:
                secondary_traded_sides.setdefault(ticker, set()).add(side.lower())
            else:
                traded_tickers.add(ticker)
        else:
            if is_secondary:
                secondary_traded_sides.setdefault(ticker, set()).add(side.lower())
            else:
                traded_tickers.add(ticker)

            _record_entry_from_fills(ticker, side.lower(), price_cents, count, response, order_ts)
            _mark_pnl_unstable(ORDER_GRACE_SECONDS)

        local_time_str = time.strftime('%I:%M:%S %p')
        print(f"[{local_time_str}] SUCCESS! V2 Order placed for {ticker}. ID: {client_order_id}")
        _push_buy_alert(ticker, side.lower(), price_cents, count, is_secondary, forced_count, response)
        return response
    except Exception as e:
        _last_order_error = str(e)
        print(f"--> [ERROR] V2 Order execution failed: {e}")
        return None

# --- REAL FILL PRICES (why P/L used to be off) ---
# Orders are placed as limit orders at the ask the bot SAW. By the time they hit the
# exchange the ask can have moved in our favor, so the order fills at a better price
# than the limit - but the bot used to record the LIMIT price and the REQUESTED count
# as the entry. Every number built on that (unrealized P/L, take-profit trigger,
# settlement P/L) was therefore a little off versus what Kalshi actually charged.
# The same thing happened on sells (recorded at the bid it saw, not what it filled at).
# Now: after every order the bot reads the actual fills from Kalshi and uses the real
# average price, real filled count, and real fees. If the fills can't be read it falls
# back to the old limit-price behavior and says so.
PNL_INCLUDE_FEES = True  # realized P/L (sells + settlements) is net of Kalshi's trading fees, so it matches your balance. Fee info comes from the fills; if Kalshi doesn't report it, fees count as $0.
_last_sell_fill = {}     # ticker -> {"price_cents", "fee"}: real average sell fill, consumed by _apply_fill_to_position

def _num(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None

def _clean_count(x):
    return int(round(x)) if abs(x - round(x)) < 1e-9 else round(x, 2)

def _fill_price_cents(f, side):
    """Price (cents) a fill paid/received on OUR contract side, whichever fields Kalshi sent."""
    other = "no" if side == "yes" else "yes"
    for key, is_dollars in ((f"{side}_price_dollars", True), (f"{side}_price", False)):
        v = _num(f.get(key))
        if v is not None:
            return v * 100.0 if (is_dollars or (isinstance(f.get(key), str) and v <= 1.0)) else v
    for key, is_dollars in ((f"{other}_price_dollars", True), (f"{other}_price", False)):
        v = _num(f.get(key))
        if v is not None:
            return 100.0 - (v * 100.0 if (is_dollars or (isinstance(f.get(key), str) and v <= 1.0)) else v)
    return None

def _fill_fee_dollars(f, count):
    """Fee on one fill in dollars (0 if unreported). Sanity-checked: Kalshi's fee can't
    exceed ~1.75c per contract, so an absurd value is read as cents or ignored."""
    for key in ("fee_cost", "fee_cost_dollars", "fee"):
        v = _num(f.get(key))
        if v is None:
            continue
        if count > 0 and v / count > 0.05:
            v = v / 100.0
            if v / count > 0.05:
                return 0.0
        return max(0.0, v)
    return 0.0

def _extract_order_id(response):
    if not isinstance(response, dict):
        return None
    return response.get("order_id") or (response.get("order") or {}).get("order_id")

def _fetch_order_fills(ticker, side, order_id, since_ts, action, expected_count=None, attempts=4, delay=0.35):
    """Real fills for one order -> {"count", "avg_cents", "fee"} or None.
    Fills can lag the order response by a moment, so it retries briefly until the
    filled count catches up to what the order response reported."""
    path = f"/portfolio/fills?ticker={ticker}&limit=100"
    path += f"&order_id={order_id}" if order_id else f"&min_ts={int(since_ts) - 2}"
    best = None
    for attempt in range(attempts):
        try:
            data = kalshi_request("GET", path)
        except Exception as e:
            if attempt == attempts - 1:
                print(f"--> [WARNING] Couldn't read fills for {ticker}: {e}")
            time.sleep(delay)
            continue
        tot_c = tot_cost = tot_fee = 0.0
        for f in (data.get("fills") or []):
            if order_id and f.get("order_id") and f.get("order_id") != order_id:
                continue
            if f.get("action") and str(f.get("action")).lower() != action:
                continue
            c = _num(f.get("count_fp"))
            if c is None:
                c = _num(f.get("count"))
            px = _fill_price_cents(f, side)
            if not c or c <= 0 or px is None:
                continue
            tot_c += c
            tot_cost += c * px
            tot_fee += _fill_fee_dollars(f, c)
        if tot_c > 0:
            best = {"count": tot_c, "avg_cents": tot_cost / tot_c, "fee": tot_fee}
            if expected_count is None or tot_c >= expected_count - 1e-6:
                return best
        time.sleep(delay)
    return best

def _late_fill_watcher(*args, **kwargs):
    """Runs while a partly-filled entry's remainder is resting; reconcile leaves that ticker to it."""
    t = args[0] if args else kwargs.get("ticker")
    _ticker_busy_begin(t)
    try:
        return _late_fill_watcher_impl(*args, **kwargs)
    finally:
        _ticker_busy_end(t)

def _late_fill_watcher_impl(ticker, side, order_id, order_ts, requested, have_count, have_cost_cents, have_fee):
    """If an entry order only partly filled (the rest is resting), keep watching it
    for ~30s and add whatever fills later, so the position is never under-tracked."""
    for _ in range(20):
        time.sleep(1.5)
        try:
            info = _fetch_order_fills(ticker, side, order_id, order_ts, "buy", attempts=1)
        except Exception:
            continue
        if not info or info["count"] <= have_count + 1e-6:
            continue
        inc_count = info["count"] - have_count
        inc_cost = info["count"] * info["avg_cents"] - have_cost_cents
        inc_px = inc_cost / inc_count if inc_count > 0 else info["avg_cents"]
        record_position(ticker, side, inc_px, _clean_count(inc_count), max(0.0, info["fee"] - have_fee))
        have_count, have_cost_cents, have_fee = info["count"], info["count"] * info["avg_cents"], info["fee"]
        print(f"--> [ENTRY] Late fill on {ticker}: now {have_count:g} of {requested} filled.")
        if have_count >= requested - 1e-6:
            return

def _record_entry_from_fills(ticker, side, limit_cents, requested, response, order_ts, ioc=False):
    """Records the position using what Kalshi actually filled (see block comment above).
    Returns True if a position was recorded. ioc=True: the order can't rest, so "no fills found" means
    "no fill" (never invent a position from the limit price) and there is nothing to watch for later."""
    expected = None
    if isinstance(response, dict):
        expected = _num(response.get("fill_count"))
    order_id = _extract_order_id(response)
    info = None
    if expected is None or expected > 0:
        try:
            info = _fetch_order_fills(ticker, side, order_id, order_ts, "buy", expected, attempts=(2 if ioc else 4))
        except Exception as e:
            print(f"--> [WARNING] Fill lookup failed for {ticker}: {e}")
    if info is None:
        if ioc:
            return False
        if expected is not None and expected <= 0:
            print(f"--> [ENTRY] {ticker}: order accepted but nothing filled yet - watching for fills.")
            threading.Thread(target=_late_fill_watcher, daemon=True,
                             args=(ticker, side, order_id, order_ts, requested, 0.0, 0.0, 0.0)).start()
            return False
        record_position(ticker, side, limit_cents, requested)
        print(f"--> [ENTRY] Couldn't read fills - recorded {requested} @ {limit_cents}\u00a2 (the limit price). "
              f"P/L may be a hair off until this closes.")
        return True
    filled = min(info["count"], requested)
    record_position(ticker, side, info["avg_cents"], _clean_count(filled), info["fee"])
    note = f" (limit {limit_cents}\u00a2)" if abs(info["avg_cents"] - limit_cents) >= 0.05 else ""
    print(f"--> [ENTRY] Filled {filled:g} @ avg {info['avg_cents']:.2f}\u00a2{note}, fees ${info['fee']:.2f}")
    if filled < requested - 1e-6 and not ioc:
        threading.Thread(target=_late_fill_watcher, daemon=True,
                         args=(ticker, side, order_id, order_ts, requested, filled,
                               filled * info["avg_cents"], info["fee"])).start()
    return True

def record_position(ticker, side, price_cents, count, fee_dollars=0.0):
    """tracks my open positions so autosell can check its profits/losses later"""
    with positions_lock:
        existing = open_positions.get(ticker)
        if existing and existing["side"] == side:
            total_cost = existing["entry_price_cents"] * existing["count"] + price_cents * count
            total_count = existing["count"] + count
            existing["entry_price_cents"] = total_cost / total_count
            existing["count"] = total_count
            existing["fees"] = existing.get("fees", 0.0) + fee_dollars
        else:
            open_positions[ticker] = {"side": side, "entry_price_cents": float(price_cents), "count": count,
                                      "fees": fee_dollars}

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

_close_time_retry_at = {}

def _close_time_for_position(market_ticker):
    """Cached close time, fetched on demand (throttled to once per 2s) if it was never cached - a missing
    entry used to silently skip the panic exit for that position."""
    ct = _market_close_time_cache.get(market_ticker)
    if ct:
        return ct
    now = time.time()
    if now < _close_time_retry_at.get(market_ticker, 0.0):
        return None
    _close_time_retry_at[market_ticker] = now + 2.0
    return _get_cached_close_time(market_ticker)

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

def execute_sell_order(*args, **kwargs):
    """Sell entry point. Marks the ticker busy so position reconcile never 'adopts' something just sold."""
    t = args[0] if args else kwargs.get("ticker")
    _ticker_busy_begin(t)
    try:
        return _execute_sell_order_impl(*args, **kwargs)
    finally:
        _ticker_busy_end(t)

def _execute_sell_order_impl(ticker, side, price_cents, count):
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
    _mark_pnl_unstable(ORDER_GRACE_SECONDS)
 
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
 
    sell_ts = time.time()
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

    if fill_count > 0:
        # Real average sell price + fees, so realized P/L reflects what actually filled
        # (not the bid we saw a moment earlier). Falls back to that bid if unreadable.
        try:
            info = _fetch_order_fills(ticker, side.lower(), _extract_order_id(response), sell_ts, "sell", fill_count)
            if info and 1.0 <= info["avg_cents"] <= 99.0:
                _last_sell_fill[ticker] = {"price_cents": round(info["avg_cents"], 2), "fee": info["fee"]}
        except Exception as e:
            print(f"--> [WARNING] Couldn't read sell fill for {ticker} (using the bid price): {e}")

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
        # Kalshi's market object calls this field "result" (yes/no/void, empty
        # until the market is determined). The old code only read
        # "market_result", which doesn't exist - so every settlement came back
        # as "no result yet", the bot waited MAX_SETTLEMENT_WAIT_MINUTES, then
        # gave up WITHOUT recording the trade. Only stop-loss/take-profit sells
        # (recorded at sell time) ever reached /history and /stats.
        result = (market_info.get("result") or market_info.get("market_result") or "").lower() or None
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
    # Round to the cent immediately. Dollar amounts here come from cents-based
    # arithmetic (price_cents * count / 100.0, weighted-average entry prices,
    # etc.), which routinely leaves a tiny float residue like -1.4e-14 on a
    # true $0.00 breakeven trade. Left unrounded, that shows up downstream as
    # a confusing "$-0.00" in /history and quietly nudges the running session
    # total off over many trades. Rounding once here, at the single choke
    # point every trade's P/L passes through, keeps every stat/log clean
    # without having to fix it at each call site separately.
    amount_dollars = round(amount_dollars, 2)
    with session_pnl_lock:
        session_realized_pnl += amount_dollars
        session_realized_pnl = round(session_realized_pnl, 2)
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
        icon = {"Take-profit": "\U0001F4B0", "Stop-loss": "\U0001F6D1"}.get(reason, "\U0001F4B5")
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
    sell_fill = _last_sell_fill.pop(market_ticker, None)
    if not filled_count or filled_count <= 0:
        return
    _mark_pnl_unstable(ORDER_GRACE_SECONDS)
    with positions_lock:
        position = open_positions.get(market_ticker)
        if not position:
            return
        entry_price = position["entry_price_cents"]
        pos_side = position["side"]
        entry_fees_total = position.get("fees", 0.0)
        if filled_count >= position["count"]:
            entry_fee_share = entry_fees_total
            del open_positions[market_ticker]
            remaining = 0
            trailing_stop_peak.pop(market_ticker, None)  # fully closed - clear any trailing-stop peak tracked for it
        else:
            entry_fee_share = entry_fees_total * filled_count / position["count"]
            position["count"] -= filled_count
            position["fees"] = entry_fees_total - entry_fee_share
            remaining = position["count"]

    if sell_price_cents is not None:
        exit_fee = 0.0
        if sell_fill:
            sell_price_cents = sell_fill["price_cents"]  # what it REALLY filled at
            exit_fee = sell_fill["fee"]
        realized = (sell_price_cents - entry_price) * filled_count / 100.0
        if PNL_INCLUDE_FEES:
            realized -= entry_fee_share + exit_fee
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

# --- POSITION RECONCILIATION (the bot's list vs. what Kalshi says you actually hold) ---
# Root cause of "trades read as deposits/withdrawals and aren't monitored": the bot only monitors positions
# it recorded itself. A fill it never recorded (a resting order that filled late, a lookup that failed,
# a restart) is invisible: no panic exit / stop-loss / take-profit, AND the cash it moved looked like an
# outside withdrawal/deposit, which was silently folded into the baselines (hiding the loss).
# Every POSITION_RECONCILE_SECONDS this asks Kalshi for the real positions and:
#   - ADOPTS any open-market position the bot doesn't track (so every exit protection applies to it),
#   - TOPS UP a tracked position if Kalshi shows more contracts than the bot recorded,
#   - flags (but never auto-fixes) a side mismatch,
#   - while any untracked position exists, the deposit/withdrawal detector is switched off.
# Adoption happens on the FIRST sighting (worst case ~1-2s after the fill). Double-counting is prevented by
# tracking which tickers the bot is actively trading right now (see _ticker_busy_*): while the bot itself has
# an order or late-fill watcher running on a ticker - and for a few seconds after - reconcile leaves it alone.
TICKER_BUSY_COOLDOWN_SECONDS = 3.0   # after the bot finishes an order on a ticker, leave it alone this long (lets exchange data catch up)
_busy_lock = threading.Lock()
_busy = {}   # ticker -> [orders running now, safety cap epoch, cooldown-until epoch]

def _ticker_busy_begin(t):
    if not t:
        return
    with _busy_lock:
        e = _busy.setdefault(t, [0, 0.0, 0.0])
        e[0] += 1
        e[1] = time.time() + 60          # a hung order can never block adoption for more than a minute

def _ticker_busy_end(t):
    if not t:
        return
    with _busy_lock:
        e = _busy.setdefault(t, [0, 0.0, 0.0])
        e[0] = max(0, e[0] - 1)
        e[2] = time.time() + TICKER_BUSY_COOLDOWN_SECONDS
        if len(_busy) > 300:
            now = time.time()
            for k in [k for k, v in _busy.items() if v[0] == 0 and now > v[2]]:
                _busy.pop(k, None)

def _ticker_is_busy(t):
    now = time.time()
    with _busy_lock:
        e = _busy.get(t)
        return bool(e and ((e[0] > 0 and now < e[1]) or now < e[2]))

POSITION_RECONCILE_SECONDS = 1.0   # one cheap read per second
_reconcile_seen = {}          # (kind, ticker) -> first time seen out of sync
_untracked_positions = {}     # ticker -> info; non-empty = equity moves are NOT classified as outside deposits/withdrawals
_reconcile_state = {"logged_shape": False, "fail_logged": False}

def _fetch_exchange_positions():
    """{ticker: {"side","count","avg_cents","fees"}} for every unsettled position Kalshi says we hold, or None on error."""
    resp, err = None, None
    for q in ("?limit=200&settlement_status=unsettled&count_filter=position", "?limit=200"):
        try:
            resp = kalshi_request("GET", "/portfolio/positions" + q)
            break
        except Exception as e:
            err = e
    if resp is None:
        if not _reconcile_state["fail_logged"]:
            _reconcile_state["fail_logged"] = True
            print(f"--> [WARNING] Position reconcile can't read /portfolio/positions: {err}")
        return None
    _reconcile_state["fail_logged"] = False
    rows = resp.get("market_positions") or []
    if not _reconcile_state["logged_shape"]:
        _reconcile_state["logged_shape"] = True
        print(f"--> [RECONCILE] Position sync active ({len(rows)} open position(s) on the exchange). "
              f"Sample row keys: {sorted(rows[0].keys()) if rows else 'n/a'}")
    out = {}
    for r in rows:
        t = r.get("ticker")
        pos = _num(r.get("position_fp") if r.get("position_fp") is not None else r.get("position"))
        if not t or not pos or abs(pos) < 1e-9:
            continue
        side, count = ("yes" if pos > 0 else "no"), abs(pos)
        cost_c = None
        if _num(r.get("market_exposure_dollars")) is not None:
            cost_c = _num(r.get("market_exposure_dollars")) * 100.0
        elif _num(r.get("market_exposure")) is not None:
            cost_c = _num(r.get("market_exposure"))
        fees = 0.0
        if _num(r.get("fees_paid_dollars")) is not None:
            fees = _num(r.get("fees_paid_dollars"))
        elif _num(r.get("fees_paid")) is not None:
            fees = _num(r.get("fees_paid")) / 100.0
        out[t] = {"side": side, "count": count, "cost_cents": cost_c, "fees": fees,
                  "avg_cents": (cost_c / count) if (cost_c and count) else None}
    return out

def _reconcile_positions_once():
    """Returns False if Kalshi couldn't be read (caller backs off briefly), else True."""
    ex = _fetch_exchange_positions()
    if ex is None:
        return False
    now, now_utc = time.time(), datetime.now(pytz.UTC)
    with positions_lock:
        tracked = {t: dict(p) for t, p in open_positions.items()}
    for k in [k for k in _reconcile_seen if k[1] not in ex]:
        _reconcile_seen.pop(k, None)
    _untracked_positions.clear()
    for t, e in ex.items():
        mine = tracked.get(t)
        if mine is None:
            _untracked_positions[t] = e
            ct = _get_cached_close_time(t)
            if ct is not None and now_utc >= ct:
                continue                                      # market already closed: nothing to sell; settlement will pay it
            if _ticker_is_busy(t):
                continue                                      # the bot is mid-order on this ticker - it will record it itself
            avg = e["avg_cents"]
            if avg is None:
                avg = get_position_bid_price(t, e["side"]) or 50.0
            record_position(t, e["side"], avg, _clean_count(e["count"]), e["fees"])
            traded_tickers.add(t)
            _untracked_positions.pop(t, None)
            _reconcile_seen.pop(("new", t), None)
            print(f"--> [RECONCILE] ADOPTED untracked position: {t} {e['side'].upper()} x{e['count']:g} @ ~{avg:.1f}\u00a2 - now monitored.")
            push_alert(f"\u26A0\uFE0F Found a position the bot wasn't tracking: {t} {e['side'].upper()} x{e['count']:g} "
                       f"(~{avg:.0f}\u00a2). It's now monitored like any other trade (panic exit / stop-loss / take-profit).")
        elif mine["side"] != e["side"]:
            if ("side", t) not in _reconcile_seen:
                _reconcile_seen[("side", t)] = now
                print(f"--> [RECONCILE] WARNING: {t} - bot tracks {mine['side'].upper()} but Kalshi shows {e['side'].upper()}.")
                push_alert(f"\u26A0\uFE0F Position mismatch on {t}: bot tracks {mine['side'].upper()}, Kalshi shows "
                           f"{e['side'].upper()} x{e['count']:g}. Check it manually.")
        elif e["count"] > mine["count"] + 0.5:
            if _ticker_is_busy(t):
                continue
            extra = e["count"] - mine["count"]
            price = mine["entry_price_cents"]
            if e["cost_cents"] is not None:
                implied = (e["cost_cents"] - mine["entry_price_cents"] * mine["count"]) / extra
                if 1 <= implied <= 99:
                    price = implied
            record_position(t, e["side"], price, _clean_count(extra), 0.0)
            _reconcile_seen.pop(("top", t), None)
            print(f"--> [RECONCILE] Topped up {t} {e['side'].upper()} by {extra:g} contract(s) Kalshi shows that the bot hadn't recorded.")
            push_alert(f"\u26A0\uFE0F {t}: Kalshi shows {extra:g} more contract(s) than the bot had recorded - now tracking all {e['count']:g}.")
    return True

def _position_reconcile_loop():
    while True:
        time.sleep(POSITION_RECONCILE_SECONDS)
        try:
            if _reconcile_positions_once() is False:
                time.sleep(2.0)       # couldn't read Kalshi (error / rate limit): back off a moment
        except Exception as e:
            print(f"--> [WARNING] Position reconcile error (continuing): {e}")

# --- EXTERNAL BALANCE MOVES (manual withdrawals / deposits) ---
# A withdrawal from the account drops cash with no trade behind it, which used
# to read as a session LOSS (and could trip the daily loss limit). Between two
# clean readings, if nothing the bot tracks changed (same open positions, same
# cost basis, same realized P/L, same sweep total) yet total equity moved, the
# move came from outside the bot. It is folded into the baselines so it never
# counts as profit or loss.
EXTERNAL_FLOW_MIN_DOLLARS = 0.50      # smaller moves are treated as ordinary rounding/fees
EXTERNAL_FLOW_STABLE_SECONDS = 60     # tracked state must have sat unchanged this long (lets late payouts land first)
_external_flow_lock = threading.Lock()
_external_flow_state = {"equity": None, "sig": None, "sig_since": 0.0}
external_flow_total_dollars = 0.0     # net outside deposits (+) / withdrawals (-) this run

def _reconcile_external_flow(current_balance, open_basis):
    global session_start_balance, external_flow_total_dollars
    global _hourly_checkpoint_pnl, _daily_checkpoint_pnl
    with positions_lock:
        keys = tuple(sorted(open_positions.keys()))
    with session_pnl_lock:
        realized = round(session_realized_pnl, 2)
    sig = (keys, round(open_basis, 2), realized, round(swept_total_dollars, 2))
    equity = current_balance + open_basis
    now = time.time()
    delta = 0.0
    with _external_flow_lock:
        st = _external_flow_state
        if _sweep_state["unconfirmed"] or _pnl_in_flight() or _untracked_positions:
            # (_untracked_positions: Kalshi shows a position the bot isn't tracking yet - that cash move is a TRADE, not an outside deposit/withdrawal)
            st["equity"] = None
            st["sig"] = None
            return 0.0
        if st["equity"] is None or st["sig"] != sig:
            st.update(equity=equity, sig=sig, sig_since=now)
            return 0.0
        move = equity - st["equity"]
        if abs(move) < EXTERNAL_FLOW_MIN_DOLLARS:
            st["equity"] = equity
            return 0.0
        if now - st["sig_since"] < EXTERNAL_FLOW_STABLE_SECONDS:
            return 0.0
        delta = round(move, 2)
        st["equity"] = equity
        external_flow_total_dollars = round(external_flow_total_dollars + delta, 2)
        if session_start_balance is not None:
            session_start_balance += delta
        if _hourly_checkpoint_pnl is not None:
            _hourly_checkpoint_pnl += delta
        if _daily_checkpoint_pnl is not None:
            _daily_checkpoint_pnl += delta
    kind = "deposit" if delta > 0 else "withdrawal"
    print(f"--> [BALANCE] Detected an outside {kind} of ${abs(delta):.2f} - not counted as profit or loss.")
    push_alert(f"\U0001F4B5 Detected a ${abs(delta):.2f} {kind} on your account (not a trade). "
               f"It is NOT counted as profit or loss and won't affect the daily loss limit.")
    return delta
# --------------------------------------------------------------

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
    if _pnl_in_flight():
        return None  # money is mid-transit (order or payout) - any number here could be a fake loss/gain
    current = get_kalshi_account_balance()
    if current is None:
        return None
    with positions_lock:
        open_cost_basis = sum(pos["entry_price_cents"] / 100.0 * pos["count"] for pos in open_positions.values())
    if _pnl_in_flight():
        return None  # something changed while we were reading the balance
    _reconcile_external_flow(current, open_cost_basis)
    return (current - session_start_balance) + open_cost_basis + swept_total_dollars

def check_autosell(market_ticker):
    """this oversees exits for an open position:
    - Takes profit once unrealized P/L reaches PROFIT_TARGET_DOLLARS (if AUTOSELLING).
    - Cuts losses once unrealized P/L drops to -STOP_LOSS_DOLLARS (if STOP_LOSS_ENABLED),
      but late in the market's life requires the loss to persist across several
      consecutive checks first, to filter out a single whale-driven price spike
      that reverts rather than a genuine reversal.
    + they both share the same bid lookup so this only costs one extra call per check."""
    # /autosell is the MASTER switch: if it's off, nothing takes profit early - including source-mode
    # positions. SOURCE_MODE_AUTOSELL can only turn take-profit off for source-mode positions, never
    # back on over the master (it used to override it, which is why autosell "turned itself back on").
    position_autosell = AUTOSELLING
    if market_ticker in _source_mode_positions:
        position_autosell = AUTOSELLING and SOURCE_MODE_AUTOSELL

    if not position_autosell and not STOP_LOSS_ENABLED and not PRICE_DROP_EXIT_ENABLED and not SOURCE_MODE_ENABLED:
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
    cached_close_time = _close_time_for_position(market_ticker)
    now_utc = datetime.now(pytz.UTC)
    if SOURCE_MODE_ENABLED and cached_close_time:
        remaining_seconds = (cached_close_time - now_utc).total_seconds()
        if _source_mode_check_panic_exit(market_ticker, position, remaining_seconds):
            return
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
            _mark_pnl_unstable(PAYOUT_GRACE_SECONDS)
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
                if PNL_INCLUDE_FEES:
                    realized -= closed_position.get("fees", 0.0)
                total = _record_realized_pnl(realized, "Settled (held to expiration)", market_ticker)
                settle_label = "\u2705 SETTLED WIN" if result == closed_position["side"] else "\u274C SETTLED LOSS"
                push_alert(
                    f"{settle_label}: {closed_position['side'].upper()} "
                    f"x{closed_position['count']} (in @ {closed_position['entry_price_cents']:.1f}\u00a2)\n"
                    f"{market_ticker}\n"
                    f"P/L: {_signed_money(realized)} | Session (tracked): {_signed_money(total)}"
                )
            return

        elif result == "void":
            _mark_pnl_unstable(PAYOUT_GRACE_SECONDS)
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
                log_smart(("pend", market_ticker), sig=0, interval=30, msg=f"--> [POSITION MGMT] {market_ticker} closed but settlement result not posted yet "
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

    # Clamp to the same 1-99c range execute_sell_order enforces, and do it
    # HERE - not just inside execute_sell_order. Kalshi's orderbook can
    # legitimately return a literal 100c top-of-book entry once a market is
    # right on the edge of settling (a real orderbook value, not bad parsing),
    # but 100c isn't a tradable price - execute_sell_order was already
    # silently clamping it to 99 before submitting, while profit_dollars here
    # kept using the raw unclamped 100. That mismatch is exactly why the
    # TAKE-PROFIT alert can say "$0.30" when the fill that actually goes out
    # can only ever happen at 99c, which is a different, lower real profit.
    # Clamping before profit_dollars is computed makes what's displayed/
    # alerted/compared against your thresholds match what will actually be
    # submitted - no more daylight between the two.
    if current_bid is not None and current_bid > 0:
        current_bid = max(1, min(99, current_bid))

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
    log_smart(("pos", market_ticker),
              f"[{local_time_str}] [POSITION] {market_ticker} {position['side'].upper()} x{count} | "
              f"in {entry_price:.1f}\u00a2 | bid {current_bid}\u00a2 | P/L {_signed_money(profit_dollars)}",
              sig=(current_bid, count), interval=10.0, min_gap=1.0)

    with positions_lock:
        is_held = market_ticker in held_positions
    if is_held:
        log_smart(("held", market_ticker), f"--> [HELD] {market_ticker} is on /hold - auto exits skipped (/unhold to resume).",
                  sig=0, interval=120)
        return

    if PRICE_DROP_EXIT_ENABLED:
        # A tight, size-independent tripwire: sells the instant the price
        # itself has fallen PRICE_DROP_EXIT_CENTS below entry, regardless of
        # dollar P/L or contract count - e.g. bought at 98c, drops to 96c with
        # a 2c setting, sells immediately. This is deliberately separate from
        # (and faster than) STOP_LOSS_DOLLARS/STOP_LOSS_CONFIRMATION_SECONDS:
        # no confirmation delay, no dollar threshold - just raw cents moved
        # against you. Checked before trailing-stop/take-profit/stop-loss so
        # it can act first if it's the one that trips.
        price_drop_cents = entry_price - current_bid
        if price_drop_cents >= PRICE_DROP_EXIT_CENTS:
            local_time_str = time.strftime('%I:%M:%S %p')
            print(f"[{local_time_str}] PRICE-DROP EXIT TRIGGERED! {market_ticker} bid fell to {current_bid}\u00a2 "
                  f"from entry {entry_price:.1f}\u00a2 (-{price_drop_cents:.1f}\u00a2, >= {PRICE_DROP_EXIT_CENTS}\u00a2 trip). "
                  f"Selling {count} contract(s) immediately...")
            filled = execute_sell_order(market_ticker, position["side"], current_bid, count)
            _apply_fill_to_position(market_ticker, filled, sell_price_cents=current_bid, reason="Price-drop exit")
            stop_loss_breach_started.pop(market_ticker, None)
            trailing_stop_peak.pop(market_ticker, None)
            return

    if position_autosell and TAKE_PROFIT_BID_CENTS > 0 and current_bid >= TAKE_PROFIT_BID_CENTS and profit_dollars >= 0:
        # Cents-based take-profit (see TAKE_PROFIT_BID_CENTS). Checked before the
        # dollar/trailing exits because at ~98-99c entries those can't reach their target.
        stop_loss_breach_started.pop(market_ticker, None)
        print(f"--> TAKE-PROFIT (BID) TRIGGERED! Bid {current_bid}\u00a2 >= {TAKE_PROFIT_BID_CENTS}\u00a2 trigger "
              f"(entry {entry_price:.1f}\u00a2, P/L ${profit_dollars:.2f}). Selling {count} contract(s) to lock it in...")
        filled = execute_sell_order(market_ticker, position["side"], current_bid, count)
        _apply_fill_to_position(market_ticker, filled, sell_price_cents=current_bid, reason="Take-profit (bid)")
        trailing_stop_peak.pop(market_ticker, None)
        return

    if position_autosell and TRAILING_STOP_ENABLED and count > TRAILING_STOP_MIN_CONTRACTS:
        # Large position - trail instead of using the flat PROFIT_TARGET_DOLLARS
        # exit below. Once profit reaches the arm level, track the best profit
        # seen (trailing_stop_peak) and sell only if it falls back by the trail
        # amount, so a strong move isn't cut short right at the old fixed target.
        if market_ticker in trailing_stop_peak or profit_dollars >= TRAILING_STOP_ARM_DOLLARS:
            # Once armed (already has a tracked peak), keep evaluating the
            # trigger even if profit dips back below the arm level - the arm
            # level should only gate the FIRST arming, not every tick after.
            # Without this, a sharp drop straight from peak to below both the
            # arm level AND the trigger level in one tick would skip the sell
            # entirely, since the old code's outer gate excluded it.
            #
            # IMPORTANT: use None as the "not armed yet" sentinel, NOT
            # profit_dollars. Defaulting to profit_dollars made peak always
            # equal the current tick's own profit on first arming (since
            # nothing had been stored yet), which made "profit_dollars > peak"
            # structurally false forever and left the dict permanently empty -
            # trigger_level always collapsed to profit_dollars - TRAIL_DOLLARS,
            # making the sell condition mathematically unreachable. This was a
            # real bug: large positions never actually trailing-stopped out.
            peak = trailing_stop_peak.get(market_ticker)
            if peak is None or profit_dollars > peak:
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
            log_smart(("tsw", market_ticker),
                      f"--> [TRAILING STOP WATCH] {market_ticker} profit ${profit_dollars:.2f}, peak ${peak:.2f}, "
                      f"sells if it drops to ${trigger_level:.2f}.",
                      sig=(round(peak, 2), round(trigger_level, 2)), interval=15)
        # Not armed yet (profit hasn't reached TRAILING_STOP_ARM_DOLLARS) - a
        # large position just holds here rather than taking the small fixed
        # target below, which is the whole point of trailing for big size.
    elif position_autosell and profit_dollars >= PROFIT_TARGET_DOLLARS:
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
                log_smart(("slw", market_ticker), sig=0, interval=2.0, msg=f"--> [STOP-LOSS WATCH] {market_ticker} loss ${profit_dollars:.2f} past -${STOP_LOSS_DOLLARS:.2f} "
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
    if not AUTOSELLING and not STOP_LOSS_ENABLED and not PRICE_DROP_EXIT_ENABLED and not SOURCE_MODE_ENABLED:
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
    if fresh is None and _pnl_in_flight():
        # Don't leave the loss limit blind while a payout settles - use the
        # bot's own realized tally (exact at sell/settle time) for this check.
        with session_pnl_lock:
            fresh = session_realized_pnl
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
            log_smart(("lossLimit",), sig=0, interval=60, msg=f"[{local_time_str}] [DAILY LOSS LIMIT] Session P/L ${current_pnl:.2f} has hit the "
                  f"-${DAILY_LOSS_LIMIT_DOLLARS:.2f} limit. No new positions will be opened. "
                  f"(Already-open positions still get managed normally. Send /unlockloss via Telegram to override.)")
            return
        elif current_pnl is None:
            local_time_str = time.strftime('%I:%M:%S %p')
            log_smart(("lossLimitWarn",), sig=0, interval=60, msg=f"[{local_time_str}] [WARNING] Could not verify balance for daily loss limit check this cycle - "
                  f"proceeding without blocking (transient API issue assumed).")
        else:
            _loss_limit_alerted = False  # back inside the limit - re-arm the alert for the next trip

    if trading_paused:
        local_time_str = time.strftime('%I:%M:%S %p')
        log_smart(("paused",), sig=0, interval=60, msg=f"[{local_time_str}] [PAUSED] Trading paused via Telegram /pause. "
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
                log_smart(("wait", market_ticker), f"[{local_time_str}] {market_ticker}: waiting for the buy window (opens at {HARD_ABSOLUTE_MAX_MINUTES}m left)",
                          sig=0, interval=3600)
                return
            
            if remaining_minutes < 0.3:
                local_time_str = time.strftime('%I:%M:%S %p')
                log_smart(("exp", market_ticker), f"[{local_time_str}] {market_ticker}: expiring imminently ({remaining_minutes:.1f}m left) - no new buys.",
                          sig=0, interval=3600)
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

        # EARLY-RESOLVE SKIP-AHEAD: by this point remaining_minutes is already
        # guaranteed <= HARD_ABSOLUTE_MAX_MINUTES (the check above returns
        # before we get here otherwise) - so only now do we care whether this
        # ticker has already resolved. An ask pinned at/near 0 on either side
        # means that side's bid book emptied out because everyone already
        # knows how this settles (this is also exactly the "0\u00a2" artifact -
        # see get_top_bid_cents_and_size's fallback). If we're not holding a
        # position here, there's no more edge left on this specific ticker -
        # signal the main loop to drop it and try the next open window
        # instead of polling a dead one until its official close_time.
        # NOTE: this used to return "EXHAUSTED" immediately right here. That
        # was a real bug: Kalshi only trades in whole cents, so a trigger
        # threshold like 98.2\u00a2 can only ever be satisfied by an actual price
        # of 99\u00a2 - but 99\u00a2 on one side means the other side is at 1\u00a2, which
        # is exactly this early-resolve cutoff. Returning immediately here
        # meant the "this ticker is decided, abandon it" check always won the
        # race against a legitimate buy trigger sitting at 98-99\u00a2, since this
        # check ran before the trigger logic below ever got a chance to fire.
        # Fix: just flag the candidate and keep going - the buy triggers below
        # get first right of refusal. Only if NOTHING fires do we actually
        # abandon the ticker (see the "Conditions not met" fallthrough below).
        if SOURCE_MODE_ENABLED:
            if _source_mode_scan(market_ticker, remaining_minutes, yes_ask, no_ask):
                return
            # Inside source mode, normal price triggers never fire - only the
            # probability-based buy above does. Fall through to early-resolve
            # bookkeeping so a dead ticker still gets handed off correctly.

        early_resolve_candidate = (
            (yes_ask <= EARLY_RESOLVE_ASK_THRESHOLD_CENTS or no_ask <= EARLY_RESOLVE_ASK_THRESHOLD_CENTS)
            and remaining_minutes > (EARLY_RESOLVE_MIN_SECONDS_LEFT / 60.0)
        )
        if early_resolve_candidate:
            with positions_lock:
                early_resolve_candidate = market_ticker not in open_positions

        # Thin series (platinum, palladium) are exempt - the depth/volume
        # floors were tuned against BTC/gold liquidity and would skip almost
        # every trigger on a market this quiet, which defeats the point of
        # trading it at all.
        liquidity_filter_active = LIQUIDITY_FILTER_ENABLED and _series_of(market_ticker) not in LIQUIDITY_FILTER_EXEMPT_SERIES

        # Market-wide volume floor - skips the WHOLE market this cycle if it's
        # too illiquid to trust the quoted price at all, independent of what's
        # sitting at the top of book right now. Fails open (doesn't block) if
        # the volume fetch itself fails, so a transient API hiccup here can't
        # freeze trading the way an expiration-check failure does.
        if liquidity_filter_active:
            market_volume = get_market_volume(market_ticker)
            if market_volume is not None and market_volume < MIN_MARKET_VOLUME_CONTRACTS:
                local_time_str = time.strftime('%I:%M:%S %p')
                log_smart(("volfilter", market_ticker), sig=0, interval=30, msg=f"[{local_time_str}] [LIQUIDITY FILTER] Skipping {market_ticker} - volume "
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
            if SOURCE_MODE_ENABLED:
                return False  # source mode buys through _source_mode_scan() above, not the normal triggers
            if SOURCE_CHECK_ENABLED and not _source_check_allows(market_ticker, "yes"):
                return False
            if NEUTRAL_MODE_ENABLED and not _neutral_buy_allowed(market_ticker, yes_ask, no_ask, yes_ask_depth, no_ask_depth, side="yes"):
                return False
            if VELOCITY_FILTER_ENABLED and yes_jump > MAX_PRICE_JUMP_CENTS:
                log_smart(("velY", market_ticker), sig=0, interval=10, msg=f"--> [VELOCITY FILTER] Skipping YES buy - price jumped {yes_jump}\u00a2 since last "
                      f"check (> {MAX_PRICE_JUMP_CENTS}\u00a2 cap). Looks like a violent swing, not a stable trend.")
                return False
            if liquidity_filter_active and yes_ask_depth < MIN_BOOK_DEPTH_CONTRACTS:
                log_smart(("liqY", market_ticker), sig=0, interval=10, msg=f"--> [LIQUIDITY FILTER] Skipping YES buy - only {yes_ask_depth} contract(s) at "
                      f"the top of book (< {MIN_BOOK_DEPTH_CONTRACTS} required). Book looks thin.")
                return False
            return True

        def no_side_stable():
            if SOURCE_MODE_ENABLED:
                return False
            if SOURCE_CHECK_ENABLED and not _source_check_allows(market_ticker, "no"):
                return False
            if NEUTRAL_MODE_ENABLED and not _neutral_buy_allowed(market_ticker, yes_ask, no_ask, yes_ask_depth, no_ask_depth, side="no"):
                return False
            if VELOCITY_FILTER_ENABLED and no_jump > MAX_PRICE_JUMP_CENTS:
                log_smart(("velN", market_ticker), sig=0, interval=10, msg=f"--> [VELOCITY FILTER] Skipping NO buy - price jumped {no_jump}\u00a2 since last "
                      f"check (> {MAX_PRICE_JUMP_CENTS}\u00a2 cap). Looks like a violent swing, not a stable trend.")
                return False
            if liquidity_filter_active and no_ask_depth < MIN_BOOK_DEPTH_CONTRACTS:
                log_smart(("liqN", market_ticker), sig=0, interval=10, msg=f"--> [LIQUIDITY FILTER] Skipping NO buy - only {no_ask_depth} contract(s) at "
                      f"the top of book (< {MIN_BOOK_DEPTH_CONTRACTS} required). Book looks thin.")
                return False
            return True

        local_time_str = time.strftime('%I:%M:%S %p')
        log_smart(("mkt", market_ticker),
                  f"[{local_time_str}] {market_ticker} | {remaining_minutes:.1f}m left | YES {yes_ask}\u00a2 | NO {no_ask}\u00a2",
                  sig=(yes_ask, no_ask), interval=10, min_gap=2)
        
        # 3. Check if already traded (with secondary exception override)
        if market_ticker in traded_tickers:
            sides_used_secondary = secondary_traded_sides.get(market_ticker, set())
            if remaining_minutes < SECONDARY_TIME_LIMIT:
                if yes_ask > SECONDARY_PRICE_CENTS and "yes" not in sides_used_secondary:
                    log_smart(("trig", market_ticker, "s-yes"), sig=0, interval=15, msg=f"--> SECONDARY TRIGGER HIT! [< {SECONDARY_TIME_LIMIT}m & YES Ask {yes_ask}¢ > {SECONDARY_PRICE_CENTS}¢]. Buying 2 more shares...")
                    if yes_side_stable() and mood_allows_buy(market_ticker, "yes"):
                        execute_order(market_ticker, side="yes", price_cents=yes_ask, forced_count=5, is_secondary=True)
                    return
                elif no_ask > SECONDARY_PRICE_CENTS and "no" not in sides_used_secondary:
                    log_smart(("trig", market_ticker, "s-no"), sig=0, interval=15, msg=f"--> SECONDARY TRIGGER HIT! [< {SECONDARY_TIME_LIMIT}m & NO Ask {no_ask}¢ > {SECONDARY_PRICE_CENTS}¢]. Buying 2 more shares...")
                    if no_side_stable() and mood_allows_buy(market_ticker, "no"):
                        execute_order(market_ticker, side="no", price_cents=no_ask, forced_count=5, is_secondary=True)
                    return
            
            log_smart(("traded", market_ticker), f"[{local_time_str}] Already traded {market_ticker}. Standing by...", sig=0, interval=3600)
            return

        # 4. Standard Triggers for Fresh Markets
        is_early_zone = remaining_minutes > STANDARD_MAX_MINUTES
        required_threshold = EARLY_SPIKE_PRICE_CENTS if is_early_zone else NORMAL_TRIGGER_PRICE_CENTS
        zone_label = f"EARLY SPIKE EXCEPTION (Time > {STANDARD_MAX_MINUTES}m)" if is_early_zone else "STANDARD WINDOW"
        
        if yes_ask >= MULTI_SHARE_THRESHOLD:
            log_smart(("trig", market_ticker, "m-yes"), sig=0, interval=15, msg=f"--> TRIGGER HIT! [MULTI-SHARE] YES Ask {yes_ask}¢ >= {MULTI_SHARE_THRESHOLD}¢. Buying {MULTI_SHARE_CONTRACT_COUNT} contracts...")
            if yes_side_stable() and mood_allows_buy(market_ticker, "yes"):
                execute_order(market_ticker, side="yes", price_cents=yes_ask, forced_count=MULTI_SHARE_CONTRACT_COUNT)
        elif no_ask >= MULTI_SHARE_THRESHOLD:
            log_smart(("trig", market_ticker, "m-no"), sig=0, interval=15, msg=f"--> TRIGGER HIT! [MULTI-SHARE] NO Ask {no_ask}¢ >= {MULTI_SHARE_THRESHOLD}¢. Buying {MULTI_SHARE_CONTRACT_COUNT} contracts...")
            if no_side_stable() and mood_allows_buy(market_ticker, "no"):
                execute_order(market_ticker, side="no", price_cents=no_ask, forced_count=MULTI_SHARE_CONTRACT_COUNT)
        elif yes_ask >= required_threshold:
            log_smart(("trig", market_ticker, "st-yes"), sig=0, interval=15, msg=f"--> TRIGGER HIT! [{zone_label}] YES Ask {yes_ask}¢ >= {required_threshold}¢ target. Executing standard buy...")
            if yes_side_stable() and mood_allows_buy(market_ticker, "yes"):
                execute_order(market_ticker, side="yes", price_cents=yes_ask)
        elif no_ask >= required_threshold:
            log_smart(("trig", market_ticker, "st-no"), sig=0, interval=15, msg=f"--> TRIGGER HIT! [{zone_label}] NO Ask {no_ask}¢ >= {required_threshold}¢ target. Executing standard buy...")
            if no_side_stable() and mood_allows_buy(market_ticker, "no"):
                execute_order(market_ticker, side="no", price_cents=no_ask)
        elif early_resolve_candidate:
            # Got all the way through every buy trigger and nothing fired -
            # NOW it's genuinely safe to call this ticker decided and move on,
            # since a real trigger had its chance first and didn't match.
            local_time_str = time.strftime('%I:%M:%S %p')
            print(f"[{local_time_str}] [EARLY RESOLVE] {market_ticker} looks already decided "
                  f"(YES ask {yes_ask}\u00a2 / NO ask {no_ask}\u00a2) with {remaining_minutes:.1f}m still "
                  f"left, no position held, and no trigger fired - nothing left to trade here. "
                  f"Moving to the next open ticker.")
            return "EXHAUSTED"
        else:
            pass  # the market line above already shows the prices - no need to repeat "standing by" every cycle

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

def get_account_equity():
    """Cash balance PLUS the cost of open positions - money sitting in a
    contract isn't a loss, so hourly/daily P/L must be measured on this, not
    on raw cash. Returns None while money is mid-transit (see _pnl_in_flight)
    so the summary waits for a clean reading instead of reporting a fake
    loss or gain."""
    if _pnl_in_flight():
        return None
    bal = get_kalshi_account_balance()
    if bal is None:
        return None
    with positions_lock:
        basis = sum(pos["entry_price_cents"] / 100.0 * pos["count"] for pos in open_positions.values())
    if _pnl_in_flight():
        return None
    _reconcile_external_flow(bal, basis)
    return bal + basis

def _summary_alert_loop():
    """Checks periodically using actual exchange balances so restarts 
    or missed ticks never throw off your hourly/daily totals."""
    global _hourly_checkpoint_pnl, _hourly_checkpoint_time
    global _daily_checkpoint_pnl, _daily_checkpoint_time
    global _hourly_checkpoint_swept, _daily_checkpoint_swept
    global daily_biggest_win, daily_biggest_win_ticker

    while True:
        try:
            current_bal = get_account_equity()
            if current_bal is None:
                time.sleep(SUMMARY_CHECK_INTERVAL_SECONDS)
                continue

            now = time.time()

            # First clean reading becomes the baseline for both windows.
            if _hourly_checkpoint_pnl is None:
                _hourly_checkpoint_pnl = current_bal
                _hourly_checkpoint_swept = swept_total_dollars
            if _daily_checkpoint_pnl is None:
                _daily_checkpoint_pnl = current_bal
                _daily_checkpoint_swept = swept_total_dollars

            # Hourly Check (aligned or rolling)
            if now - _hourly_checkpoint_time >= 3600:
                hourly_delta = current_bal - _hourly_checkpoint_pnl + (swept_total_dollars - _hourly_checkpoint_swept)
                sign = "+" if hourly_delta >= 0 else ""
                send_alert(f"\U0001F550 HOURLY PROFIT: {sign}${hourly_delta:.2f} | END OF HOUR TOTAL: ${current_bal:.2f}")
                _hourly_checkpoint_pnl = current_bal
                _hourly_checkpoint_swept = swept_total_dollars
                _hourly_checkpoint_time = now

            # Daily Check (24h)
            if now - _daily_checkpoint_time >= 86400:
                daily_delta = current_bal - _daily_checkpoint_pnl + (swept_total_dollars - _daily_checkpoint_swept)
                sign = "+" if daily_delta >= 0 else ""
                window_start_dt = datetime.fromtimestamp(_daily_checkpoint_time)

                with session_pnl_lock:
                    best_win = daily_biggest_win
                    best_win_ticker = daily_biggest_win_ticker

                daily_msg = f"\U0001F4C5 DAILY PROFIT: {sign}${daily_delta:.2f} | ON THE DAY TOTAL: ${current_bal:.2f}"
                if best_win > 0:
                    daily_msg += f"\n\U0001F3C6 Biggest win today: +${best_win:.2f} ({best_win_ticker})"
                send_alert(daily_msg)

                chart_path = _build_equity_curve_chart(window_start_dt)
                if chart_path:
                    send_photo(chart_path, caption=f"\U0001F4C8 Equity curve \u2013 {sign}${daily_delta:.2f} on the day")

                _daily_checkpoint_pnl = current_bal
                _daily_checkpoint_swept = swept_total_dollars
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
    _series_label = SERIES_STATUS_LABELS.get(ACTIVE_SERIES_TICKER, ACTIVE_SERIES_TICKER)
    if NEUTRAL_MODE_ENABLED:
        _series_label = f"\U0001F9ED Neutral mode - auto-picked {_series_label}"
    lines = [
        "\U0001F4CA STATUS",
        f"Trading: {status_label}",
        f"Mood: {get_market_mood()}",
        f"Liquidity filter: {'OFF (exempt series)' if ACTIVE_SERIES_TICKER in LIQUIDITY_FILTER_EXEMPT_SERIES else ('ON' if LIQUIDITY_FILTER_ENABLED else 'OFF')} "
        f"(min depth {MIN_BOOK_DEPTH_CONTRACTS} contracts, min volume {MIN_MARKET_VOLUME_CONTRACTS} contracts)",
        f"Trailing stop: {'ON' if TRAILING_STOP_ENABLED else 'OFF'} for positions > {TRAILING_STOP_MIN_CONTRACTS} contracts "
        f"(arms at ${TRAILING_STOP_ARM_DOLLARS:.2f}, trails ${TRAILING_STOP_TRAIL_DOLLARS:.2f})",
        f"Trading series: {ACTIVE_SERIES_TICKER} ({_series_label})",
        f"Profit sweep: {'ON' if PROFIT_SWEEP_ENABLED else 'OFF'} (${PROFIT_SWEEP_THRESHOLD_DOLLARS:.2f} -> exchange {WITHDRAW_SHARD}, swept ${swept_total_dollars:.2f} so far)",
        f"Cross-series switch: {'ON' if CROSS_SERIES_SWITCH_ENABLED else 'OFF'}",
        f"Price-drop exit: {'ON' if PRICE_DROP_EXIT_ENABLED else 'OFF'} (sells at -{PRICE_DROP_EXIT_CENTS}\u00a2 from entry)",
        f"Early-resolve skip-ahead: ON (past {HARD_ABSOLUTE_MAX_MINUTES}m cap, ask \u2264{EARLY_RESOLVE_ASK_THRESHOLD_CENTS}\u00a2, "
        f">{EARLY_RESOLVE_MIN_SECONDS_LEFT}s left, no position held)",
    ]
    if real_pnl is not None:
        lines.append(f"Session P/L (real balance): ${real_pnl:.2f}")
    else:
        with session_pnl_lock:
            fallback_total = session_realized_pnl
        lines.append(f"Session P/L: ${fallback_total:.2f} (tracked trades only - a payout/order is still settling, so the live-balance figure is paused to avoid a false loss/gain)")
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
    "/tpbid <cents|off> - sell as soon as the bid reaches this many cents (e.g. /tpbid 99). The $ target can't fire on ~98-99c entries\n"
    "/setstoploss <amt> - change stop-loss amount\n"
    "/setlosslimit <amt> - change daily loss limit\n"
    "/setmultishare <count> - change multi-share trigger contract count\n"
    "/setthreshold <name> <value> - change a time/price trigger threshold\n"
    "/autosell on|off - toggle take-profit auto-sell\n"
    "/stoploss on|off - toggle stop-loss (use with care)\n"
    "/sweep on|off - auto-move profit to exchange 0 when it hits the sweep amount\n"
    "/setsweep <amt> - change the profit amount that triggers a sweep\n"
    "/sweepnow [amt] - sweep unswept profit (or a specific amount) right now\n"
    "/crossswitch on|off - on early resolve, hop to other series (BTC/ETH/SOL/gold/silver/natgas/platinum/palladium) if this one has nothing left\n"
    "/pricedropexit on|off - sell immediately if bid falls N\u00a2 below entry (/setthreshold pdc <cents>)\n"
    "/balances - show cash balance on every exchange shard, plus total\n"
    f"/fundtrading <amt> - move dollars from exchange {WITHDRAW_SHARD} into the trading exchange ({TRADING_SHARD})\n"
    "/nightmode on|off - switch budget/profit/stop-loss/limit/thresholds to night values\n"
    "/goldmode on|off - trade Gold 15min (KXGOLD15M) instead of Bitcoin\n"
    "/silvermode on|off - trade Silver 15min (KXSILVER15M) instead of Bitcoin\n"
    "/platinummode on|off - trade Platinum 15min (KXPLATINUM15M) instead of Bitcoin\n"
    "/palladiummode on|off - trade Palladium 15min (KXPALLADIUM15M) instead of Bitcoin\n"
    "/ethereummode on|off (or /ethmode) - trade Ethereum 15min (KXETH15M) instead of Bitcoin\n"
    "/solanamode on|off (or /solmode) - trade Solana 15min (KXSOL15M) instead of Bitcoin\n"
    "/naturalgasmode on|off (or /gasmode, /natgasmode) - trade natural gas 15min (KXNATGAS15M) instead of Bitcoin\n"
    "/neutralmode on|off - auto-pick the most STABLE series every 15-min window (late reversals + swings + liquidity)\n"
    "/sourcecheck [on|off|shadow] - checks each BTC/ETH/SOL buy against the real settlement index (CF Benchmarks) and vetoes it if the final average is projected too close to the strike. No arg = live test\n"
    "/sourcemode on|off - trades purely off the source check instead of your price triggers: buys at >=87% win chance inside the last 5m, panic-sells if it drops below 5%. BTC/ETH/SOL only\n"
    "/sourcemode autosell on|off - whether normal take-profit still applies to source-mode positions\n"
    "/setsourcemode buy|sell|tight <pct> - tune source mode's buy / panic-sell / max choppy-market panic-sell thresholds\n"
    "/sourcemode adapt on|off - raise the panic-sell line on a market while it's choppy, then relax it back automatically\n"
    "/sourcemode chase on|off - momentum-proof entries: IOC orders that pay a few cents over the ask and retry if the price runs\n"
    "/setsourcemode chase <cents> - how many cents over the ask an entry may pay (0-10)\n"
    "/sourcemode scale on|off - scale the buy and panic-sell lines with volatility (calm = buy early + tight panic line, wild = stricter buy + more room)\n"
    "/setsourcescale calm <buy> <sell> | hot <buy> <sell> | range <calm_x> <hot_x> - tune scale mode (e.g. /setsourcescale calm 90 88)\n"
    "/satellite [ticker] / /satellite stop - streams a ticker's win-chance to the console every second until stopped\n"
    "/pythfeed - connection status for the gold/silver/platinum/palladium/natgas websocket feed\n"
    "/setsource z|margin <value> - tune the source check (z-score needed / minimum lead in bps)\n"
    "/neutralrank - show how each series scores right now and whether it passes the floors (doesn't switch anything)\n"
    "/neutralfloors on|off - hard floors: neutral mode SKIPS series that are too swingy/reversal-prone/thin instead of trading the best of a bad lot\n"
    "/setneutral <reversal|swing|depth|spread|mindepth|sizefrac> <value> - tune those floors (depth = full-size line, mindepth = hard minimum, sizefrac = % of depth a thin-book buy may take)\n"
    "/neutralsize on|off - trade thin series at reduced size (on) instead of skipping them (off)\n"
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
    global GOLD_MODE_ENABLED, SILVER_MODE_ENABLED, PLATINUM_MODE_ENABLED, PALLADIUM_MODE_ENABLED, ETH_MODE_ENABLED, SOL_MODE_ENABLED, NATGAS_MODE_ENABLED, ACTIVE_SERIES_TICKER
    global PROFIT_SWEEP_ENABLED, PROFIT_SWEEP_THRESHOLD_DOLLARS, CROSS_SERIES_SWITCH_ENABLED
    global PRICE_DROP_EXIT_ENABLED

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
                        send_alert(f"\U0001F4B0 Session P/L: ${fallback:.2f} (tracked trades only - a payout/order is still settling, so the live-balance figure is paused to avoid a false loss/gain)")
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
                            amt = round(entry.get("amount", 0.0), 2)
                            if amt == 0:
                                amt = 0.0  # normalize -0.0 -> 0.0 so it never prints as "-0.00"
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
                        f"Take-profit bid trigger: {str(TAKE_PROFIT_BID_CENTS) + chr(162) if TAKE_PROFIT_BID_CENTS > 0 else 'OFF'}\n"
                        f"Stop-loss: ${STOP_LOSS_DOLLARS:.2f} {'(OFF)' if not STOP_LOSS_ENABLED else ''}\n"
                        f"Stop-loss confirmation: {STOP_LOSS_CONFIRMATION_SECONDS}s "
                        f"(if <{STOP_LOSS_CONFIRMATION_TIME_THRESHOLD_MINUTES}m left)\n"
                        f"Daily loss limit: ${DAILY_LOSS_LIMIT_DOLLARS:.2f}"
                        f"{' (OVERRIDDEN)' if loss_limit_overridden else ''}\n"
                        f"Mode: {'DEMO' if DEMO_MODE else 'LIVE'}\n"
                        f"Night mode: {night_label}\n"
                        f"Profit sweep: {'ON' if PROFIT_SWEEP_ENABLED else 'OFF'} (every ${PROFIT_SWEEP_THRESHOLD_DOLLARS:.2f} -> exchange {WITHDRAW_SHARD}, swept so far ${swept_total_dollars:.2f})\n"
                        f"Cross-series switch: {'ON' if CROSS_SERIES_SWITCH_ENABLED else 'OFF'}\n"
                        f"Price-drop exit: {'ON' if PRICE_DROP_EXIT_ENABLED else 'OFF'} (sells at -{PRICE_DROP_EXIT_CENTS}\u00a2 from entry)\n"
                        f"Source mode: {'ON' if SOURCE_MODE_ENABLED else 'OFF'}\n"
                        f"  Buy at \u2265 {SOURCE_MODE_BUY_PROB:.0%} win chance, panic-sell below {SOURCE_MODE_SELL_PROB:.0%}\n"
                        f"  Active in last {SOURCE_MODE_WINDOW_MINUTES:g}m of each window, autosell {'ON' if SOURCE_MODE_AUTOSELL else 'OFF'}\n"
                        f"  Adaptive sell line: {'ON' if SOURCE_MODE_ADAPT_ENABLED else 'OFF'} (rises up to "
                        f"{min(SOURCE_MODE_ADAPT_MAX_SELL_PROB, SOURCE_MODE_BUY_PROB - 0.02):.0%} when choppy, relaxes after {SOURCE_MODE_ADAPT_HOLD_SECONDS}s calm)"
                        f"{_source_mode_tight_summary()}\n"
                        f"  Momentum chase: {'ON' if SOURCE_MODE_CHASE_ENABLED else 'OFF'} (IOC entry, up to {SOURCE_MODE_CHASE_CENTS}\u00a2 over the ask, "
                        f"{SOURCE_MODE_ENTRY_ATTEMPTS} tries/scan)\n"
                        f"  Volatility scaling: {'ON' if SOURCE_MODE_SCALE_ENABLED else 'OFF'} (calm {SOURCE_MODE_SCALE_CALM_BUY:.0%}/{SOURCE_MODE_SCALE_CALM_SELL:.0%}"
                        f" -> wild {SOURCE_MODE_SCALE_HOT_BUY:.0%}/{SOURCE_MODE_SCALE_HOT_SELL:.0%} buy/panic, vol {SOURCE_MODE_SCALE_CALM_RATIO:g}x-{SOURCE_MODE_SCALE_HOT_RATIO:g}x)\n"
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
                        send_alert(f"\U0001F4B5 Manually sold {filled} of {position['count']} {ticker} @ {current_bid}\u00a2 (via /sell).")
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

                elif text.startswith("/tpbid"):
                    parts = raw_text.split()
                    if len(parts) == 2 and parts[1].lower() == "off":
                        globals()["TAKE_PROFIT_BID_CENTS"] = 0
                        _save_config_override("TAKE_PROFIT_BID_CENTS", 0)
                        send_alert("\u26A0\uFE0F Cents-based take-profit OFF. Saved - survives restarts.")
                    else:
                        val = _parse_float_arg(raw_text)
                        if val is None or not (50 <= val <= 99):
                            send_alert("Usage: /tpbid <cents|off>, e.g. /tpbid 99  (sells once the bid hits 99\u00a2 and you're not under water). "
                                       f"Now: {str(TAKE_PROFIT_BID_CENTS) + chr(162) if TAKE_PROFIT_BID_CENTS > 0 else 'OFF'}")
                        else:
                            globals()["TAKE_PROFIT_BID_CENTS"] = val
                            _save_config_override("TAKE_PROFIT_BID_CENTS", val)
                            send_alert(f"\u2705 Cents-based take-profit set: sells once the bid reaches {val:g}\u00a2. Saved - survives restarts.")

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
                        send_alert("Usage: /setthreshold <name> <value>\nNames (old 3-letter codes and full snake_case names also still work): " + ", ".join(THRESHOLD_SHORT_NAMES))
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

                elif text.startswith("/setsweep"):
                    val = _parse_float_arg(raw_text)
                    if val is None or val <= 0:
                        send_alert("Usage: /setsweep <amount>, e.g. /setsweep 5")
                    else:
                        PROFIT_SWEEP_THRESHOLD_DOLLARS = val
                        _save_config_override("PROFIT_SWEEP_THRESHOLD_DOLLARS", val)
                        send_alert(f"\u2705 Profit sweep threshold set to ${val:.2f}. Saved - survives restarts.")

                elif text == "/sweep on":
                    PROFIT_SWEEP_ENABLED = True
                    _save_config_override("PROFIT_SWEEP_ENABLED", True)
                    send_alert(f"\u2705 Profit sweep ON - moves profit to exchange {WITHDRAW_SHARD} every "
                               f"${PROFIT_SWEEP_THRESHOLD_DOLLARS:.2f}. Saved - survives restarts.")
                elif text == "/sweep off":
                    PROFIT_SWEEP_ENABLED = False
                    _save_config_override("PROFIT_SWEEP_ENABLED", False)
                    send_alert("\u26A0\uFE0F Profit sweep OFF - profit stays on the trading shard. Saved - survives restarts.")

                elif text.startswith("/sweepnow"):
                    # /sweepnow = sweep ALL unswept profit; /sweepnow 0.10 = sweep exactly that much (good for a first test)
                    parts = raw_text.split()
                    with _sweep_lock:
                        if _sweep_state["unconfirmed"]:
                            send_alert("A previous sweep hasn't shown up in the balance yet - wait for it to confirm first.")
                            continue
                        if len(parts) >= 2:
                            amt = _parse_float_arg(raw_text)
                            if amt is None or amt <= 0:
                                send_alert("Usage: /sweepnow or /sweepnow <amount>, e.g. /sweepnow 0.10")
                                continue
                        else:
                            amt, why = _safe_sweepable_amount(require_stable=False)
                            if amt is None:
                                send_alert(f"Not sweeping right now: {why}. (Nothing is lost - it'll sweep once that clears. "
                                           f"/sweepnow <amount> forces a specific amount.)")
                                continue
                        if amt <= 0:
                            send_alert("No unswept profit to move right now.")
                        elif not _sweep_funds(amt, "manual /sweepnow"):
                            send_alert("Sweep didn't go through - see the log (/log) for why.")

                elif text == "/crossswitch on":
                    CROSS_SERIES_SWITCH_ENABLED = True
                    _save_config_override("CROSS_SERIES_SWITCH_ENABLED", True)
                    send_alert("\u2705 Cross-series early-resolve switching ON. Saved - survives restarts.")
                elif text == "/crossswitch off":
                    CROSS_SERIES_SWITCH_ENABLED = False
                    _save_config_override("CROSS_SERIES_SWITCH_ENABLED", False)
                    send_alert("\u26A0\uFE0F Cross-series switching OFF - early resolves only look inside the active series. Saved - survives restarts.")

                elif text == "/pricedropexit on":
                    PRICE_DROP_EXIT_ENABLED = True
                    _save_config_override("PRICE_DROP_EXIT_ENABLED", True)
                    send_alert(f"\u2705 Price-drop exit ON - sells immediately if the bid falls "
                               f"{PRICE_DROP_EXIT_CENTS}\u00a2 or more below entry. Saved - survives restarts.")
                elif text == "/pricedropexit off":
                    PRICE_DROP_EXIT_ENABLED = False
                    _save_config_override("PRICE_DROP_EXIT_ENABLED", False)
                    send_alert("\u26A0\uFE0F Price-drop exit OFF. Saved - survives restarts.")

                elif text == "/balances":
                    total, breakdown = get_all_exchange_balances()
                    if total is None:
                        send_alert("Couldn't fetch balances right now - see the log (/log) for why.")
                    else:
                        lines = [f"\U0001F4CA Exchange balances:"]
                        for idx in sorted(breakdown.keys()):
                            tag = " (trading)" if idx == TRADING_SHARD else (" (withdraw)" if idx == WITHDRAW_SHARD else "")
                            lines.append(f"Exchange {idx}{tag}: ${breakdown[idx]:.2f}")
                        lines.append(f"Total: ${total:.2f}")
                        send_alert("\n".join(lines))

                elif text.startswith("/fundtrading"):
                    # Moves money INTO the trading shard - the reverse of
                    # /sweepnow (which moves profit OUT). Plain dollar amount;
                    # converted to centicents internally, no manual math needed.
                    amt = _parse_float_arg(raw_text)
                    if amt is None or amt <= 0:
                        send_alert(f"Usage: /fundtrading <amount>, e.g. /fundtrading 25 "
                                   f"(moves that many dollars from exchange {WITHDRAW_SHARD} to exchange {TRADING_SHARD})")
                    else:
                        ok, result = fund_trading_shard(amt)
                        if ok:
                            send_alert(f"\u2705 Sent ${amt:.2f} from exchange {WITHDRAW_SHARD} to exchange "
                                       f"{TRADING_SHARD}. Transfer ID: {result}")
                        else:
                            send_alert(f"\u26A0\uFE0F Transfer failed: {result}")

                elif text == "/autosell on":
                    AUTOSELLING = True
                    _save_config_override("AUTOSELLING", True)
                    send_alert("\u2705 Take-profit auto-sell ENABLED. Saved - survives restarts.")
                elif text == "/autosell off":
                    AUTOSELLING = False
                    _save_config_override("AUTOSELLING", False)
                    send_alert("\u26A0\uFE0F Take-profit auto-sell DISABLED for ALL positions, source-mode ones included. "
                                "Winning positions will ride to expiration instead of being sold early. Saved - survives restarts.")

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

                elif text in ("/neutralmode on", "/neutralmode off"):
                    if text.endswith(" on") and NEUTRAL_MODE_ENABLED:
                        send_alert("\U0001F9ED Neutral mode is already ON. Nothing changed. /neutralrank shows the current scores.")
                        continue
                    if text.endswith(" off") and not NEUTRAL_MODE_ENABLED:
                        send_alert(f"\U0001F9ED Neutral mode is already OFF. Nothing changed (currently: {_current_mode_text()}).")
                        continue
                    for _flag in MODE_FLAG_NAMES:
                        globals()[_flag] = False
                    if text.endswith(" on"):
                        globals()["NEUTRAL_MODE_ENABLED"] = True
                        globals()["_neutral_force_pick"] = True  # pick right away, then once per window
                        msg = ("\U0001F9ED NEUTRAL MODE ON - picking the most stable series now, then re-picking every "
                               "15-min window just before the buy window opens. Other modes are off. /neutralrank shows the scores. "
                               "Saved - survives restarts.")
                    else:
                        ACTIVE_SERIES_TICKER = SERIES_TICKER_BTC
                        msg = f"\U0001F9ED NEUTRAL MODE OFF - back to trading {SERIES_TICKER_BTC}. Saved - survives restarts."
                    for _flag in MODE_FLAG_NAMES:
                        _save_config_override(_flag, globals()[_flag])
                    _save_config_override("ACTIVE_SERIES_TICKER", ACTIVE_SERIES_TICKER)
                    _active_market_cache["ticker"] = None
                    _active_market_cache["close_time"] = None
                    send_alert(msg)

                elif text in ("/sourcemode on", "/sourcemode off"):
                    if text.endswith(" on") == SOURCE_MODE_ENABLED:
                        send_alert(f"\U0001F6F0\uFE0F Source mode is already {'ON' if SOURCE_MODE_ENABLED else 'OFF'}. Nothing changed.")
                        continue
                    globals()["SOURCE_MODE_ENABLED"] = text.endswith(" on")
                    _save_config_override("SOURCE_MODE_ENABLED", SOURCE_MODE_ENABLED)
                    if SOURCE_MODE_ENABLED:
                        send_alert(f"\U0001F6F0\uFE0F SOURCE MODE ON - your normal price triggers are OFF for new buys. "
                                   f"In the last {SOURCE_MODE_WINDOW_MINUTES:g}m of each window, it buys whichever side's "
                                   f"win chance is \u2265 {SOURCE_MODE_BUY_PROB:.0%}, and sells immediately if the held "
                                   f"side's win chance drops below {SOURCE_MODE_SELL_PROB:.0%}. Covers BTC/ETH/SOL only - "
                                   f"gold/silver/platinum/palladium/natgas have no REST-accessible index. Saved.")
                    else:
                        send_alert("\u26A0\uFE0F Source mode OFF - normal price triggers are back on. Saved.")

                elif text in ("/sourcemode autosell on", "/sourcemode autosell off"):
                    if text.endswith(" on") == SOURCE_MODE_AUTOSELL:
                        send_alert(f"\U0001F6F0\uFE0F Source mode autosell is already {'ON' if SOURCE_MODE_AUTOSELL else 'OFF'}. Nothing changed.")
                        continue
                    globals()["SOURCE_MODE_AUTOSELL"] = text.endswith(" on")
                    _save_config_override("SOURCE_MODE_AUTOSELL", SOURCE_MODE_AUTOSELL)
                    if SOURCE_MODE_AUTOSELL and not AUTOSELLING:
                        send_alert("\u26A0\uFE0F Source mode autosell ON, but the main /autosell is OFF and it takes priority - "
                                   "nothing will take profit early until you run /autosell on. Saved.")
                    elif SOURCE_MODE_AUTOSELL:
                        send_alert("\u2705 Source mode autosell ON - normal take-profit still applies to source-mode "
                                   "positions. The panic-exit (<5% win chance) and stop-loss still protect them either way. Saved.")
                    else:
                        send_alert("\u26A0\uFE0F Source mode autosell OFF - source-mode positions ride to settlement "
                                   "(or the panic-exit/stop-loss) instead of taking a normal profit early. Saved.")

                elif text in ("/sourcemode scale on", "/sourcemode scale off"):
                    globals()["SOURCE_MODE_SCALE_ENABLED"] = text.endswith(" on")
                    _save_config_override("SOURCE_MODE_SCALE_ENABLED", SOURCE_MODE_SCALE_ENABLED)
                    if SOURCE_MODE_SCALE_ENABLED:
                        send_alert(f"\U0001F4C8 Volatility scaling ON. Calm market (vol \u2264 {SOURCE_MODE_SCALE_CALM_RATIO:g}x): buy \u2265 "
                                   f"{SOURCE_MODE_SCALE_CALM_BUY:.0%}, panic below {SOURCE_MODE_SCALE_CALM_SELL:.0%}. Wild (vol \u2265 "
                                   f"{SOURCE_MODE_SCALE_HOT_RATIO:g}x): buy \u2265 {SOURCE_MODE_SCALE_HOT_BUY:.0%}, panic below "
                                   f"{SOURCE_MODE_SCALE_HOT_SELL:.0%}. Blends smoothly in between. Replaces your saved "
                                   f"{SOURCE_MODE_BUY_PROB:.0%}/{SOURCE_MODE_SELL_PROB:.0%} while on (they're kept for when it's off). Saved.")
                    else:
                        send_alert(f"\u26A0\uFE0F Volatility scaling OFF - back to your fixed lines: buy \u2265 {SOURCE_MODE_BUY_PROB:.0%}, "
                                   f"panic below {SOURCE_MODE_SELL_PROB:.0%}. Saved.")

                elif text.startswith("/setsourcescale"):
                    parts = raw_text.split()
                    usage = ("Usage: /setsourcescale calm <buy> <sell>  |  hot <buy> <sell>  |  range <calm_x> <hot_x>\n"
                             f"Now: calm {SOURCE_MODE_SCALE_CALM_BUY:.0%}/{SOURCE_MODE_SCALE_CALM_SELL:.0%}, wild "
                             f"{SOURCE_MODE_SCALE_HOT_BUY:.0%}/{SOURCE_MODE_SCALE_HOT_SELL:.0%}, vol range "
                             f"{SOURCE_MODE_SCALE_CALM_RATIO:g}x-{SOURCE_MODE_SCALE_HOT_RATIO:g}x")
                    try:
                        kind = parts[1].lower()
                        if kind in ("calm", "hot") and len(parts) >= 4:
                            vals = [float(parts[2]), float(parts[3])]
                            vals = [v / 100.0 if v > 1 else v for v in vals]
                            buy, sell = vals
                            if not (0.5 <= sell < buy <= 0.999):
                                raise ValueError
                            pre = "SOURCE_MODE_SCALE_CALM" if kind == "calm" else "SOURCE_MODE_SCALE_HOT"
                            globals()[pre + "_BUY"], globals()[pre + "_SELL"] = buy, sell
                            _save_config_override(pre + "_BUY", buy)
                            _save_config_override(pre + "_SELL", sell)
                            send_alert(f"\u2705 {kind.capitalize()} market lines set: buy \u2265 {buy:.0%}, panic below {sell:.0%}. Saved.")
                        elif kind == "range" and len(parts) >= 4:
                            lo, hi = float(parts[2]), float(parts[3])
                            if not (0 < lo < hi):
                                raise ValueError
                            globals()["SOURCE_MODE_SCALE_CALM_RATIO"], globals()["SOURCE_MODE_SCALE_HOT_RATIO"] = lo, hi
                            _save_config_override("SOURCE_MODE_SCALE_CALM_RATIO", lo)
                            _save_config_override("SOURCE_MODE_SCALE_HOT_RATIO", hi)
                            send_alert(f"\u2705 Volatility range set: calm at \u2264 {lo:g}x normal, wild at \u2265 {hi:g}x. "
                                       f"(Narrower = more sensitive.) Saved.")
                        else:
                            send_alert(usage)
                    except (ValueError, IndexError):
                        send_alert(usage)

                elif text in ("/sourcemode chase on", "/sourcemode chase off"):
                    globals()["SOURCE_MODE_CHASE_ENABLED"] = text.endswith(" on")
                    _save_config_override("SOURCE_MODE_CHASE_ENABLED", SOURCE_MODE_CHASE_ENABLED)
                    if SOURCE_MODE_CHASE_ENABLED:
                        send_alert(f"\U0001F3C3 Momentum chase ON. Entries are immediate-or-cancel orders that may pay up to "
                                   f"{SOURCE_MODE_CHASE_CENTS}\u00a2 over the ask (never above the model's win chance), retry up to "
                                   f"{SOURCE_MODE_ENTRY_ATTEMPTS}x per scan if the price runs, and nothing is left resting. Saved.")
                    else:
                        send_alert("\u26A0\uFE0F Momentum chase OFF - entries go back to a resting order at the ask seen. Saved.")

                elif text in ("/sourcemode adapt on", "/sourcemode adapt off"):
                    globals()["SOURCE_MODE_ADAPT_ENABLED"] = text.endswith(" on")
                    _save_config_override("SOURCE_MODE_ADAPT_ENABLED", SOURCE_MODE_ADAPT_ENABLED)
                    if SOURCE_MODE_ADAPT_ENABLED:
                        send_alert(f"\U0001F30A Adaptive panic-sell line ON. When a market gets choppy (vol \u2265 "
                                   f"{SOURCE_MODE_ADAPT_START_RATIO:g}x normal) the line rises from {SOURCE_MODE_SELL_PROB:.0%} "
                                   f"toward {min(SOURCE_MODE_ADAPT_MAX_SELL_PROB, SOURCE_MODE_BUY_PROB - 0.02):.0%}, and relaxes back "
                                   f"after {SOURCE_MODE_ADAPT_HOLD_SECONDS}s of calm. Your saved {SOURCE_MODE_SELL_PROB:.0%} is never changed. Saved.")
                    else:
                        send_alert(f"\u26A0\uFE0F Adaptive panic-sell line OFF - the line stays fixed at {SOURCE_MODE_SELL_PROB:.0%}. Saved.")

                elif text.startswith("/setsourcemode"):
                    parts = raw_text.split()
                    if len(parts) > 2 and parts[1].lower() == "chase":
                        try:
                            cents = int(float(parts[2]))
                            if not (0 <= cents <= 10):
                                raise ValueError
                        except ValueError:
                            send_alert(f"Usage: /setsourcemode chase <cents 0-10>   (now {SOURCE_MODE_CHASE_CENTS}\u00a2)")
                            continue
                        globals()["SOURCE_MODE_CHASE_CENTS"] = cents
                        _save_config_override("SOURCE_MODE_CHASE_CENTS", cents)
                        send_alert(f"\u2705 Momentum chase set to {cents}\u00a2 over the ask. Saved.")
                        continue
                    try:
                        key, val = parts[1].lower(), float(parts[2])
                        if key not in ("buy", "sell", "tight") or not (0 < val < 100):
                            raise ValueError
                        val = val / 100.0 if val > 1 else val
                    except (IndexError, ValueError):
                        send_alert("Usage: /setsourcemode buy <pct>  |  sell <pct>  |  tight <pct>\n"
                                   f"Now: buy \u2265 {SOURCE_MODE_BUY_PROB:.0%}, sell below {SOURCE_MODE_SELL_PROB:.0%}, "
                                   f"choppy-market max {SOURCE_MODE_ADAPT_MAX_SELL_PROB:.0%}")
                        continue
                    name = {"buy": "SOURCE_MODE_BUY_PROB", "sell": "SOURCE_MODE_SELL_PROB",
                            "tight": "SOURCE_MODE_ADAPT_MAX_SELL_PROB"}[key]
                    globals()[name] = val
                    _save_config_override(name, val)
                    send_alert(f"\u2705 Source mode {key} threshold set to {val:.0%}. Saved.")

                elif text == "/pythfeed":
                    send_alert(_format_pyth_status())

                elif text.startswith("/satellite"):
                    parts = raw_text.split()
                    arg = parts[1] if len(parts) > 1 else None
                    if arg and arg.lower() == "stop":
                        stopped = _satellite_stop()
                        if stopped:
                            send_alert(f"\U0001F6F0\uFE0F Satellite stopped ({stopped}). Nothing more will be sent from it.")
                        else:
                            send_alert("Satellite isn't running.")
                    else:
                        ticker = arg or _active_market_cache.get("ticker")
                        if not ticker:
                            send_alert("Usage: /satellite <ticker>  (or /satellite with no ticker once a market is active)\n"
                                       "/satellite stop ends it.")
                            continue
                        ok, running = _satellite_start(ticker, on_started=lambda t=ticker: send_alert(
                            f"\U0001F6F0\uFE0F Satellite streaming {t} to the console every second. "
                            f"Telegram gets an update every {SATELLITE_TELEGRAM_INTERVAL_SECONDS}s. /satellite stop to end it."))
                        if not ok:
                            send_alert(f"\U0001F6F0\uFE0F A satellite is already running on {running}. Only one at a time - "
                                       f"/satellite stop first.")

                elif text.startswith("/sourcecheck"):
                    arg = raw_text.split()[1].lower() if len(raw_text.split()) > 1 else "status"
                    if arg in ("on", "off", "shadow"):
                        globals()["SOURCE_CHECK_ENABLED"] = arg != "off"
                        globals()["SOURCE_CHECK_SHADOW"] = arg == "shadow"
                        _save_config_override("SOURCE_CHECK_ENABLED", SOURCE_CHECK_ENABLED)
                        _save_config_override("SOURCE_CHECK_SHADOW", SOURCE_CHECK_SHADOW)
                        if arg == "on":
                            send_alert("\u2705 Source check ENFORCING - BTC/ETH/SOL buys are vetoed when the real index average isn't safely on your side. Saved.")
                        elif arg == "shadow":
                            send_alert("\U0001F441\uFE0F Source check in SHADOW mode - logs and alerts what it WOULD veto, but still lets the buy through. Saved.")
                        else:
                            send_alert("\u26A0\uFE0F Source check OFF. Saved.")
                    else:
                        send_alert("\U0001F6E1\uFE0F Checking the live index - a few seconds...")
                        threading.Thread(target=lambda: send_alert(_format_source_check_status()), daemon=True).start()

                elif text.startswith("/setsource"):
                    parts = raw_text.split()
                    try:
                        key, val = parts[1].lower(), float(parts[2])
                        if key not in ("z", "margin") or val < 0:
                            raise ValueError
                    except (IndexError, ValueError):
                        send_alert("Usage: /setsource z <value>  or  /setsource margin <bps>\n"
                                   f"Now: z \u2265 {SOURCE_CHECK_MIN_Z:g}, lead \u2265 {SOURCE_CHECK_MIN_MARGIN_BPS:g}bps. Higher z = pickier "
                                   "(z 2 \u2248 98% win odds on the model, z 3 \u2248 99.9%).")
                        continue
                    name = "SOURCE_CHECK_MIN_Z" if key == "z" else "SOURCE_CHECK_MIN_MARGIN_BPS"
                    globals()[name] = val
                    _save_config_override(name, val)
                    send_alert(f"\u2705 Source check {key} set to {val:g}. Saved - survives restarts.")

                elif text in ("/neutralfloors on", "/neutralfloors off"):
                    globals()["NEUTRAL_FLOORS_ENABLED"] = text.endswith(" on")
                    _save_config_override("NEUTRAL_FLOORS_ENABLED", NEUTRAL_FLOORS_ENABLED)
                    if NEUTRAL_FLOORS_ENABLED:
                        send_alert("\u2705 Neutral floors ON - neutral mode skips any series that's too swingy, reversal-prone, thin or wide. Saved.")
                    else:
                        send_alert("\u26A0\uFE0F Neutral floors OFF - neutral mode will trade the best-ranked series even if it's junk. Saved.")

                elif text in ("/neutralsize on", "/neutralsize off"):
                    globals()["NEUTRAL_REDUCE_SIZE_ENABLED"] = text.endswith(" on")
                    _save_config_override("NEUTRAL_REDUCE_SIZE_ENABLED", NEUTRAL_REDUCE_SIZE_ENABLED)
                    if NEUTRAL_REDUCE_SIZE_ENABLED:
                        send_alert(f"\u2705 Thin-book sizing ON - series with depth {NEUTRAL_REDUCED_MIN_DEPTH_CONTRACTS}-{NEUTRAL_MIN_DEPTH_CONTRACTS - 1} "
                                   f"trade at up to {NEUTRAL_DEPTH_SIZE_FRACTION:.0%} of their depth. Saved.")
                    else:
                        send_alert(f"\u26A0\uFE0F Thin-book sizing OFF - series under {NEUTRAL_MIN_DEPTH_CONTRACTS} depth are skipped. Saved.")

                elif text.startswith("/setneutral"):
                    parts = raw_text.split()
                    names = {"reversal": "NEUTRAL_MAX_REVERSAL_RATE", "swing": "NEUTRAL_MAX_SWING_CENTS",
                             "depth": "NEUTRAL_MIN_DEPTH_CONTRACTS", "spread": "NEUTRAL_MAX_SPREAD_CENTS",
                             "mindepth": "NEUTRAL_REDUCED_MIN_DEPTH_CONTRACTS", "sizefrac": "NEUTRAL_DEPTH_SIZE_FRACTION"}
                    try:
                        key = parts[1].lower()
                        val = float(parts[2])
                        if key not in names or val < 0:
                            raise ValueError
                    except (IndexError, ValueError):
                        send_alert("Usage: /setneutral <reversal|swing|depth|spread> <value>\n"
                                   "e.g. /setneutral swing 5   /setneutral reversal 10 (percent)   /setneutral depth 60   /setneutral spread 2\n"
                                   f"Now: reversal \u2264 {NEUTRAL_MAX_REVERSAL_RATE:.0%}, swing \u2264 {NEUTRAL_MAX_SWING_CENTS:.1f}\u00a2/min, "
                                   f"depth \u2265 {NEUTRAL_MIN_DEPTH_CONTRACTS}, spread \u2264 {NEUTRAL_MAX_SPREAD_CENTS}\u00a2")
                        continue
                    if key in ("reversal", "sizefrac") and val > 1:
                        val = val / 100.0  # accept "15" as 15%
                    if key in ("depth", "spread", "mindepth"):
                        val = int(val)
                    if key == "sizefrac" and not (0.05 <= val <= 1.0):
                        send_alert("sizefrac must be between 5 and 100 (percent of visible depth a thin-book buy may take).")
                        continue
                    globals()[names[key]] = val
                    _save_config_override(names[key], val)
                    send_alert(f"\u2705 Neutral floor set: {key} = {val if key not in ('reversal', 'sizefrac') else format(val, '.0%')}. Saved - survives restarts.")

                elif text == "/neutralrank":
                    # Runs on its own thread: it makes a bunch of API calls and shouldn't stall command polling.
                    send_alert("\U0001F9ED Scoring every series - give it a few seconds...")
                    threading.Thread(target=lambda: send_alert(_format_neutral_ranking(_rank_series())), daemon=True).start()

                elif (len(text.split(" ")) == 2 and text.split(" ")[1] in ("on", "off")
                      and text.split(" ")[0][1:] in MODE_COMMANDS):
                    # Exactly one series is ever active. Picking a mode ON
                    # switches straight to it (and turns the others off);
                    # turning the active one OFF falls back to Bitcoin.
                    # Dropping the cached event/close-time makes the very
                    # next scan re-resolve against the new series immediately,
                    # instead of finishing out whatever ticker was cached.
                    cmd_name, action = text[1:].split(" ")  # e.g. "goldmode", "on"
                    series, label, flag_name = MODE_COMMANDS[cmd_name]

                    if action == "on" and globals().get(flag_name) and ACTIVE_SERIES_TICKER == series:
                        send_alert(f"{label} is already ON - already trading {series}. Nothing changed.")
                        continue
                    if action == "off" and not globals().get(flag_name):
                        send_alert(f"{label} is already OFF. Nothing changed (currently: {_current_mode_text()}).")
                        continue

                    for _flag in MODE_FLAG_NAMES:
                        globals()[_flag] = False

                    if action == "on":
                        ACTIVE_SERIES_TICKER = series
                        globals()[flag_name] = True
                        msg = f"{label} ON - now trading {series} exclusively. Saved - survives restarts."
                    else:
                        ACTIVE_SERIES_TICKER = SERIES_TICKER_BTC
                        msg = f"{label} OFF - back to trading {SERIES_TICKER_BTC}. Saved - survives restarts."

                    for _flag in MODE_FLAG_NAMES:
                        _save_config_override(_flag, globals()[_flag])
                    _save_config_override("ACTIVE_SERIES_TICKER", ACTIVE_SERIES_TICKER)
                    _active_market_cache["ticker"] = None
                    _active_market_cache["close_time"] = None
                    send_alert(msg)

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
    threading.Thread(target=_source_prefetch_loop, daemon=True).start()
    threading.Thread(target=_position_reconcile_loop, daemon=True).start()
    print(f"--> Position reconcile thread started (checks Kalshi's real positions every {POSITION_RECONCILE_SECONDS}s and adopts any the bot isn't tracking).")
    print(f"--> Source prefetch thread started (refreshes the index every {SOURCE_PREFETCH_SECONDS}s while a source-mode position is open).")
    print(f"--> Position monitor thread started (checking open positions every {POSITION_CHECK_INTERVAL_SECONDS}s).")

    sweep_thread = threading.Thread(target=_profit_sweep_loop, daemon=True)
    sweep_thread.start()
    _start_pyth_feed()
    print("--> Pyth feed thread started (gold/silver/platinum/palladium/natgas source check).")

    neutral_thread = threading.Thread(target=_neutral_mode_loop, daemon=True)
    neutral_thread.start()
    print(f"--> Neutral mode thread started (currently {'ON' if NEUTRAL_MODE_ENABLED else 'OFF'}; /neutralmode on to use it).")

    print(f"--> Profit sweep thread started (auto-sweeps to shard {WITHDRAW_SHARD} at ${PROFIT_SWEEP_THRESHOLD_DOLLARS:.2f} profit; currently {'ON' if PROFIT_SWEEP_ENABLED else 'OFF'}).")

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

        send_alert(f"\u2705 Started Trading | Mode: {'DEMO' if DEMO_MODE else 'LIVE'} | Current Budget: ${BUDGET_DOLLARS:.2f}")
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
                # The neutral thread can switch ACTIVE_SERIES_TICKER while we're mid-lookup;
                # don't cache a market from the series we just switched away from.
                if resolved_ticker and _series_of(resolved_ticker) == ACTIVE_SERIES_TICKER:
                    close_time = _get_cached_close_time(resolved_ticker, close_time_hint)
                    market_ticker = resolved_ticker
                    _active_market_cache["ticker"] = resolved_ticker
                    _active_market_cache["close_time"] = close_time

            if market_ticker:
                result = check_market_and_trade(market_ticker)

                if result == "EXHAUSTED":
                    # This ticker already resolved early with time still on
                    # the clock and we're not holding it - drop it and look
                    # for a fresher window among the other currently-open
                    # candidates for this series, rather than keep polling
                    # a dead one until its official close_time.
                    _active_market_cache["ticker"] = None
                    _active_market_cache["close_time"] = None
                    _mark_exhausted(market_ticker)
                    if NEUTRAL_MODE_ENABLED:
                        # Re-rank right now against live books (the dead ticker is excluded)
                        # so the hop lands on the BEST series, not just the deepest book.
                        try:
                            _neutral_pick_and_apply("early resolve")
                        except Exception as e:
                            print(f"--> [WARNING] Neutral re-pick after early resolve failed: {e}")
                    next_ticker, next_close_time = None, None
                    for candidate_event_ticker, _ in get_candidate_event_tickers():
                        resolved, close_hint = get_active_market_strike_ticker(candidate_event_ticker)
                        if resolved and resolved != market_ticker and not _is_recently_exhausted(resolved):
                            next_ticker = resolved
                            next_close_time = _get_cached_close_time(resolved, close_hint)
                            break

                    # Nothing else open in THIS series (normal - only one 15m
                    # window is open per series at a time), so look across the
                    # other series for a live, liquid market instead.
                    if (not next_ticker and CROSS_SERIES_SWITCH_ENABLED
                            and time.time() - _last_cross_series_scan >= CROSS_SERIES_SCAN_COOLDOWN_SECONDS):
                        _last_cross_series_scan = time.time()
                        next_ticker, next_close_time = find_cross_series_candidate(market_ticker)
                        if next_ticker and _series_of(next_ticker) != _series_of(market_ticker):
                            push_alert(f"\U0001F504 {_series_of(market_ticker)} resolved early - switching to "
                                       f"{next_ticker} until it closes.")

                    local_time_str = time.strftime('%I:%M:%S %p')
                    if next_ticker:
                        print(f"[{local_time_str}] [EARLY RESOLVE] Switching to {next_ticker} (was {market_ticker}).")
                        _active_market_cache["ticker"] = next_ticker
                        _active_market_cache["close_time"] = next_close_time
                        check_market_and_trade(next_ticker)
                    else:
                        # Nothing else open right now - stay on the original
                        # ticker rather than stall with nothing active.
                        print(f"[{local_time_str}] [EARLY RESOLVE] No other open ticker available - staying on {market_ticker}.")
                        _active_market_cache["ticker"] = market_ticker
                        _active_market_cache["close_time"] = _get_cached_close_time(market_ticker)
            else:
                local_time_str = time.strftime('%I:%M:%S %p')
                log_smart(("lookup",), f"[{local_time_str}] Looking up active market for event {event_ticker}...", sig=0, interval=10)

            time.sleep(0.5)
            
    except KeyboardInterrupt:
        final_pnl = get_session_pnl()
        pnl_display = f"${final_pnl:.2f}" if final_pnl is not None else f"${session_realized_pnl:.2f} (internal tracker - balance check failed)"
        print(f"\nBot shut down safely. Final session P/L: {pnl_display}")