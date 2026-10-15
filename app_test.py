# ============================================================
#  នំប៉ាវហុងកុង Supply Chain Hub  -  v3: fast, secure, self-healing
#  Run with:  py watchdog_bot.py      (or:  py -m streamlit run app.py)
# ============================================================
import streamlit as st
import pandas as pd
import os
import io
import re
import csv
import glob
import time
import pickle
import shutil
import hmac
import difflib
import tempfile
import warnings
import traceback
import threading
import contextlib
import secrets as pysecrets
import fnmatch
import json
import html
import unicodedata
import hashlib
from collections import Counter
from datetime import datetime, date, timedelta, timezone
from zoneinfo import ZoneInfo

if not hasattr(st, "fragment"):            # very old Streamlit: run everything normally
    def _fragment_shim(func=None, **kwargs):
        return func if func is not None else (lambda f: f)
    st.fragment = _fragment_shim

warnings.filterwarnings("ignore", category=UserWarning, module="openpyxl")
warnings.filterwarnings("ignore", message=".*Could not infer format.*")
warnings.filterwarnings("ignore", message=".*Parsing dates.*")

# ==========================================
# WHERE THE DATA LIVES
#   * Dropbox mode (online): used when DROPBOX_REFRESH_TOKEN (or DROPBOX_ACCESS_TOKEN) exists in the
#     app Secrets. The journal and all CSV files are read from / saved to your Dropbox folder, so
#     nothing is lost when the online host restarts.
#   * Local mode (your PC): plain files next to app.py.
# ==========================================
def _secret(name):
    try:
        v = st.secrets[name]
        return str(v).strip() if v else ""
    except Exception:
        return os.environ.get(name, "").strip()


USE_DROPBOX = bool(_secret("DROPBOX_REFRESH_TOKEN") or _secret("DROPBOX_ACCESS_TOKEN"))
DROPBOX_FOLDER = "/" + (_secret("DROPBOX_FOLDER") or "/dropbox/4- Sale Jounal").strip().strip("/")

# ==========================================
# CONFIGURATION
# ==========================================
CURRENT_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(tempfile.gettempdir(), "hk_supply_hub_data") if USE_DROPBOX else CURRENT_DIR
os.makedirs(DATA_DIR, exist_ok=True)
DATA_FILE = os.path.join(DATA_DIR, "daily_delivery_expenses.csv")
PACKING_FILE = os.path.join(DATA_DIR, "daily_packing_progress.csv")
BACKUP_DIR = os.path.join(CURRENT_DIR, "backups")                 # local mode only (Dropbox mode: <folder>/backups)
BOT_LOG_FILE = os.path.join(DATA_DIR, "bot_log.csv")
AUDIT_FILE = os.path.join(DATA_DIR, "audit_log.csv")
USERS_FILE = os.path.join(DATA_DIR, "users.json")          # accounts (passwords are stored hashed, never as text)
ASSIGN_FILE = os.path.join(DATA_DIR, "delivery_assignments.csv")   # who will deliver which customer today
LOCATIONS_FILE = os.path.join(DATA_DIR, "customer_locations.csv")   # provinces that the admin set by hand
LOG_PUSH_DELAY = 10                                                # seconds before logs are copied to Dropbox
CACHE_DIR = os.path.join(tempfile.gettempdir(), "hk_supply_hub_cache")       # outside Dropbox = faster

# Excel journal. The bot tries EXCEL_PATTERN first; if nothing matches it switches to
# EXCEL_FALLBACK_PATTERN by itself. To force one exact file: EXCEL_OVERRIDE = "name.xlsx"
EXCEL_PATTERN = "*conflicted copy*.xlsx"
EXCEL_FALLBACK_PATTERN = "*Sale_Journal*.xlsx"
EXCEL_OVERRIDE = ""

SHEET_NAME = "Master List"
JOURNAL_SHEET = "DAILY SALE JOUNAL"
COLUMN_NAME = "Customer Name"
JOURNAL_HEADER_TEXT = "ឈ្មោះអតិថិជន"
JOURNAL_CASES_HEADER = "កេស"           # journal column: cases ordered
JOURNAL_INVOICE_HEADER = "វិក្កយប័ត្រ"   # journal column: invoice number
JOURNAL_REMARK_HEADER = "ចំណាំ"          # journal column: remark / note
INVOICE_PREFIX = "NP"                  # if the invoice column is empty, the first cell starting with this is used
URGENT_WORDS = ["ប្រញាប់", "URGENT"]    # a remark containing one of these gets a 🔥
SNAPSHOT_VERSION = 4                   # change this number to force the journal to be re-read

TZ = ZoneInfo("Asia/Phnom_Penh")
DAYFIRST = True                        # only used for ambiguous TEXT dates with no other hint

BOT_INTERVAL_MIN = 30                  # the bot checks everything by itself every 30 minutes
LIVE_REFRESH_SECONDS = 20              # dashboard "Live" refresh

# --- security ---
LOGIN_TTL_HOURS = 12                   # automatic log-out after this many hours
MAX_FAILS = 5                          # wrong codes before a temporary lock-out
LOCKOUT_MIN = 5                        # lock-out length (minutes)
MAX_CASES = 10000
MAX_RIEL = 50_000_000
MAX_TEXT = 200

LOCAL_DRIVERS = ["ងិន វុទ្ធា", "អួន តួ"]
OPS_STAFF = ["ឆែម សំណុក", "សាយ ប៊ុនលី", "ប៉ៅ រីណា", "ពេជ រដ្ឋា", "រ៉ូ សុវណ្ណាឌែន", "ហេង រតនា", "កង សៀន", "ណាត ផានិត"]

DISPATCH_COLS = ["Date", "Handled_By", "Customer", "Cases", "Local_Driver",
                 "Taxi_Station", "Phnom_Penh_Expense", "Taxi_Expense", "Note", "Verified_By", "Expense_Status"]
DISPATCH_NUM_COLS = ["Cases", "Phnom_Penh_Expense", "Taxi_Expense"]
PACKING_COLS = ["Date", "Prepared_By", "Customer", "Cases_Packed", "Status"]
ASSIGN_COLS = ["Date", "Handler", "Customer", "Action"]
PACKING_NUM_COLS = ["Cases_Packed"]
NUM_COLS_ALL = set(DISPATCH_NUM_COLS + PACKING_NUM_COLS)
FILES = {
    "dispatch": (DATA_FILE, DISPATCH_COLS, DISPATCH_NUM_COLS, "Dispatch CSV"),
    "packing": (PACKING_FILE, PACKING_COLS, PACKING_NUM_COLS, "Packing CSV"),
    "assign": (ASSIGN_FILE, ASSIGN_COLS, [], "Assignments CSV"),
}

STATUS_RANK = {"✅ Sent": 1, "🔵 Partial": 2, "🟡 Ready for Delivery": 3, "🟠 Packing": 4, "⏳ Pending": 5}
ROLE_LABEL = {"admin": "Admin", "staff": "Staff", "viewer": "Viewer (read-only)"}


# ==========================================
# TIME HELPERS
# ==========================================
def now_kh():
    return datetime.now(TZ)


def today_kh():
    return now_kh().date()


def now_str():
    return now_kh().strftime("%Y-%m-%d %H:%M:%S")


# ==========================================
# DATE PARSING (never guesses blindly, never loses rows)
# ==========================================
def _try_parse(s, dayfirst):
    try:
        t = pd.to_datetime(s, dayfirst=dayfirst, errors="coerce")
        return None if pd.isna(t) else pd.Timestamp(t)
    except Exception:
        return None


def parse_dt(v):
    """One CSV date value. ISO is read as written; ambiguous text dates (10/12/2026)
    pick the reading that is closest to today."""
    if isinstance(v, (datetime, pd.Timestamp)):
        return pd.Timestamp(v)
    s = str(v).strip()
    if not s or s.lower() in ("nan", "nat", "-", "none"):
        return pd.NaT
    if re.match(r"^\d{4}[-/]\d{1,2}[-/]\d{1,2}", s):
        t = _try_parse(s, False)
        return pd.NaT if t is None else t
    us, eu = _try_parse(s, False), _try_parse(s, True)
    if us is None and eu is None:
        return pd.NaT
    if us is None:
        return eu
    if eu is None or us == eu:
        return us
    today = pd.Timestamp(today_kh())
    return us if abs((us - today).days) <= abs((eu - today).days) else eu


def parse_dates(series):
    """Fast path for ISO rows, slow path only for the odd hand-typed ones."""
    s = series.astype(str).str.strip()
    out = pd.to_datetime(s, format="%Y-%m-%d %H:%M:%S", errors="coerce")
    bad = out.isna()
    if bad.any():
        out.loc[bad] = pd.to_datetime(s[bad].map(parse_dt), errors="coerce")
    return out


def cell_to_date(v, dominant=None):
    """One Excel journal cell -> date (or None). `dominant` = (year, month) most journal dates use."""
    if v is None:
        return None
    if isinstance(v, (datetime, pd.Timestamp)):
        return v.date()
    if isinstance(v, date):
        return v
    s = str(v).strip()
    if not s:
        return None
    if re.match(r"^\d{4}[-/]\d{1,2}[-/]\d{1,2}", s):
        t = _try_parse(s, False)
        return None if t is None else t.date()
    us, eu = _try_parse(s, False), _try_parse(s, True)
    if us is None and eu is None:
        return None
    if us is None:
        return eu.date()
    if eu is None or us == eu:
        return us.date()
    if dominant:
        if (us.year, us.month) == dominant:
            return us.date()
        if (eu.year, eu.month) == dominant:
            return eu.date()
    return (eu if DAYFIRST else us).date()


def norm_name(s):
    return re.sub(r"\s+", " ", str(s)).strip().casefold()


# ==========================================
# LOCATIONS: Phnom Penh / Province, province names, delivery regions, map coordinates
# ==========================================
PP = "Phnom Penh"
AREA_LABEL = {PP: "🏙️ Phnom Penh", "Province": "🌄 Province", "Unknown": "❓ Unknown"}
AREA_RANK = {"🏙️ Phnom Penh": 1, "🌄 Province": 2, "❓ Unknown": 3}

# region name -> (map colour, legend emoji). Regions follow the national roads out of Phnom Penh.
REGIONS = {
    "Phnom Penh":          ("#E63946", "🟥"),
    "Near Phnom Penh":     ("#F4A261", "🟧"),
    "East (NR1)":          ("#E9C46A", "🟨"),
    "South (NR2/3)":       ("#2A9D8F", "🟩"),
    "Southwest (NR4)":     ("#457B9D", "🟦"),
    "Northwest (NR5)":     ("#8E5CC4", "🟪"),
    "North (NR6)":         ("#8D6E63", "🟫"),
    "Northeast (NR7)":     ("#2B2D42", "⬛"),
    "Unassigned":          ("#9E9E9E", "⬜"),
}

# English name: (latitude, longitude, region, [Khmer names])   - map points are the provincial towns
PROVINCES = {
    "Phnom Penh":       (11.5564, 104.9282, "Phnom Penh",      ["ភ្នំពេញ"]),
    "Kandal":           (11.4833, 104.9500, "Near Phnom Penh", ["កណ្តាល"]),
    "Prey Veng":        (11.4868, 105.3253, "East (NR1)",      ["ព្រៃវែង"]),
    "Svay Rieng":       (11.0878, 105.7993, "East (NR1)",      ["ស្វាយរៀង"]),
    "Takeo":            (10.9908, 104.7850, "South (NR2/3)",   ["តាកែវ"]),
    "Kampot":           (10.6104, 104.1815, "South (NR2/3)",   ["កំពត"]),
    "Kep":              (10.4829, 104.3167, "South (NR2/3)",   ["កែប"]),
    "Kampong Speu":     (11.4533, 104.5208, "Southwest (NR4)", ["កំពង់ស្ពឺ"]),
    "Preah Sihanouk":   (10.6275, 103.5222, "Southwest (NR4)", ["ព្រះសីហនុ", "សីហនុវិល"]),
    "Koh Kong":         (11.6153, 102.9838, "Southwest (NR4)", ["កោះកុង"]),
    "Kampong Chhnang":  (12.2500, 104.6667, "Northwest (NR5)", ["កំពង់ឆ្នាំង"]),
    "Pursat":           (12.5388, 103.9192, "Northwest (NR5)", ["ពោធិសាត់"]),
    "Battambang":       (13.0957, 103.2022, "Northwest (NR5)", ["បាត់ដំបង"]),
    "Banteay Meanchey": (13.5859, 102.9737, "Northwest (NR5)", ["បន្ទាយមានជ័យ"]),
    "Pailin":           (12.8489, 102.6093, "Northwest (NR5)", ["ប៉ៃលិន"]),
    "Kampong Thom":     (12.7111, 104.8887, "North (NR6)",     ["កំពង់ធំ"]),
    "Siem Reap":        (13.3633, 103.8564, "North (NR6)",     ["សៀមរាប"]),
    "Preah Vihear":     (13.8070, 104.9800, "North (NR6)",     ["ព្រះវិហារ"]),
    "Oddar Meanchey":   (14.1810, 103.5174, "North (NR6)",     ["ឧត្តរមានជ័យ"]),
    "Kampong Cham":     (11.9934, 105.4635, "Northeast (NR7)", ["កំពង់ចាម"]),
    "Tbong Khmum":      (11.8892, 105.6561, "Northeast (NR7)", ["ត្បូងឃ្មុំ"]),
    "Kratie":           (12.4881, 106.0188, "Northeast (NR7)", ["ក្រចេះ"]),
    "Stung Treng":      (13.5259, 105.9683, "Northeast (NR7)", ["ស្ទឹងត្រែង"]),
    "Ratanakiri":       (13.7394, 106.9873, "Northeast (NR7)", ["រតនគិរី"]),
    "Mondulkiri":       (12.4558, 107.1881, "Northeast (NR7)", ["មណ្ឌលគិរី"]),
}

# Well-known towns / districts / markets -> province (used when the customer name has no province name)
PLACES = {
    "Banteay Meanchey": ["ប៉ោយប៉ែត", "បោយប៉ែត", "ផ្សារបែកចាន", "សិរីសោភ័ណ", "ស្វាយចេក", "មង្គលបូរី"],
    "Koh Kong": ["ស្រែអំបិល", "ថ្មបាំង", "ជីផាត"],
    "Pursat": ["ក្រគរ", "បាកាន", "អូរសោម", "វាលវែង", "កណ្តៀង", "ភ្នំក្រវាញ"],
    "Ratanakiri": ["បរកែវ", "បានលុង", "ឡុមផាត់"],
    "Kampong Cham": ["ស្តឹងត្រង់", "ស្ទឹងត្រង់", "ព្រៃឈរ", "ចំការលើ", "ជើងព្រៃ", "កងមាស", "បាធាយ", "ស្រីសន្ធរ", "កំពង់សៀម"],
    "Tbong Khmum": ["មេមត់", "ពញាក្រែក", "ក្រូចឆ្មារ", "អូររាំងឪ", "តំបែរ"],
    "Prey Veng": ["អ្នកលឿង", "កំពង់ត្របែក", "ពាមរ", "បាភ្នំ", "កំចាយមារ", "ពារាំង", "មេសាង", "ស៊ីធរកណ្តាល"],
    "Kandal": ["តាខ្មៅ", "ស្អាង", "កោះធំ", "ល្វាឯម", "មុខកំពូល", "កៀនស្វាយ", "ពញាឮ", "លើកដែក"],
    "Svay Rieng": ["រមាសហែក", "បាវិត", "ស្វាយទាប", "ចន្ទ្រា", "កំពង់រោទ៍", "រំដួល"],
    "Preah Sihanouk": ["កំពង់សិលា", "ស្ទឹងហាវ", "កំពង់សោម", "ព្រៃនប់"],
    "Takeo": ["អង្គតាសោម", "អង្គរតាសោម", "ត្រាំកក់", "បាទី", "គីរីវង់", "កោះអណ្តែត", "បូរីជលសារ", "ព្រៃកប្បាស", "ដូនកែវ"],
    "Kampot": ["ផ្សារឈូក", "កំពង់ត្រាច", "ទឹកឈូ", "ទូកមាស", "អង្គរជ័យ", "ជុំគិរី"],
    "Kampong Thom": ["សន្ទុក", "ស្ទោង", "បារាយណ៍", "កំពង់ស្វាយ", "ស្ទឹងសែន", "តាំងគោក"],
    "Kratie": ["ឆ្លូង", "ស្នួល", "ព្រែកប្រា"],
    "Battambang": ["បវេល", "មោងឫស្សី", "ឯកភ្នំ", "ថ្មគោល", "សំពៅលូន", "រតនមណ្ឌល", "កំរៀង", "បានន់", "សំឡូត"],
    "Siem Reap": ["បន្ទាយស្រី", "ស្វាយលើ", "សូទ្រនិគម", "ជីក្រែង", "បាគង", "អង្គរធំ"],
    "Kampong Speu": ["ឧដុង្គ", "សំរោងទង", "ភ្នំស្រួច", "ឱរ៉ាល់", "ច្បារមន", "បរសេដ្ឋ", "គងពិសី", "ថ្ពង"],
    "Kampong Chhnang": ["រលាប្អៀរ", "សាមគ្គីមានជ័យ", "ទឹកផុស", "កំពង់ត្រឡាច", "ជលគិរី"],
    "Mondulkiri": ["សែនមនោរម្យ"],
    "Preah Vihear": ["ត្បែងមានជ័យ"],
    "Oddar Meanchey": ["អូរស្មាច់", "អន្លង់វែង", "ចុងកាល់"],
    "Phnom Penh": ["ជ្រោយចង្វារ", "ចំការមន", "ដូនពេញ", "ទួលគោក", "ដង្កោ", "ឬស្សីកែវ", "សែនសុខ", "ពោធិសែនជ័យ",
                   "ច្បារអំពៅ", "បឹងកេងកង", "ព្រែកព្នៅ", "កំបូល", "៧មករា", "ចោមចៅ"],
}


def _kh(text):
    """Makes Khmer spellings comparable (different encodings of the same word)."""
    t = unicodedata.normalize("NFC", str(text))
    for ch in ("\u200b", "\u200c", "\u200d", "៍"):
        t = t.replace(ch, "")
    return t.replace("្ដ", "្ត")


def _build_matchers():
    pats = []
    for prov, (_, _, _, names) in PROVINCES.items():
        for kw in names:
            k = re.escape(_kh(kw))
            if prov == "Kandal":
                k = "(?<!ផ្សារ)" + k                       # "ផ្សារកណ្តាល" = central market, not Kandal
            elif prov == "Preah Sihanouk":
                k = "(?<!មហាវិថី)(?<!មហាវិថី )" + k       # "Preah Sihanouk Blvd" is a Phnom Penh street
            pats.append((prov, re.compile(k), "province name"))
    for prov, names in PLACES.items():
        for kw in names:
            pats.append((prov, re.compile(re.escape(_kh(kw))), "town name"))
    return pats


_MATCHERS = _build_matchers()


def detect_province(name, allow_pp=True):
    """(province, how) read from the customer name. The match that ends last wins (the place is usually written last)."""
    t = _kh(re.sub(r"\s+", " ", str(name)))
    best = None
    for prov, rx, kind in _MATCHERS:
        if prov == PP and not allow_pp:
            continue
        for m in rx.finditer(t):
            key = (m.end(), m.end() - m.start())
            if best is None or key > best[0]:
                best = (key, prov, kind)
    return (best[1], best[2]) if best else (None, None)


def region_of(province):
    return PROVINCES[province][2] if province in PROVINCES else "Unassigned"


def resolve_location(name, area_master, override=None):
    """-> (area, province, region, how). area_master: 'Phnom Penh' | 'Province' | 'Unknown' | None (not in Master List)."""
    if override in PROVINCES:
        return (PP if override == PP else "Province"), override, region_of(override), "set by admin"
    if area_master == PP:
        return PP, PP, region_of(PP), "master list"
    if area_master == "Province":
        prov, how = detect_province(name, allow_pp=False)
        if prov:
            return "Province", prov, region_of(prov), how
        return "Province", "Unknown province", "Unassigned", "unknown"
    prov, how = detect_province(name, allow_pp=True)
    if prov:
        return (PP if prov == PP else "Province"), prov, region_of(prov), how + (" (not in Master List)" if area_master is None else "")
    return "Unknown", "Unknown", "Unassigned", "unknown"


def _read_loc_df():
    try:
        return pd.read_csv(LOCATIONS_FILE, dtype=str, keep_default_na=False, encoding="utf-8-sig")
    except Exception:
        return pd.DataFrame(columns=["Customer", "Province"])


def load_location_overrides():
    """{normalised customer name: province} typed in by the admin."""
    if USE_DROPBOX:
        try:
            pull(LOCATIONS_FILE)
        except Exception:
            pass
    df = _read_loc_df()
    out = {}
    if {"Customer", "Province"} <= set(df.columns):
        for c, p in zip(df["Customer"], df["Province"]):
            if norm_name(c) and str(p).strip() in PROVINCES:
                out[norm_name(c)] = str(p).strip()
    return out


def modify_locations(fn):
    """Safe read-change-save of the manual locations. fn({customer: province}) returns the new dict."""
    last = None
    for attempt in range(6):
        try:
            with _sync_state()["lock"]:
                if USE_DROPBOX:
                    pull(LOCATIONS_FILE, force=True)
                df = _read_loc_df()
                cur = {}
                if {"Customer", "Province"} <= set(df.columns):
                    cur = {str(c).strip(): str(p).strip() for c, p in zip(df["Customer"], df["Province"]) if str(c).strip()}
                new = fn(cur)
                out = pd.DataFrame(sorted(new.items()), columns=["Customer", "Province"])
                tmp = LOCATIONS_FILE + ".tmp"
                with file_lock(LOCATIONS_FILE):
                    out.to_csv(tmp, index=False, encoding="utf-8-sig")
                    os.replace(tmp, LOCATIONS_FILE)
                if USE_DROPBOX:
                    push(LOCATIONS_FILE)
            return
        except ConflictError as e:
            last = e
            time.sleep(0.2 * (attempt + 1))
    raise RuntimeError("Dropbox is busy - please try again") from last


def areas_lookup(snap):
    """{normalised customer name: area} from the Master List."""
    if not snap:
        return {}
    return {norm_name(n): a for n, a in snap.get("areas", {}).items()}


# ==========================================
# SECURITY: input cleaning, access codes, login, audit log
# ==========================================
_CTRL = re.compile(r"[\x00-\x08\x0b-\x1f\x7f]")
_PHONE = re.compile(r"[+\-]?[\d\s().\-]+")


def safe_text(v, maxlen=MAX_TEXT):
    """Removes control characters, cuts the length and blocks Excel formula injection (=, @, +cmd, -cmd)."""
    s = _CTRL.sub(" ", str(v)).replace("\r", " ").replace("\n", " ").strip()[:maxlen]
    if s and (s[0] in "=@" or (s[0] in "+-" and not _PHONE.fullmatch(s))):
        s = "'" + s
    return s


def _append_log(path, cols, row, max_bytes=300_000, keep=300):
    try:
        if USE_DROPBOX:
            _log_pull_once(path)
        new = (not os.path.exists(path)) or os.path.getsize(path) == 0
        with open(path, "a", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            if new:
                w.writerow(cols)
            w.writerow(row)
        if os.path.getsize(path) > max_bytes:
            with open(path, "r", encoding="utf-8-sig") as f:
                lines = f.readlines()
            with open(path, "w", encoding="utf-8-sig", newline="") as f:
                f.writelines([lines[0]] + lines[-keep:])
        if USE_DROPBOX:
            _schedule_log_push(path)
    except Exception:
        pass


BOT_LOG_COLS = ["Time", "Level", "Check", "Message", "Action"]
AUDIT_COLS = ["Time", "User", "Client", "Event", "Detail"]


def bot_log(level, check, message, action="-"):
    _append_log(BOT_LOG_FILE, BOT_LOG_COLS, [now_str(), level, check, message, action])


def client_id():
    try:
        h = st.context.headers
        xff = h.get("X-Forwarded-For") or h.get("x-forwarded-for")
        if xff:
            return str(xff).split(",")[0].strip()[:45]
        ip = getattr(st.context, "ip_address", None)
        if ip:
            return str(ip)[:45]
    except Exception:
        pass
    return "local"


def current_role():
    return st.session_state.get("role")


def current_user():
    return st.session_state.get("user")


def audit(event, detail=""):
    who = f"{current_user() or '-'}/{current_role() or '-'}"
    _append_log(AUDIT_FILE, AUDIT_COLS, [now_str(), who, client_id(), event, safe_text(detail, 200)],
                keep=2000, max_bytes=800_000)


# ---------- accounts (users.json) ----------
PBKDF2_ITER = 200_000
DEFAULT_ADMIN_USER = "admin"
DEFAULT_ADMIN_PW = "Hk-Admin-7Q4mW2"          # starter password: the app forces a change at the first login
USERNAME_RE = re.compile(r"^[a-z0-9._-]{3,30}$")
COMMON_PW = {"password", "password1", "12345678", "123456789", "qwerty123", "admin123", "hk2026", "staff2026",
             "hk-admin-7q4mw2", "hk-staff-3rn8zp", "change-me-admin-9x", "11111111", "abcd1234"}
ROLES = ["staff", "viewer", "admin"]


def _hash_pw(password, salt=None, iters=PBKDF2_ITER):
    salt = salt or os.urandom(16)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, iters)
    return {"salt": salt.hex(), "hash": dk.hex(), "iter": iters}


def _check_pw(password, rec):
    try:
        dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), bytes.fromhex(rec["salt"]), int(rec["iter"]))
        return hmac.compare_digest(dk.hex(), rec["hash"])
    except Exception:
        return False


@st.cache_resource(show_spinner=False)
def _dummy_rec():
    return _hash_pw("not-a-real-password")           # makes unknown usernames take the same time as real ones


def password_problem(new, username=""):
    if len(new) < 8:
        return "Use at least 8 characters."
    if len(new) > 100:
        return "That password is too long (max 100)."
    if new.lower() in COMMON_PW or new.lower() == (username or "").lower():
        return "That password is too easy to guess. Choose another one."
    if not (any(c.isalpha() for c in new) and any(c.isdigit() for c in new)):
        return "Use letters AND numbers."
    return None


def generate_password():
    alphabet = "ABCDEFGHJKMNPQRSTUVWXYZabcdefghjkmnpqrstuvwxyz23456789"
    while True:
        pw = "".join(pysecrets.choice(alphabet) for _ in range(10))
        if any(c.isdigit() for c in pw) and any(c.isalpha() for c in pw):
            return pw


def _new_user(role, password, must_change):
    return {"role": role, "active": True, "must_change": bool(must_change), "created": now_str(),
            "last_login": "", **_hash_pw(password)}


def _default_users():
    pw = _secret("INITIAL_ADMIN_PASSWORD") or DEFAULT_ADMIN_PW
    return {DEFAULT_ADMIN_USER: _new_user("admin", pw, must_change=True)}


def _read_users_file():
    try:
        with open(USERS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        users = data.get("users") if isinstance(data, dict) else None
        return users if isinstance(users, dict) and users else None
    except (OSError, ValueError):
        return None


def save_users(users):
    tmp = USERS_FILE + ".tmp"

    def _do():
        with file_lock(USERS_FILE):
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump({"users": users}, f, ensure_ascii=False, indent=1)
            os.replace(tmp, USERS_FILE)
    _retry(_do)
    if USE_DROPBOX:
        push(USERS_FILE)


def load_users():
    """All accounts. On the very first start the starter admin account is created."""
    if USE_DROPBOX:
        try:
            pull(USERS_FILE)
        except Exception:
            if not os.path.exists(USERS_FILE):
                raise RuntimeError("Cannot reach Dropbox to load the accounts. Please try again in a minute.")
    users = _read_users_file()
    if users:
        return users
    for _ in range(3):
        try:
            if USE_DROPBOX:
                pull(USERS_FILE, force=True)
            users = _read_users_file()
            if users:
                return users
            users = _default_users()
            save_users(users)
            bot_log("info", "Security", "First start: created the starter admin account", "created")
            return users
        except ConflictError:
            continue
    raise RuntimeError("Could not create the first account. Reload the page.")


def modify_users(fn):
    """Safe read-change-save of the accounts. fn(users) returns the new dict (or raises ValueError)."""
    last = None
    for attempt in range(6):
        try:
            with _sync_state()["lock"]:
                if USE_DROPBOX:
                    pull(USERS_FILE, force=True)
                users = _read_users_file() or _default_users()
                save_users(fn(users))
            return
        except ConflictError as e:
            last = e
            time.sleep(0.2 * (attempt + 1))
    raise RuntimeError("Dropbox is busy - please try again") from last


@st.cache_resource(show_spinner=False)
def _login_guard():
    return {"fails": {}, "locked": {}, "lock": threading.Lock()}


def _clear_session():
    for k in ("role", "user", "login_time", "must_change", "sel_cust"):
        st.session_state.pop(k, None)


def logout(reason="manual"):
    audit("logout", reason)
    _clear_session()


def session_ok():
    """True when the person is logged in and the account is still valid."""
    user, role = st.session_state.get("user"), st.session_state.get("role")
    if not user or not role:
        return False
    if time.time() - st.session_state.get("login_time", 0) >= LOGIN_TTL_HOURS * 3600:
        logout("session expired")
        return False
    try:
        rec = load_users().get(user)
    except Exception:
        return True                                        # storage hiccup: keep working people logged in
    if not rec or not rec.get("active", True) or rec.get("role") != role:
        logout("account removed or changed")
        return False
    st.session_state["must_change"] = bool(rec.get("must_change"))
    return True


def _try_login(username, password):
    guard, cid, now = _login_guard(), client_id(), time.time()
    uname = re.sub(r"\s+", "", username or "").lower()[:40]
    keys = [cid, "u:" + uname]
    with guard["lock"]:
        locked_until = max(guard["locked"].get(k, 0) for k in keys)
    if locked_until > now:
        st.error(f"Too many wrong attempts. Please wait {int((locked_until - now) // 60) + 1} minute(s) and try again.")
        audit("login_blocked", f"user={uname}")
        return
    try:
        users = load_users()
    except Exception as e:
        st.error(f"⚠️ {e}")
        return
    rec = users.get(uname)
    good = _check_pw(password or "", rec if rec else _dummy_rec())
    if rec and good and rec.get("active", True):
        with guard["lock"]:
            for k in keys:
                guard["fails"].pop(k, None)
        st.session_state.update({"user": uname, "role": rec["role"], "login_time": time.time(),
                                 "must_change": bool(rec.get("must_change"))})
        audit("login", rec["role"])

        def _stamp(u):
            if uname in u:
                u[uname]["last_login"] = now_str()
            return u
        try:
            modify_users(_stamp)
        except Exception:
            pass
        st.rerun()
    with guard["lock"]:
        for k in keys:
            guard["fails"][k] = guard["fails"].get(k, 0) + 1
            limit = MAX_FAILS if k == cid else MAX_FAILS * 2
            if guard["fails"][k] >= limit:
                guard["locked"][k] = time.time() + LOCKOUT_MIN * 60
                guard["fails"][k] = 0
    audit("login_failed", f"user={uname}")
    time.sleep(1)                                          # slows down guessing
    st.error("❌ Wrong username or password.")


def change_password(user, current, new, new2):
    """Returns an error text, or None when the password was changed."""
    if new != new2:
        return "The two new passwords are not the same."
    problem = password_problem(new, user)
    if problem:
        return problem

    def _fn(users):
        rec = users.get(user)
        if not rec or not _check_pw(current or "", rec):
            raise ValueError("The current password is wrong.")
        if _check_pw(new, rec):
            raise ValueError("Choose a password that is different from the current one.")
        rec.update(_hash_pw(new))
        rec["must_change"] = False
        rec["pw_changed"] = now_str()
        return users
    try:
        modify_users(_fn)
    except ValueError as e:
        return str(e)
    except Exception as e:
        return f"Could not save the new password: {e}"
    audit("password_changed", "own password")
    return None


def render_login():
    st.markdown("<div style='height:8vh'></div>", unsafe_allow_html=True)
    _, mid, _ = st.columns([1, 2, 1])
    with mid:
        st.markdown("## 🔐 នំប៉ាវហុងកុង Hub")
        st.caption("Enter your username and password to continue.")
        with st.form("login_form"):
            u = st.text_input("Username", max_chars=40)
            p = st.text_input("Password", type="password", max_chars=100)
            go = st.form_submit_button("Log in", type="primary")
        if go:
            _try_login(u, p)


def render_force_change():
    user = current_user()
    st.markdown("<div style='height:6vh'></div>", unsafe_allow_html=True)
    _, mid, _ = st.columns([1, 2, 1])
    with mid:
        st.markdown("## 🔑 Choose your own password")
        st.caption(f"Hello {user}. For safety you must replace your starter password before you continue. "
                   "Use at least 8 characters with letters and numbers.")
        with st.form("force_pw_form"):
            cur = st.text_input("Starter password (the one you just used)", type="password", max_chars=100)
            n1 = st.text_input("New password", type="password", max_chars=100)
            n2 = st.text_input("New password again", type="password", max_chars=100)
            go = st.form_submit_button("Save new password", type="primary")
        if go:
            err = change_password(user, cur, n1, n2)
            if err:
                st.error(f"❌ {err}")
            else:
                st.session_state["must_change"] = False
                st.session_state["flash"] = "Password changed. Welcome!"
                st.rerun()
        if st.button("🚪 Log out", key="force_logout"):
            logout("manual")
            st.rerun()


def require_login():
    """Shows the login page (and stops the app) until the person is logged in. Returns the role."""
    if session_ok():
        if st.session_state.get("must_change"):
            render_force_change()
            st.stop()
        return st.session_state["role"]
    render_login()
    st.stop()


def failed_logins(hours=24):
    try:
        if USE_DROPBOX:
            _log_pull_once(AUDIT_FILE)
        if not os.path.exists(AUDIT_FILE):
            return 0
        df = pd.read_csv(AUDIT_FILE, encoding="utf-8-sig", dtype=str, keep_default_na=False)
        t = pd.to_datetime(df["Time"], errors="coerce")
        cutoff = now_kh().replace(tzinfo=None) - timedelta(hours=hours)
        return int(((df["Event"] == "login_failed") & (t >= cutoff)).sum())
    except Exception:
        return 0


# ==========================================
# SAFE FILE HELPERS (lock, atomic write, backup)
# ==========================================
@contextlib.contextmanager
def file_lock(path, timeout=6.0):
    lock, fd, start = path + ".lock", None, time.time()
    while True:
        try:
            fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            break
        except FileExistsError:
            try:
                if time.time() - os.path.getmtime(lock) > 15:     # stale lock -> remove
                    os.remove(lock)
                    continue
            except OSError:
                pass
            if time.time() - start > timeout:                     # never block the staff
                break
            time.sleep(0.05)
        except OSError:
            break
    try:
        yield
    finally:
        if fd is not None:
            try:
                os.close(fd)
                os.remove(lock)
            except OSError:
                pass


def _retry(fn, tries=6, delay=0.4):
    """Retry when Excel / Dropbox is holding the file for a moment."""
    last = None
    for _ in range(tries):
        try:
            return fn()
        except PermissionError as e:
            last = e
            time.sleep(delay)
    raise PermissionError("The file is open in another program (Excel?). Close it and try again.") from last


# ==========================================
# DROPBOX LAYER  (only active in Dropbox mode)
# ==========================================
class ConflictError(Exception):
    """Somebody else changed the Dropbox file while we were saving."""


@st.cache_resource(show_spinner=False)
def _sync_state():
    return {"lock": threading.RLock(), "rev": {}, "last_pull": {}, "xl_hash": {},
            "log_pulled": set(), "timers": {}}


@st.cache_resource(show_spinner=False)
def _dbx():
    import dropbox
    refresh = _secret("DROPBOX_REFRESH_TOKEN")
    if refresh:
        return dropbox.Dropbox(oauth2_refresh_token=refresh, app_key=_secret("DROPBOX_APP_KEY"),
                               app_secret=_secret("DROPBOX_APP_SECRET"), timeout=30)
    return dropbox.Dropbox(oauth2_access_token=_secret("DROPBOX_ACCESS_TOKEN"), timeout=30)


def _rpath(name):
    return f"{DROPBOX_FOLDER}/{name}"


def _remote_backup_dir():
    return f"{DROPBOX_FOLDER}/backups"


def _is_not_found(e):
    return "not_found" in str(e).lower()


def _is_conflict(e):
    return "conflict" in str(e).lower()


def where_text():
    return f"Dropbox folder {DROPBOX_FOLDER}" if USE_DROPBOX else CURRENT_DIR


def remote_meta(name):
    """Dropbox file info (None if the file does not exist)."""
    try:
        md = _dbx().files_get_metadata(_rpath(name))
    except Exception as e:
        if _is_not_found(e):
            return None
        raise
    return md if hasattr(md, "rev") else None


def _write_atomic(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".dl"
    with open(tmp, "wb") as f:
        f.write(data)
    os.replace(tmp, path)


def pull(path, force=False, max_age=5.0):
    """Makes the local working copy equal to Dropbox (cheap: only downloads when the file changed)."""
    if not USE_DROPBOX:
        return
    S, name = _sync_state(), os.path.basename(path)
    with S["lock"]:
        if not force and time.time() - S["last_pull"].get(path, 0) < max_age:
            return
        md = remote_meta(name)
        S["last_pull"][path] = time.time()
        if md is None:
            S["rev"].pop(path, None)
            return
        if S["rev"].get(path) == md.rev and os.path.exists(path):
            return
        _, res = _dbx().files_download(_rpath(name))
        _write_atomic(path, res.content)
        S["rev"][path] = md.rev


def push(path):
    """Uploads the local working copy. Fails with ConflictError if Dropbox changed in the meantime."""
    if not USE_DROPBOX:
        return
    import dropbox
    S, name = _sync_state(), os.path.basename(path)
    with S["lock"]:
        with open(path, "rb") as f:
            data = f.read()
        rev = S["rev"].get(path)
        mode = dropbox.files.WriteMode.update(rev) if rev else dropbox.files.WriteMode.add
        try:
            md = _dbx().files_upload(data, _rpath(name), mode=mode, autorename=False, mute=True)
        except Exception as e:
            S["rev"].pop(path, None)                 # next pull will download a fresh copy
            S["last_pull"].pop(path, None)
            if _is_conflict(e):
                raise ConflictError(f"{name} was changed by someone else") from e
            raise
        S["rev"][path] = md.rev
        S["last_pull"][path] = time.time()


def _log_pull_once(path):
    """Logs (bot/audit) are kept locally and copied to Dropbox a few seconds after each entry."""
    S = _sync_state()
    with S["lock"]:
        if path in S["log_pulled"]:
            return
        S["log_pulled"].add(path)
    try:
        if not os.path.exists(path) and remote_meta(os.path.basename(path)) is not None:
            _, res = _dbx().files_download(_rpath(os.path.basename(path)))
            _write_atomic(path, res.content)
    except Exception:
        pass


def _schedule_log_push(path):
    import dropbox
    S, dbx = _sync_state(), _dbx()
    name = os.path.basename(path)
    with S["lock"]:
        if S["timers"].get(path):
            return

        def _go():
            with S["lock"]:
                S["timers"].pop(path, None)
            try:
                with open(path, "rb") as f:
                    data = f.read()
                dbx.files_upload(data, _rpath(name), mode=dropbox.files.WriteMode.overwrite, mute=True)
            except Exception:
                pass
        t = threading.Timer(LOG_PUSH_DELAY, _go)
        t.daemon = True
        S["timers"][path] = t
        t.start()


@st.cache_data(ttl=15, show_spinner=False)
def _list_remote_folder(_token=0):
    dbx, out = _dbx(), []
    res = dbx.files_list_folder(DROPBOX_FOLDER)
    while True:
        for e in res.entries:
            if hasattr(e, "rev"):
                out.append({"name": e.name, "rev": e.rev,
                            "hash": getattr(e, "content_hash", None) or e.rev,
                            "mtime": e.server_modified.replace(tzinfo=timezone.utc).timestamp()})
        if not res.has_more:
            break
        res = dbx.files_list_folder_continue(res.cursor)
    return out


def _remote_excel_names():
    try:
        return [x for x in _list_remote_folder()
                if x["name"].lower().endswith(".xlsx") and not x["name"].startswith("~$")]
    except Exception:
        return []


def _pick_remote(names, pattern):
    ms = [x for x in names if fnmatch.fnmatchcase(x["name"].lower(), pattern.lower())]
    return max(ms, key=lambda x: x["mtime"]) if ms else None


def excel_pattern_matches():
    if USE_DROPBOX:
        return _pick_remote(_remote_excel_names(), EXCEL_PATTERN) is not None
    return bool([f for f in glob.glob(os.path.join(CURRENT_DIR, EXCEL_PATTERN))
                 if not os.path.basename(f).startswith("~$")])


def _dropbox_excel():
    """Downloads the newest matching journal from Dropbox (only when it changed) and returns the local copy."""
    S = _sync_state()
    try:
        names = [x for x in _list_remote_folder()
                 if x["name"].lower().endswith(".xlsx") and not x["name"].startswith("~$")]
        chosen = None
        if EXCEL_OVERRIDE:
            chosen = next((x for x in names if x["name"].lower() == EXCEL_OVERRIDE.lower()), None)
        chosen = chosen or _pick_remote(names, EXCEL_PATTERN) or _pick_remote(names, EXCEL_FALLBACK_PATTERN)
        if not chosen:
            return None
        local = os.path.join(DATA_DIR, chosen["name"])
        with S["lock"]:
            if (not os.path.exists(local)) or S["xl_hash"].get(chosen["name"]) != chosen["hash"]:
                _, res = _dbx().files_download(_rpath(chosen["name"]))
                _write_atomic(local, res.content)
                S["xl_hash"][chosen["name"]] = chosen["hash"]
        return local
    except Exception as e:
        bot_log("warn", "Dropbox", f"Cannot fetch the journal: {str(e)[:120]}", "using the saved copy")
        old = [f for f in glob.glob(os.path.join(DATA_DIR, "*.xlsx")) if not os.path.basename(f).startswith("~$")]
        return max(old, key=os.path.getmtime) if old else None


def resync_now():
    """Forget everything we know about Dropbox so the next read downloads fresh copies."""
    st.cache_data.clear()
    if USE_DROPBOX:
        S = _sync_state()
        with S["lock"]:
            S["last_pull"].clear()
            S["rev"].clear()
            S["xl_hash"].clear()


# ==========================================
# BACKUPS
# ==========================================
def backup_file(path, tag):
    try:
        if not os.path.exists(path):
            return None
        stamp = now_kh().strftime("%Y-%m-%d_%H%M%S")
        name = f"{stamp}_{tag}_{os.path.basename(path)}"
        if USE_DROPBOX:
            import dropbox
            with open(path, "rb") as f:
                _dbx().files_upload(f.read(), f"{_remote_backup_dir()}/{name}",
                                    mode=dropbox.files.WriteMode.add, autorename=True, mute=True)
            return name
        os.makedirs(BACKUP_DIR, exist_ok=True)
        dest = os.path.join(BACKUP_DIR, name)
        shutil.copy2(path, dest)
        return dest
    except Exception:
        return None


def latest_good_backup(path):
    """Newest daily backup of this file (a local file path to copy from), or None."""
    base = os.path.basename(path)
    pat = re.compile(r"^\d{4}-\d{2}-\d{2}_" + re.escape(base) + r"$")
    if USE_DROPBOX:
        try:
            res = _dbx().files_list_folder(_remote_backup_dir())
            ents = list(res.entries)
            while res.has_more:
                res = _dbx().files_list_folder_continue(res.cursor)
                ents += list(res.entries)
            names = sorted(e.name for e in ents if hasattr(e, "rev") and pat.match(e.name))
            if not names:
                return None
            _, r = _dbx().files_download(f"{_remote_backup_dir()}/{names[-1]}")
            local = os.path.join(DATA_DIR, "restore_" + names[-1])
            _write_atomic(local, r.content)
            return local
        except Exception:
            return None
    files = [f for f in glob.glob(os.path.join(BACKUP_DIR, "*")) if pat.match(os.path.basename(f))]
    return max(files, key=os.path.getmtime) if files else None


def prune_backups():
    removed = 0
    try:
        if USE_DROPBOX:
            res = _dbx().files_list_folder(_remote_backup_dir())
            ents = list(res.entries)
            while res.has_more:
                res = _dbx().files_list_folder_continue(res.cursor)
                ents += list(res.entries)
            now = datetime.now(timezone.utc).timestamp()
            for e in ents:
                if not hasattr(e, "rev"):
                    continue
                age_days = (now - e.server_modified.replace(tzinfo=timezone.utc).timestamp()) / 86400
                extra = re.match(r"^\d{4}-\d{2}-\d{2}_\d{6}_", e.name)
                if age_days > 30 or (extra and age_days > 7):
                    _dbx().files_delete_v2(f"{_remote_backup_dir()}/{e.name}")
                    removed += 1
            return removed
        now = time.time()
        for f in glob.glob(os.path.join(BACKUP_DIR, "*")):
            age_days = (now - os.path.getmtime(f)) / 86400
            extra = re.match(r"^\d{4}-\d{2}-\d{2}_\d{6}_", os.path.basename(f))
            if age_days > 30 or (extra and age_days > 7):
                os.remove(f)
                removed += 1
    except Exception:
        pass
    return removed


@st.cache_resource(show_spinner=False)
def daily_backup_once(day_str):
    """One copy of each CSV per day (cached, so it costs nothing on later runs)."""
    try:
        if USE_DROPBOX:
            dbx = _dbx()
            try:
                dbx.files_create_folder_v2(_remote_backup_dir())
            except Exception:
                pass                                        # already exists
            for f in (DATA_FILE, PACKING_FILE, ASSIGN_FILE):
                base = os.path.basename(f)
                dest = f"{_remote_backup_dir()}/{day_str}_{base}"
                try:
                    if remote_meta(base) is None:
                        continue
                    try:
                        dbx.files_get_metadata(dest)
                    except Exception as e:
                        if _is_not_found(e):
                            dbx.files_copy_v2(_rpath(base), dest)
                except Exception:
                    pass
        else:
            os.makedirs(BACKUP_DIR, exist_ok=True)
            for f in (DATA_FILE, PACKING_FILE, ASSIGN_FILE):
                dest = os.path.join(BACKUP_DIR, f"{day_str}_{os.path.basename(f)}")
                if os.path.exists(f) and not os.path.exists(dest):
                    shutil.copy2(f, dest)
        prune_backups()
    except Exception:
        pass
    return True


# ==========================================
# CSV READ (cached by file change) / WRITE
# ==========================================
def _csv_read(path, cols):
    df = pd.DataFrame()
    if os.path.exists(path) and os.path.getsize(path) > 0:
        try:
            df = pd.read_csv(path, dtype=str, keep_default_na=False, encoding="utf-8-sig")
        except Exception:
            try:
                df = pd.read_csv(path, dtype=str, keep_default_na=False, encoding="utf-8-sig",
                                 engine="python", on_bad_lines="skip")
            except Exception:
                df = pd.DataFrame()
    for c in cols:
        if c not in df.columns:
            df[c] = "0" if c in NUM_COLS_ALL else "-"
    for c in df.columns:
        df[c] = df[c].astype(str).str.strip()
    for c in cols:
        if c == "Date":
            continue
        if c in NUM_COLS_ALL:
            df[c] = pd.to_numeric(df[c], errors="coerce").fillna(0).round().astype(int)
        else:
            df[c] = df[c].replace({"": "-", "nan": "-", "NaN": "-", "None": "-"})
            if c == "Customer":
                df[c] = df[c].str.replace(r"\s+", " ", regex=True)
    df["_dt"] = parse_dates(df["Date"])
    return df.reset_index(drop=True)


@st.cache_data(show_spinner=False, max_entries=8)
def _csv_cached(path, mtime_ns, size, cols):
    return _csv_read(path, list(cols))


def read_raw(path, cols):
    """Cleaned DataFrame of a CSV (with hidden `_dt` datetime column). Fast: cached until the file changes."""
    if USE_DROPBOX:
        try:
            pull(path)                                   # cheap check, downloads only if Dropbox changed
        except Exception as e:
            bot_log("warn", "Dropbox", f"Could not refresh {os.path.basename(path)}: {str(e)[:100]}", "using the saved copy")
    try:
        stt = os.stat(path)
        key = (stt.st_mtime_ns, stt.st_size)
    except OSError:
        key = (0, 0)
    return _csv_cached(path, key[0], key[1], tuple(cols)).copy()


def save_csv(path, df):
    out = df.drop(columns=[c for c in ("_dt",) if c in df.columns])
    tmp = path + ".tmp"

    def _do():
        with file_lock(path):
            out.to_csv(tmp, index=False, encoding="utf-8-sig")
            os.replace(tmp, path)
    _retry(_do)
    if USE_DROPBOX:
        push(path)


def _append_local_many(path, rows):
    """Appends rows to the local file, keeping the column order of the existing file."""
    with file_lock(path):
        exists = os.path.exists(path) and os.path.getsize(path) > 0
        if not exists:
            pd.DataFrame(rows).to_csv(path, index=False, encoding="utf-8-sig")
            return
        header = list(pd.read_csv(path, nrows=0, encoding="utf-8-sig").columns)
        if all(set(r) <= set(header) for r in rows):
            with open(path, "rb") as fh:                       # file must end with a newline
                fh.seek(-1, os.SEEK_END)
                needs_nl = fh.read(1) not in (b"\n", b"\r")
            if needs_nl:
                with open(path, "ab") as fh:
                    fh.write(b"\r\n")
            ordered = [{c: r.get(c, "-") for c in header} for r in rows]
            pd.DataFrame(ordered).to_csv(path, mode="a", header=False, index=False, encoding="utf-8-sig")
        else:                                                  # file lacks some columns -> rewrite once
            df = pd.read_csv(path, encoding="utf-8-sig")
            df = pd.concat([df, pd.DataFrame(rows)], ignore_index=True)
            df.to_csv(path, index=False, encoding="utf-8-sig")


def append_rows(path, rows):
    """Add several rows in ONE save (text is cleaned first). Online: one download, one upload."""
    rows = [{k: (v if k == "Date" or not isinstance(v, str) else safe_text(v)) for k, v in r.items()} for r in rows]
    if not rows:
        return
    if not USE_DROPBOX:
        _retry(lambda: _append_local_many(path, rows))
        return
    last = None
    for attempt in range(6):
        try:
            with _sync_state()["lock"]:
                pull(path, force=True)
                _append_local_many(path, rows)
                push(path)
            return
        except ConflictError as e:
            last = e
            time.sleep(0.2 * (attempt + 1))
    raise RuntimeError("Dropbox is busy - please press Save again") from last


def append_row(path, row):
    """Add ONE row (see append_rows)."""
    append_rows(path, [row])


def modify_csv(path, cols, fn):
    """Safe read-change-save: always starts from the newest file. fn(df) returns the new DataFrame."""
    last = None
    for attempt in range(6):
        try:
            with _sync_state()["lock"]:
                pull(path, force=True)
                df = _csv_read(path, cols)
                save_csv(path, fn(df))
            return
        except ConflictError as e:
            last = e
            time.sleep(0.2 * (attempt + 1))
    raise RuntimeError("Dropbox is busy - please try again") from last


def rows_for_day(df, target_date):
    if df.empty or "_dt" not in df.columns:
        return df.iloc[0:0].copy()
    mask = df["_dt"].dt.normalize() == pd.Timestamp(target_date)
    out = df[mask].copy()
    out["Time"] = out["_dt"].dt.strftime("%I:%M %p")
    return out


# ==========================================
# EXCEL JOURNAL SNAPSHOT (fast read-only parse + memory cache + disk cache)
# ==========================================
def find_excel_file():
    if USE_DROPBOX:
        return _dropbox_excel()

    def _files(pattern):
        fs = glob.glob(os.path.join(CURRENT_DIR, pattern))
        return [f for f in fs if not os.path.basename(f).startswith("~$")]

    if EXCEL_OVERRIDE:
        p = os.path.join(CURRENT_DIR, EXCEL_OVERRIDE)
        if os.path.exists(p):
            return p
    for pat in (EXCEL_PATTERN, EXCEL_FALLBACK_PATTERN):
        fs = _files(pat)
        if fs:
            return max(fs, key=os.path.getmtime)
    return None


def _cell_text(v):
    if v is None:
        return ""
    if isinstance(v, float) and v.is_integer():
        return str(int(v))
    if isinstance(v, (datetime, date)):
        return v.strftime("%Y-%m-%d")
    s = re.sub(r"\s+", " ", str(v)).strip()
    return "" if s.lower() in ("nan", "none", "nat") else s


def _find_invoice(row, inv_col):
    """Invoice column first; if empty, the first cell (from column 3 on) that starts with INVOICE_PREFIX."""
    if inv_col is not None and inv_col < len(row):
        s = _cell_text(row[inv_col])
        if s:
            return s
    pre = INVOICE_PREFIX.upper()
    for c_i in range(2, len(row)):
        v = row[c_i]
        if isinstance(v, str):
            s = v.strip()
            if s.upper().startswith(pre) and len(s) > len(pre):
                return s
    return "-"


def _read_excel_snapshot(path):
    from openpyxl import load_workbook
    wb = load_workbook(path, read_only=True, data_only=True)
    try:
        names = wb.sheetnames
        if SHEET_NAME not in names:
            raise ValueError(f"Sheet '{SHEET_NAME}' not found. Sheets in file: {names}")
        if JOURNAL_SHEET not in names:
            raise ValueError(f"Sheet '{JOURNAL_SHEET}' not found. Sheets in file: {names}")

        # --- Master List: customer names ---
        ws = wb[SHEET_NAME]
        try:
            ws.reset_dimensions()
        except Exception:
            pass
        col_idx, rows_after = None, []
        for row in ws.iter_rows(values_only=True):
            if col_idx is None:
                for i, v in enumerate(row):
                    if v is not None and str(v).strip() == COLUMN_NAME:
                        col_idx = i
                        break
                continue
            if col_idx < len(row) and row[col_idx] is not None:
                n = re.sub(r"\s+", " ", str(row[col_idx])).strip()
                if n:
                    rows_after.append((n, row))
        customers = sorted({n for n, _ in rows_after})

        # the column that says "Province" / "Phnom Penh" / "Unknown" (it has no header in your file, so it is found by its values)
        best_i, best_n = None, 0
        for i in range(max((len(r) for _, r in rows_after), default=0)):
            if i == col_idx:
                continue
            hits = sum(1 for _, r in rows_after if i < len(r) and isinstance(r[i], str)
                       and r[i].strip().lower() in ("province", "phnom penh", "unknown"))
            if hits > best_n:
                best_i, best_n = i, hits
        areas = {}
        if best_i is not None and best_n >= 5:
            for n, r in rows_after:
                v = str(r[best_i]).strip().lower() if best_i < len(r) and r[best_i] is not None else ""
                a = {"province": "Province", "phnom penh": PP}.get(v, "Unknown")
                if n not in areas or (areas[n] == "Unknown" and a != "Unknown"):
                    areas[n] = a

        # --- Journal: date / customer / cases / invoice / remark ---
        ws = wb[JOURNAL_SHEET]
        try:
            ws.reset_dimensions()
        except Exception:
            pass
        raw_rows = []
        cases_col = inv_col = rem_col = None
        for r_i, row in enumerate(ws.iter_rows(values_only=True)):
            if r_i < 15 and (cases_col is None or inv_col is None or rem_col is None):
                for c_i, v in enumerate(row):
                    if v is None:
                        continue
                    sv = str(v)
                    if cases_col is None and JOURNAL_CASES_HEADER in sv:
                        cases_col = c_i
                    elif inv_col is None and JOURNAL_INVOICE_HEADER in sv:
                        inv_col = c_i
                    elif rem_col is None and JOURNAL_REMARK_HEADER in sv:
                        rem_col = c_i
            if len(row) < 2 or row[1] is None:
                continue
            name = re.sub(r"\s+", " ", str(row[1])).strip()
            if not name or name == JOURNAL_HEADER_TEXT:
                continue
            qty = row[cases_col] if (cases_col is not None and cases_col < len(row)) else None
            inv = _find_invoice(row, inv_col)
            rem = _cell_text(row[rem_col]) if (rem_col is not None and rem_col < len(row)) else ""
            raw_rows.append((row[0], name, qty, inv, rem or "-"))
    finally:
        wb.close()

    months = Counter((r[0].year, r[0].month) for r in raw_rows if isinstance(r[0], datetime))
    dominant = months.most_common(1)[0][0] if months else None
    out = []
    for v, name, qty, inv, rem in raw_rows:
        d = cell_to_date(v, dominant)
        if d is None:
            continue
        try:
            q = pd.to_numeric(qty, errors="coerce")
            q = None if pd.isna(q) else float(q)
        except Exception:
            q = None
        out.append((d, name, q, inv, rem))
    journal = pd.DataFrame(out, columns=["Date", "Customer", "Cases", "Invoice", "Remark"])
    journal["Cases"] = pd.to_numeric(journal["Cases"], errors="coerce")
    return {"customers": customers, "journal": journal, "cases_col_found": cases_col is not None,
            "invoice_col_found": inv_col is not None, "areas": areas, "area_col_found": bool(areas)}


def load_snapshot(path, mtime_ns, size):
    """Returns (data, source). source = 'disk' | 'fresh' | 'stale' (last good copy used)."""
    os.makedirs(CACHE_DIR, exist_ok=True)
    cache_file = os.path.join(CACHE_DIR, "excel_snapshot.pkl")
    key = (SNAPSHOT_VERSION, os.path.basename(path), mtime_ns, size)
    obj = None
    try:
        with open(cache_file, "rb") as f:
            obj = pickle.load(f)
        if obj.get("key") == key:
            return obj["data"], "disk"
    except Exception:
        obj = None
    try:
        data = _read_excel_snapshot(path)
    except Exception as e:
        if obj and obj.get("data") and obj.get("key", (0,))[0] == SNAPSHOT_VERSION:
            bot_log("fixed", "Excel", f"Could not read journal ({str(e)[:120]}); using last good copy", "used saved copy")
            return obj["data"], "stale"
        raise
    try:
        tmp = cache_file + ".tmp"
        with open(tmp, "wb") as f:
            pickle.dump({"key": key, "data": data}, f)
        os.replace(tmp, cache_file)
    except Exception:
        pass
    return data, "fresh"


@st.cache_data(ttl=120, show_spinner="📄 Loading journal (first time only)...", max_entries=4)
def get_snapshot(path, mtime_ns, size):
    return load_snapshot(path, mtime_ns, size)


def current_snapshot():
    """(snapshot | None, source, path, error text | None). Never raises."""
    path = find_excel_file()
    if not path or not os.path.exists(path):
        return None, None, path, f"No journal file found in {where_text()}"
    try:
        stt = os.stat(path)
        data, src = get_snapshot(path, stt.st_mtime_ns, stt.st_size)
        return data, src, path, None
    except Exception as e:
        return None, None, path, str(e)


def get_customer_list():
    snap, _, _, err = current_snapshot()
    if snap and snap["customers"]:
        return snap["customers"]
    return [f"⚠️ Error: {err or 'Master List is empty'}"]


# ==========================================
# 🤖 HEALTH BOT  (detects problems and fixes them by itself)
# ==========================================
LEVEL_ICON = {"ok": "✅ OK", "fixed": "🔧 Fixed", "warn": "⚠️ Warning", "error": "❌ Error", "info": "ℹ️ Info"}


def canonical_map(master):
    groups = {}
    for n in master:
        groups.setdefault(norm_name(n), []).append(n)
    return {k: v[0] for k, v in groups.items() if len(v) == 1}


def _check_csv(add, key, master, auto_fix):
    path, cols, nums, label = FILES[key]
    base = os.path.basename(path)
    suggestions = []

    if USE_DROPBOX:                                  # never "repair" because of a network problem
        try:
            pull(path, force=True)
        except Exception as e:
            add("error", label, f"Cannot reach Dropbox for {base}: {str(e)[:100]}", "will retry at the next check")
            return suggestions

    # 1) missing / empty file
    if (not os.path.exists(path)) or os.path.getsize(path) == 0:
        if auto_fix:
            pd.DataFrame(columns=cols).to_csv(path, index=False, encoding="utf-8-sig")
            if USE_DROPBOX:
                push(path)
            add("fixed", label, f"{base} was missing or empty", "created a new file with headers")
        else:
            add("warn", label, f"{base} is missing or empty", "would create a new file")
        return suggestions

    # 2) corrupted file (broken lines, bad encoding)
    try:
        raw = pd.read_csv(path, dtype=str, keep_default_na=False, encoding="utf-8-sig")
    except Exception as e:
        reason = str(e).splitlines()[0] if str(e) else type(e).__name__
        if not auto_fix:
            add("error", label, f"{base} cannot be read: {reason}", "would repair")
            return suggestions
        backup_file(path, "corrupt")
        repaired = None
        try:
            repaired = pd.read_csv(path, dtype=str, keep_default_na=False, encoding="utf-8-sig",
                                   engine="python", on_bad_lines="skip")
        except Exception:
            pass
        if repaired is not None and len(repaired) > 0:
            save_csv(path, repaired)
            add("fixed", label, f"{base} had broken lines ({reason})", "kept good rows; original saved in backups")
        else:
            good = latest_good_backup(path)
            if good:
                shutil.copy2(good, path)
                if USE_DROPBOX:
                    push(path)
                add("fixed", label, f"{base} was unreadable", f"restored from backup {os.path.basename(good)}")
            else:
                add("error", label, f"{base} is unreadable and there is no backup", "needs manual help")
                return suggestions
        raw = pd.read_csv(path, dtype=str, keep_default_na=False, encoding="utf-8-sig")

    df = _csv_read(path, cols)
    fixed = df.copy()
    notes = []

    missing = [c for c in cols if c not in raw.columns]
    if missing:
        notes.append(f"added missing columns {missing}")

    n_nan = int(raw.isin(["nan", "NaN", "None"]).sum().sum())
    if n_nan:
        notes.append(f"cleaned {n_nan} 'nan' texts")

    n_name = 0
    if master and "Customer" in fixed.columns:
        canon = canonical_map(master)
        master_set = set(master)

        def _fix_name(n):
            if n in master_set:
                return n
            return canon.get(norm_name(n), n)
        new_names = fixed["Customer"].map(_fix_name)
        n_name = int((new_names != fixed["Customer"]).sum())
        fixed["Customer"] = new_names
    if n_name:
        notes.append(f"corrected {n_name} customer names (spaces/capitals)")

    dup = fixed.duplicated(subset=cols, keep="first")
    n_dup = int(dup.sum())
    if n_dup:
        fixed = fixed[~dup]
        notes.append(f"removed {n_dup} double-click duplicates")

    if notes:
        if auto_fix:
            backup_file(path, "before-fix")
            save_csv(path, fixed)
            add("fixed", label, f"{base}: " + "; ".join(notes), "saved clean file (backup kept)")
        else:
            add("warn", label, f"{base}: " + "; ".join(notes), "would fix automatically")

    bad_dates = fixed.index[fixed["_dt"].isna()].tolist()
    if bad_dates:
        lines = ", ".join(str(i + 2) for i in bad_dates[:8])
        add("warn", label, f"{base}: {len(bad_dates)} rows have an unreadable Date (file lines {lines})",
            "fix them in the Admin tool")
    for c in nums:
        if c in fixed.columns and (fixed[c] < 0).any():
            add("warn", label, f"{base}: negative numbers in {c}", "check them in the Admin tool")

    if master and "Customer" in fixed.columns:
        master_set = set(master)
        unknown = sorted({n for n in fixed["Customer"].unique() if n not in master_set and n != "-"})
        no_match = []
        for n in unknown[:60]:
            close = difflib.get_close_matches(n, master, n=1, cutoff=0.9)
            if close:
                suggestions.append((key, n, close[0]))
            else:
                no_match.append(n)
        if suggestions:
            add("warn", label, f"{base}: {len(suggestions)} customer names look like typos", "see suggestions below")
        if no_match:
            add("info", label, f"{base}: names not in Master List: {', '.join(no_match[:4])}"
                + (" ..." if len(no_match) > 4 else ""), "-")
    return suggestions


def run_health_check(auto_fix=True):
    """Returns (findings, suggestions). With auto_fix=True the bot repairs what is safe to repair."""
    findings, suggestions = [], []

    def add(level, check, message, action="-"):
        findings.append({"Level": LEVEL_ICON[level], "Check": check, "Message": message, "Action": action})
        if level in ("fixed", "warn", "error") and auto_fix:
            bot_log(level, check, message, action)

    # --- storage ---
    if USE_DROPBOX:
        try:
            _dbx().files_get_metadata(DROPBOX_FOLDER)
            add("info", "Dropbox", f"Connected - data folder {DROPBOX_FOLDER}", "-")
        except Exception as e:
            add("error", "Dropbox", f"Cannot open folder '{DROPBOX_FOLDER}': {str(e)[:120]}",
                "check DROPBOX_FOLDER, the app permissions and the token")

    # --- Excel journal ---
    path = find_excel_file()
    master = []
    if not path:
        add("error", "Excel", f"No journal file found in {where_text()}", "put the .xlsx in that folder")
    else:
        if (not EXCEL_OVERRIDE) and not excel_pattern_matches():
            add("fixed", "Excel", f"No file matches '{EXCEL_PATTERN}'", f"switched to {os.path.basename(path)}")
        snap, src, _, err = current_snapshot()
        if err:
            add("error", "Excel", f"Cannot read '{os.path.basename(path)}': {err}",
                "close it in Excel / wait for Dropbox, bot retries automatically")
        else:
            master = snap["customers"]
            if src == "stale":
                add("fixed", "Excel", "Journal file was locked or half-synced", "using the last good copy")
            if not master:
                add("warn", "Excel", "Master List has no customers", "check sheet 'Master List'")
            if not snap["cases_col_found"]:
                add("warn", "Excel", f"No column '{JOURNAL_CASES_HEADER}' found in the journal", "ordered cases will be empty")
            if not snap.get("invoice_col_found", True):
                add("info", "Excel", f"No column '{JOURNAL_INVOICE_HEADER}' found; invoice numbers use the '{INVOICE_PREFIX}' cells", "-")
            if "conflicted copy" in os.path.basename(path).lower():
                add("info", "Excel", "Using a Dropbox 'conflicted copy' file", "-")

    # --- customer locations ---
    try:
        snap2, _, _, err2 = current_snapshot()
        if snap2 is not None:
            if not snap2.get("area_col_found"):
                add("warn", "Locations", "No Province / Phnom Penh column found in the Master List", "places come from customer names only")
            areas2, ov2 = areas_lookup(snap2), load_location_overrides()
            recent = snap2["journal"]
            recent = recent[recent["Date"] >= today_kh() - timedelta(days=7)]["Customer"].unique()
            n_unk = sum(1 for n in recent if resolve_location(n, areas2.get(norm_name(n)), ov2.get(norm_name(n)))[1]
                        in ("Unknown province", "Unknown"))
            if n_unk:
                add("info", "Locations", f"{n_unk} customers of the last 7 days have no known province", "admin can set them in the Admin tab")
    except Exception:
        pass

    # --- CSV files ---
    for key in FILES:
        try:
            suggestions += _check_csv(add, key, master, auto_fix)
        except Exception as e:
            add("error", FILES[key][3], f"Check failed: {e}", "-")

    # --- backups, locks, disk ---
    if auto_fix:
        daily_backup_once(today_kh().strftime("%Y-%m-%d"))
    elif not glob.glob(os.path.join(BACKUP_DIR, f"{today_kh():%Y-%m-%d}_*")):
        add("warn", "Backup", "No backup made today yet", "would create one")
    for lk in glob.glob(os.path.join(DATA_DIR, "*.lock")):
        try:
            if time.time() - os.path.getmtime(lk) > 30:
                if auto_fix:
                    os.remove(lk)
                    add("fixed", "Locks", f"Removed stuck lock {os.path.basename(lk)}", "deleted")
                else:
                    add("warn", "Locks", f"Stuck lock {os.path.basename(lk)}", "would delete")
        except OSError:
            pass
    try:
        free_gb = shutil.disk_usage(CURRENT_DIR).free / 1e9
        if free_gb < 1:
            add("warn", "Disk", f"Only {free_gb:.1f} GB free on this drive", "free some space")
    except Exception:
        pass

    # --- security ---
    try:
        users = load_users()
        if not [u for u, r in users.items() if r.get("role") == "admin" and r.get("active", True)]:
            add("error", "Security", "There is no active admin account", "delete users.json to restart with the starter admin")
        starters = [u for u, r in users.items() if r.get("must_change")]
        if starters:
            add("warn", "Security", f"Still on a starter password: {', '.join(sorted(starters))}",
                "log in with each account and choose a new password")
        n_fail = failed_logins(1)
        if n_fail >= 15:
            add("warn", "Security", f"{n_fail} wrong-password attempts in the last hour", "see the Audit log; consider changing passwords")
    except Exception:
        pass
    try:
        major, minor = [int(x) for x in st.__version__.split(".")[:2]]
        if (major, minor) < (1, 37):
            add("warn", "Streamlit", f"Version {st.__version__} is old (fast mode needs 1.37+)", "pip install -U streamlit")
    except Exception:
        pass

    if not findings:
        add("ok", "All checks", "No problems found", "-")
    return findings, suggestions


@st.cache_data(ttl=BOT_INTERVAL_MIN * 60, show_spinner=False)
def auto_bot(_token=0):
    """Runs by itself at start-up and then every BOT_INTERVAL_MIN minutes."""
    try:
        return run_health_check(auto_fix=True)
    except Exception as e:
        bot_log("error", "Bot", f"Health check crashed: {e}", "-")
        return [{"Level": LEVEL_ICON["error"], "Check": "Bot", "Message": str(e), "Action": "-"}], []


def apply_name_fixes(suggestions):
    by_file = {}
    for key, bad, good in suggestions:
        by_file.setdefault(key, {})[bad] = good
    for key, mapping in by_file.items():
        path, cols, _, label = FILES[key]
        backup_file(path, "before-name-fix")

        def _rename(frame, mapping=mapping):
            frame["Customer"] = frame["Customer"].replace(mapping)
            return frame
        modify_csv(path, cols, _rename)
        bot_log("fixed", label, f"{len(mapping)} customer names corrected", "applied suggested names")
        audit("name_fix", f"{label}: {len(mapping)} names")


def safe_render(fn, label):
    """If a tab crashes the bot logs it, runs a repair check and offers a retry button."""
    try:
        fn()
    except Exception as e:
        bot_log("error", label, f"{type(e).__name__}: {e}", "auto-repair started")
        if current_role() == "admin":
            st.error(f"⚠️ Problem in {label}: {e}")
        else:
            st.error("⚠️ Something went wrong. The bot is checking the data - press Retry in a moment.")
        flag = f"bot_ran_{label}"
        if time.time() - st.session_state.get(flag, 0) > 60:
            st.session_state[flag] = time.time()
            try:
                run_health_check(auto_fix=True)
                st.cache_data.clear()
                st.info("🤖 The bot checked and repaired the data files. Press Retry.")
            except Exception:
                pass
        if current_role() == "admin":
            with st.expander("Technical details"):
                st.code(traceback.format_exc())
        if st.button("🔁 Retry now", key=f"retry_{label}"):
            st.cache_data.clear()
            st.rerun()


# ==========================================
# UI HELPERS
# ==========================================
CSS = """
<style>
.block-container {padding-top: 1.4rem; padding-bottom: 2.5rem; max-width: 1500px;}
div[data-testid="stMetric"] {background: rgba(128,128,128,.07); border: 1px solid rgba(128,128,128,.22);
    border-radius: 12px; padding: 8px 14px;}
.stButton > button, .stDownloadButton > button, div[data-testid="stFormSubmitButton"] > button {
    border-radius: 10px; min-height: 2.7rem; font-weight: 600;}
footer {visibility: hidden;}
.hk-kpis {display: flex; flex-wrap: wrap; gap: 6px; margin: 4px 0 10px;}
.hk-pill {background: rgba(128,128,128,.10); border: 1px solid rgba(128,128,128,.25); border-radius: 999px;
    padding: 4px 12px; font-size: .92rem; white-space: nowrap;}
.hk-card {background: rgba(128,128,128,.07); border: 1px solid rgba(128,128,128,.22); border-radius: 12px;
    padding: 10px 12px; margin: 7px 0;}
.hk-top {display: flex; justify-content: space-between; gap: 8px; align-items: flex-start;}
.hk-name {font-weight: 700; font-size: 1.02rem; word-break: break-word;}
.hk-badge {border-radius: 999px; padding: 2px 10px; font-size: .78rem; white-space: nowrap;}
.hk-sub {opacity: .75; font-size: .85rem; margin-top: 2px; word-break: break-word;}
.hk-nums {display: flex; flex-wrap: wrap; gap: 6px 18px; margin-top: 6px; font-size: .95rem;}
.hk-note {margin-top: 6px; font-size: .85rem;}
.hk-group {font-weight: 700; margin: 16px 0 4px; padding-bottom: 3px; border-bottom: 2px solid rgba(128,128,128,.3);}
@media (max-width: 640px) {
  .block-container {padding-left: .7rem; padding-right: .7rem;}
  h1 {font-size: 1.45rem !important;}
  h3 {font-size: 1.15rem !important;}
  .hk-pill {font-size: .85rem; padding: 3px 9px;}
}
</style>
"""


def show_df(df, height=None, key=None, selectable=False, column_config=None):
    """Shows a table. Returns the selection event when row-click is available (else None)."""
    base = {"hide_index": True}
    if height:
        base["height"] = height
    if column_config:
        base["column_config"] = column_config
    sel = dict(on_select="rerun", selection_mode="single-row", key=key) if selectable else {}
    for width_kw in ({"width": "stretch"}, {"use_container_width": True}):
        try:
            return st.dataframe(df, **base, **width_kw, **sel)
        except Exception:
            continue
    st.dataframe(df, **base)
    return None


def kpi(container, label, value):
    try:
        container.metric(label, value, border=True)
    except TypeError:
        container.metric(label, value)


def flash_and_refresh(msg):
    st.session_state["flash"] = msg
    st.session_state["clear_sel"] = True
    st.rerun()


# ==========================================
# FORMS
# ==========================================
BASE_VIA = "Grab/TukTuk"


def via_options():
    return [BASE_VIA] + LOCAL_DRIVERS


def expense_status(via, station, pp, taxi):
    """'Pending' while a needed expense (Grab/TukTuk or a taxi station) has no amount yet, otherwise 'Done'."""
    station = (station or "").strip()
    need_pp = via == BASE_VIA
    need_taxi = station not in ("", "-")
    return "Done" if ((not need_pp or _int(pp) > 0) and (not need_taxi or _int(taxi) > 0)) else "Pending"


def current_assignments(day=None):
    """{customer: handler} for a day (the last Assign / Release of each customer wins)."""
    df = rows_for_day(read_raw(ASSIGN_FILE, ASSIGN_COLS), day or today_kh())
    out = {}
    for r in df.to_dict("records"):
        if r["Action"] == "Assign":
            out[r["Customer"]] = r["Handler"]
        elif r["Action"] == "Release":
            out.pop(r["Customer"], None)
    return out


def dispatch_form(form_key, fixed_customer=None, default_cases=1, verify=False):
    k = form_key
    with st.form(form_key, clear_on_submit=True):
        st.markdown("#### Order Details")
        dispatched_by = st.selectbox("Dispatched By:", ["-- Select Staff --"] + OPS_STAFF, key=f"{k}_by")
        if fixed_customer is None:
            customer_name = st.selectbox("Customer Name / ID (Type to search):",
                                         ["-- Select a Customer --"] + get_customer_list(), key=f"{k}_cust")
        else:
            customer_name = fixed_customer
            st.markdown(f"**Customer:** {fixed_customer}")
        d_cases = max(0, min(int(default_cases), MAX_CASES))
        cases = st.number_input("ចំនួនកេស (Number of Cases):", min_value=0, max_value=MAX_CASES, step=1,
                                value=d_cases, key=f"{k}_cases_{d_cases}")
        if verify:
            verified_by = st.selectbox("✅ Cases verified by (confirms the កេស number is correct):",
                                       ["-- Select Staff --"] + OPS_STAFF, key=f"{k}_vby")
        else:
            verified_by = st.selectbox("Cases verified by (optional):", ["-"] + OPS_STAFF, key=f"{k}_vby")

        st.markdown("---")
        st.markdown("#### Transportation Details")
        local_driver = st.selectbox("Local Driver (Phnom Penh):", ["None (Grab/TukTuk)"] + LOCAL_DRIVERS, key=f"{k}_drv")
        taxi_station = st.text_input("Taxi Station Name (Leave blank if purely local Phnom Penh delivery):",
                                     max_chars=MAX_TEXT, key=f"{k}_taxi")
        delivery_note = st.text_input("📝 Note (Optional: Taxi phone number, plate, or instructions):",
                                      max_chars=MAX_TEXT, key=f"{k}_note")

        st.markdown("#### Expenses (៛ Riel) - optional now, you can fill them later in the Delivery tab")
        pp_expense = st.number_input("1. Phnom Penh Expense (៛) - Enter 0 if using own driver:",
                                     min_value=0, max_value=MAX_RIEL, step=500, key=f"{k}_pp")
        taxi_expense = st.number_input("2. Taxi Expense (៛) - Enter 0 if local delivery:",
                                       min_value=0, max_value=MAX_RIEL, step=500, key=f"{k}_te")

        submitted = st.form_submit_button("💾 Save Delivery", type="primary")

        if submitted:
            if dispatched_by == "-- Select Staff --":
                st.error("❌ Please select who dispatched this order.")
            elif customer_name == "-- Select a Customer --" or "⚠️ Error" in customer_name:
                st.error("❌ Please select a valid Customer Name.")
            elif cases == 0:
                st.error("❌ Number of cases must be at least 1.")
            elif verify and verified_by == "-- Select Staff --":
                st.error("❌ Please select who verified the number of cases.")
            else:
                try:
                    handler_local = local_driver if local_driver != "None (Grab/TukTuk)" else BASE_VIA
                    append_row(DATA_FILE, {
                        "Date": now_str(),
                        "Handled_By": dispatched_by,
                        "Customer": customer_name.strip(),
                        "Cases": cases,
                        "Local_Driver": handler_local,
                        "Taxi_Station": taxi_station.strip() or "-",
                        "Phnom_Penh_Expense": pp_expense,
                        "Taxi_Expense": taxi_expense,
                        "Note": delivery_note.strip() or "-",
                        "Verified_By": verified_by,
                        "Expense_Status": expense_status(handler_local, taxi_station, pp_expense, taxi_expense),
                    })
                    audit("dispatch", f"{customer_name} | {cases} cases | by {dispatched_by}")
                    flash_and_refresh(f"Dispatched by {dispatched_by}: {customer_name} | {cases} កេស")
                except Exception as save_err:
                    bot_log("error", "Save dispatch", str(save_err), "-")
                    st.error(f"⚠️ Could not save: {save_err}")


def packing_form(form_key, fixed_customer=None, default_cases=1):
    k = form_key
    with st.form(form_key, clear_on_submit=True):
        if fixed_customer is None:
            customer = st.selectbox("Customer Name / ID (Type to search):",
                                    ["-- Select a Customer --"] + get_customer_list(), key=f"{k}_cust")
        else:
            customer = fixed_customer
            st.markdown(f"**Customer:** {fixed_customer}")
        prepared_by = st.selectbox("Prepared / Packed By:", ["-- Select Staff --"] + OPS_STAFF, key=f"{k}_by")

        col1, col2 = st.columns(2)
        with col1:
            d_cases = max(0, min(int(default_cases), MAX_CASES))
            cases_packed = st.number_input("ចំនួនកេស (Cases Packed/Prepping):", min_value=0, max_value=MAX_CASES,
                                           step=1, value=d_cases, key=f"{k}_cases_{d_cases}")
        with col2:
            pack_status = st.radio("Status of these cases:", ["In Progress (កំពុងធ្វើ)", "Completed (រួចរាល់)"],
                                   key=f"{k}_status")

        if st.form_submit_button("💾 Save Packing Progress", type="primary"):
            if prepared_by == "-- Select Staff --":
                st.error("❌ Please select who is preparing this order.")
            elif customer == "-- Select a Customer --" or "⚠️ Error" in customer:
                st.error("❌ Please select a valid Customer Name.")
            elif cases_packed == 0:
                st.error("❌ Number of cases must be at least 1.")
            else:
                try:
                    append_row(PACKING_FILE, {
                        "Date": now_str(),
                        "Prepared_By": prepared_by,
                        "Customer": customer.strip(),
                        "Cases_Packed": cases_packed,
                        "Status": pack_status,
                    })
                    audit("packing", f"{customer} | {cases_packed} cases | by {prepared_by}")
                    flash_and_refresh(f"Packing logged: {customer} | {cases_packed} cases | {pack_status}")
                except Exception as err:
                    bot_log("error", "Save packing", str(err), "-")
                    st.error(f"⚠️ Could not save: {err}")


def admin_editor(path, cols, num_cols, key, label_cols):
    if current_role() != "admin":
        st.info("🔒 Admin only. Log in with the admin access code to fix or delete entries.")
        return
    try:
        df = read_raw(path, cols)
        df_today = rows_for_day(df, today_kh())
        if df_today.empty:
            st.info("No entries logged for today.")
            return
        labels = {i: f"{i}: " + " | ".join(str(df_today.loc[i, c]) for c in label_cols) for i in df_today.index}
        row_idx = st.selectbox("Select entry to correct:", list(labels.keys()),
                               format_func=lambda i: labels[i], key=f"sel_{key}")
        current = df.loc[row_idx]
        orig = {c: str(current[c]) for c in cols}

        def _match(frame):
            m = pd.Series(True, index=frame.index)
            for c in cols:
                m &= frame[c].astype(str) == orig[c]
            return m

        with st.form(f"edit_form_{key}"):
            new_vals = {}
            for c in cols:
                wkey = f"{key}_{c}_{row_idx}"
                if c in num_cols:
                    step = 500 if c.endswith("Expense") else 1
                    cap = MAX_CASES if "Cases" in c else MAX_RIEL
                    new_vals[c] = st.number_input(f"Edit {c}:", min_value=0, max_value=cap,
                                                  value=min(int(current[c]), cap), step=step, key=wkey)
                else:
                    new_vals[c] = st.text_input(f"Edit {c}:", value=str(current[c]), max_chars=MAX_TEXT, key=wkey)
            col_upd, col_del = st.columns(2)
            update_btn = col_upd.form_submit_button("🔄 Update Record")
            delete_btn = col_del.form_submit_button("🗑️ Delete Wrong Entry")
            if update_btn:
                if pd.isna(parse_dt(new_vals["Date"])):
                    st.error("❌ Date format is invalid. Use YYYY-MM-DD HH:MM:SS")
                else:
                    final = {c: (new_vals[c] if c in num_cols or c == "Date" else safe_text(new_vals[c])) for c in cols}
                    changes = [f"{c}: {orig[c]} -> {final[c]}" for c in cols if orig[c] != str(final[c])]

                    def _upd(frame):
                        m = _match(frame)
                        if not m.any():
                            raise ValueError("This record was changed by someone else. Reload the page and try again.")
                        i = frame.index[m][0]
                        for c in cols:
                            frame.loc[i, c] = final[c]
                        return frame
                    try:
                        backup_file(path, "before-edit")
                        modify_csv(path, cols, _upd)
                        audit("edit", f"{os.path.basename(path)} {current['Customer']} | " + "; ".join(changes))
                        flash_and_refresh("Record updated")
                    except (ValueError, RuntimeError, ConflictError) as err:
                        st.error(f"❌ {err}")
            if delete_btn:
                def _del(frame):
                    m = _match(frame)
                    if not m.any():
                        raise ValueError("This record was already changed or deleted. Reload the page.")
                    return frame.drop(frame.index[m][0])
                try:
                    backup_file(path, "before-delete")
                    modify_csv(path, cols, _del)
                    audit("delete", f"{os.path.basename(path)} {current['Customer']} | {current['Date']}")
                    flash_and_refresh("Record deleted")
                except (ValueError, RuntimeError, ConflictError) as err:
                    st.error(f"❌ {err}")
    except Exception as e:
        bot_log("error", "Admin editor", str(e), "-")
        st.warning(f"Could not load admin panel: {e}")


# ==========================================
# TAB: PACKING
# ==========================================
# ==========================================
# FAST PACKING UPDATE: tick list + upload an Excel/CSV with "done / not yet"
# ==========================================
DONE_WORDS = {"done", "yes", "y", "ok", "okay", "✔", "✓", "✅", "☑", "✔️", "☑️", "true", "1", "complete", "completed",
              "finish", "finished", "ready", "packed", "រួចរាល់", "រួច", "ហើយ", "រួចហើយ", "បានរួច", "បានហើយ", "បានរួចរាល់"}
NOT_WORDS = {"not yet", "notyet", "no", "n", "pending", "wait", "waiting", "todo", "to do", "in progress", "progress",
             "❌", "✗", "✘", "✖", "false", "0", "មិនទាន់", "មិនទាន់រួច", "មិនទាន់ហើយ", "កំពុងធ្វើ", "ចាំ", "ខ្វះ"}
MAX_UPLOAD_BYTES = 5_000_000


def parse_status(v):
    """'done' | 'not' | None (not understood) for one cell of the uploaded file."""
    t = "" if v is None else str(v).strip().lower()
    if not t or t in ("nan", "none"):
        return None
    t = re.sub(r"[\s._\-]+", " ", t).strip()
    if t in DONE_WORDS:
        return "done"
    if t in NOT_WORDS:
        return "not"
    if ("មិនទាន់" in t or "មិនរួច" in t or "កំពុង" in t or "not yet" in t or t.startswith("not ")
            or "pending" in t or "wait" in t):
        return "not"
    if "រួច" in t or "ហើយ" in t or "done" in t or "complete" in t or "finish" in t or "packed" in t or "ready" in t:
        return "done"
    return None


def _col_letter(i):
    i, out = int(i), ""
    while True:
        out = chr(65 + i % 26) + out
        i = i // 26 - 1
        if i < 0:
            return out


def read_upload_tables(up):
    """{sheet name: DataFrame of text} from an uploaded .xlsx / .csv file."""
    name, data = (up.name or "").lower(), up.getvalue()
    if len(data) > MAX_UPLOAD_BYTES:
        raise ValueError("The file is bigger than 5 MB.")
    if name.endswith((".xlsx", ".xlsm")):
        tabs = pd.read_excel(io.BytesIO(data), sheet_name=None, header=None, dtype=str, engine="openpyxl")
    elif name.endswith((".csv", ".txt")):
        text = None
        for enc in ("utf-8-sig", "utf-8", "cp1252", "latin-1"):
            try:
                text = data.decode(enc)
                break
            except UnicodeDecodeError:
                continue
        tabs = {"CSV": pd.read_csv(io.StringIO(text), sep=None, engine="python", header=None, dtype=str,
                                   keep_default_na=False)}
    else:
        raise ValueError("Please upload an .xlsx or .csv file (for an old .xls, save it as .xlsx first).")
    out = {}
    for k, v in tabs.items():
        v = v.fillna("").astype(str).apply(lambda col: col.str.strip())
        v = v[(v != "").any(axis=1)].reset_index(drop=True)
        if not v.empty and len(v) <= 3000:
            out[str(k)] = v
    return out


def guess_columns(tbl, known):
    """Best guess of (customer column, status column, cases column) of an uploaded table."""
    scores = {}
    for c in tbl.columns:
        vals = [v for v in tbl[c] if v]
        if vals:
            scores[c] = {"name": sum(norm_name(v) in known for v in vals) / len(vals),
                         "status": sum(parse_status(v) is not None for v in vals) / len(vals),
                         "num": sum(bool(re.fullmatch(r"\d{1,4}", v)) for v in vals) / len(vals), "n": len(vals)}
    if not scores:
        return None, None, None
    name_col = max(scores, key=lambda c: scores[c]["name"])
    if scores[name_col]["name"] == 0:
        txt = [c for c in scores if scores[c]["num"] < .5 and scores[c]["status"] < .5]
        name_col = max(txt, key=lambda c: scores[c]["n"]) if txt else None
    rest = [c for c in scores if c != name_col]
    status_col = max(rest, key=lambda c: scores[c]["status"], default=None)
    if status_col is not None and scores[status_col]["status"] == 0:
        status_col = None
    cases_col = None
    for c in rest:
        if c == status_col:
            continue
        head = " ".join(tbl[c].head(3)).lower()
        if scores[c]["num"] > .6 and any(k in head for k in ("case", "កេស", "qty", "ចំនួន")):
            cases_col = c
            break
    return name_col, status_col, cases_col


def match_names(names, cand_today, cand_master):
    """{name in file: (customer, how)}. Today's customers are tried first."""
    nt = {norm_name(n): n for n in cand_today}
    nm = {norm_name(n): n for n in cand_master}
    out = {}
    for fn in dict.fromkeys(names):
        k = norm_name(fn)
        if k in nt:
            out[fn] = (nt[k], "✅ exact")
        elif k in nm:
            out[fn] = (nm[k], "⚠️ not scheduled today")
        else:
            res = ("", "❌ not found")
            hit = [v for kk, v in nt.items() if len(k) >= 6 and (k in kk or kk in k)]
            if len(hit) == 1:
                res = (hit[0], "≈ similar - check")
            else:
                c = difflib.get_close_matches(k, list(nt), n=1, cutoff=0.86)
                if c:
                    res = (nt[c[0]], "≈ similar - check")
                else:
                    c = difflib.get_close_matches(k, list(nm), n=1, cutoff=0.9)
                    if c:
                        res = (nm[c[0]], "≈ similar, not scheduled today")
            out[fn] = res
    return out


def packing_context():
    """Today's customers and what is already packed (used to match and to avoid double entries)."""
    df, _, _ = build_report(today_kh())
    snap = current_snapshot()[0]
    recs = df.to_dict("records") if not df.empty else []
    return {"df": df, "master": snap["customers"] if snap else [],
            "today": [r["Customer"] for r in recs if r["Source"] == "Journal"],
            "ordered": {r["Customer"]: (None if pd.isna(r["កេស"]) else int(r["កេស"])) for r in recs},
            "packed": {r["Customer"]: int(r["Packed Cases"]) for r in recs}}


BULK_COLS = ["Save?", "Customer", "Name in file", "Match", "Status", "Cases", "Already packed", "Note"]


def build_bulk_preview(tbl, name_col, status_col, cases_col, blank_means, mark_progress, ctx):
    """One preview row per line of the uploaded file, with a safe default for 'Save?'."""
    names = [tbl.at[i, name_col] for i in tbl.index if tbl.at[i, name_col]]
    matches = match_names(names, ctx["today"], ctx["master"])
    rows, seen = [], set()
    for i in tbl.index:
        fname = tbl.at[i, name_col]
        if not fname:
            continue
        raw = tbl.at[i, status_col] if status_col is not None else ""
        kind = parse_status(raw)
        cust, how = matches[fname]
        note = ""
        if kind is None:
            if raw == "" and blank_means == "Not yet":
                kind = "not"
            elif raw != "":
                note = f"Status not understood: '{raw[:20]}'. "
        if not cust and kind is None:
            continue                                            # header line or an empty line
        file_cases = None
        if cases_col is not None:
            m = re.search(r"\d+", tbl.at[i, cases_col] or "")
            file_cases = int(m.group()) if m else None
        already = ctx["packed"].get(cust, 0) if cust else 0
        ordered = ctx["ordered"].get(cust) if cust else None
        target = file_cases or ordered
        exact = how.startswith("✅")
        if kind == "done":
            label = "Done"
            if target:
                cases = max(target - already, 0)
                if cases == 0:
                    note += f"Already packed {already} of {target}. "
            else:
                cases = 0
                note += "Cases unknown - type the number. "
            save = bool(cust) and exact and cases > 0
        elif kind == "not":
            label = "Not yet"
            cases = (target - already) if (target and target > already) else (target or 1)
            save = bool(cust) and exact and mark_progress
        else:
            label, cases, save = "Skip", 0, False
        if not cust:
            note += "Customer not found - pick the right name or leave it. "
        elif not exact:
            note += "Check that the customer is the right one. "
        if cust and cust in seen:
            save, note = False, note + "Appears twice in the file. "
        if cust:
            seen.add(cust)
        rows.append({"Save?": bool(save), "Customer": cust, "Name in file": fname, "Match": how, "Status": label,
                     "Cases": int(cases), "Already packed": int(already), "Note": note.strip()})
    return pd.DataFrame(rows, columns=BULK_COLS)


def _int(v, default=0):
    try:
        return default if pd.isna(v) else int(v)
    except Exception:
        return default


def bulk_editor(df, ctx, key, check_col="Save?", column_order=None):
    """Editable preview + save button. Saves ALL chosen rows in one go."""
    if df.empty:
        st.info("Nothing to show.")
        return
    prepared_by = st.selectbox("👷 Prepared / packed by", ["-- Select Staff --"] + OPS_STAFF, key=f"{key}_by")
    opts = sorted(set(ctx["today"]) | {c for c in df["Customer"] if c})
    d = df.rename(columns={"Save?": check_col}) if check_col != "Save?" else df
    sig = hashlib.md5("|".join(d["Customer"].astype(str) + d["Name in file"].astype(str)).encode("utf-8")).hexdigest()[:8]
    edited = st.data_editor(
        d, hide_index=True, height=min(480, 60 + 36 * len(d)), key=f"{key}_{sig}_{st.session_state.get('bulk_key', 0)}",
        disabled=[c for c in d.columns if c not in (check_col, "Customer", "Status", "Cases")],
        column_order=column_order,
        column_config={
            check_col: st.column_config.CheckboxColumn(check_col),
            "Customer": st.column_config.SelectboxColumn("Customer", options=opts),
            "Status": st.column_config.SelectboxColumn("Status", options=["Done", "Not yet", "Skip"]),
            "Cases": st.column_config.NumberColumn("Cases", min_value=0, max_value=MAX_CASES, step=1)})
    n_pick = int(edited[check_col].sum())
    st.caption(f"{n_pick} row(s) ticked. 'Cases' = how many to record now (the app never adds more than what is still missing).")
    if st.button(f"💾 Save {n_pick} packing record(s)", key=f"{key}_save", type="primary"):
        if prepared_by == "-- Select Staff --":
            st.error("❌ Please choose who prepared these orders.")
            return
        valid, recs, total = set(ctx["today"]) | set(ctx["master"]), [], 0
        for r in edited.to_dict("records"):
            cust, cases = str(r["Customer"] or "").strip(), _int(r["Cases"])
            if not r[check_col] or r["Status"] == "Skip" or cust not in valid or cases <= 0 or cases > MAX_CASES:
                continue
            recs.append({"Date": now_str(), "Prepared_By": prepared_by, "Customer": cust, "Cases_Packed": cases,
                         "Status": "Completed (រួចរាល់)" if r["Status"] == "Done" else "In Progress (កំពុងធ្វើ)"})
            total += cases
        if not recs:
            st.warning("Nothing to save: tick at least one row that has a customer and cases above 0.")
            return
        try:
            append_rows(PACKING_FILE, recs)
            audit("packing_bulk", f"{len(recs)} customers, {total} cases, by {prepared_by}")
            st.session_state["bulk_key"] = st.session_state.get("bulk_key", 0) + 1
            flash_and_refresh(f"Saved {len(recs)} packing records ({total} cases)")
        except (RuntimeError, ConflictError, PermissionError) as err:
            bot_log("error", "Save packing (bulk)", str(err), "-")
            st.error(f"⚠️ Could not save: {err}")


def checklist_xlsx(ctx):
    """A ready-to-fill Excel list of today's customers with a Done / Not yet drop-down."""
    df = ctx["df"]
    if df.empty:
        return None
    d = df[df["Source"] == "Journal"].copy()
    if d.empty:
        return None
    d["_a"] = d["Area"].map(AREA_RANK)
    d["_g"] = d["Region"].map(_REGION_ORDER).fillna(99)
    d = d.sort_values(["_a", "_g", "Province", "Customer"])
    out = pd.DataFrame({"Customer": d["Customer"], "Area": d["Area"], "Province": d["Province"],
                        "Cases": d["កេស"], "Status": "Not yet"})
    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine="openpyxl") as w:
        out.to_excel(w, index=False, sheet_name="Packing")
        ws = w.sheets["Packing"]
        try:
            from openpyxl.worksheet.datavalidation import DataValidation
            dv = DataValidation(type="list", formula1='"Done,Not yet"', allow_blank=True)
            ws.add_data_validation(dv)
            dv.add(f"E2:E{len(out) + 1}")
            for col, wd in zip("ABCDE", (46, 16, 20, 8, 12)):
                ws.column_dimensions[col].width = wd
            ws.freeze_panes = "A2"
        except Exception:
            pass
    return buf.getvalue()


def _ticklist_tab():
    ctx = packing_context()
    df = ctx["df"]
    if df.empty:
        st.info("No customers in today's journal yet.")
        return
    st.caption("Tick the customers whose buns are packed, check the cases, choose who packed them, and save. "
               "Fastest way on a phone.")
    show_all = st.checkbox("Also show customers that are already packed or sent", key="tick_all")
    d = df[df["Source"] == "Journal"].copy()
    if not show_all:
        d = d[d["Status"].isin(["⏳ Pending", "🟠 Packing"])]
    if d.empty:
        st.success("Everything in today's journal is already packed. 🎉")
        return
    d["_a"] = d["Area"].map(AREA_RANK)
    d["_g"] = d["Region"].map(_REGION_ORDER).fillna(99)
    d = d.sort_values(["_a", "_g", "Province", "Customer"])
    rows = []
    for r in d.to_dict("records"):
        ordered = None if pd.isna(r["កេស"]) else int(r["កេស"])
        packed = int(r["Packed Cases"])
        left = (ordered - packed) if (ordered and ordered > packed) else (0 if ordered else 1)
        rows.append({"Save?": False, "Customer": r["Customer"], "Name in file": "", "Match": "✅ exact", "Status": "Done",
                     "Cases": int(left), "Already packed": packed,
                     "Note": f"{r['Province']} · ordered {ordered if ordered is not None else '-'} · packed {packed}"})
    bulk_editor(pd.DataFrame(rows, columns=BULK_COLS), ctx, key="tick", check_col="Done ✅",
                column_order=["Done ✅", "Customer", "Cases", "Note"])


def _upload_tab():
    ctx = packing_context()
    st.caption("Upload an Excel (.xlsx) or CSV list of customers with **done / not yet**. The app finds the columns, "
               "matches the names, and shows you everything before saving.")
    data = checklist_xlsx(ctx)
    if data:
        st.download_button("📥 Download today's checklist (Excel with a Done / Not yet drop-down)", data=data,
                           file_name=f"Packing_checklist_{today_kh()}.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    bk = st.session_state.get("bulk_key", 0)
    up = st.file_uploader("Excel (.xlsx) or CSV file", type=["xlsx", "xlsm", "csv", "txt"], key=f"bulk_up_{bk}")
    if not up:
        return
    try:
        tables = read_upload_tables(up)
    except Exception as e:
        st.error(f"❌ Could not read the file: {e}")
        return
    if not tables:
        st.error("❌ The file is empty (or has more than 3000 rows).")
        return
    known = {norm_name(n) for n in ctx["today"] + ctx["master"]}
    sheet = list(tables)[0]
    if len(tables) > 1:
        sheet = st.selectbox("Sheet", list(tables), key="bulk_sheet")
    tbl = tables[sheet]
    ng, sg, cg = guess_columns(tbl, known)
    cols = list(tbl.columns)

    def _lab(c):
        if c is None:
            return "(none)"
        sample = next((v for v in tbl[c] if v), "")
        return f"Column {_col_letter(c)}  -  e.g. {sample[:28]}"
    c1, c2, c3 = st.columns(3)
    name_col = c1.selectbox("Customer column", cols, index=cols.index(ng) if ng in cols else 0, format_func=_lab, key="bulk_c1")
    status_opts = [None] + cols
    status_col = c2.selectbox("Status column (done / not yet)", status_opts,
                              index=status_opts.index(sg) if sg in status_opts else 0, format_func=_lab, key="bulk_c2")
    cases_col = c3.selectbox("Cases column (optional)", status_opts,
                             index=status_opts.index(cg) if cg in status_opts else 0, format_func=_lab, key="bulk_c3")
    o1, o2 = st.columns(2)
    blank_means = o1.radio("Empty status means", ["Not yet", "Skip the row"], horizontal=True, key="bulk_blank")
    mark_progress = o2.checkbox("Also save 'Not yet' rows as 🟠 In progress", value=False, key="bulk_prog")
    df = build_bulk_preview(tbl, name_col, status_col, cases_col, blank_means, mark_progress, ctx)
    if df.empty:
        st.warning("No customer names were found in that column. Choose another 'Customer column'.")
        return
    n_done, n_not = int((df["Status"] == "Done").sum()), int((df["Status"] == "Not yet").sum())
    n_bad = int((df["Customer"] == "").sum())
    st.info(f"📄 {len(df)} lines: ✅ {n_done} done, ⏳ {n_not} not yet, ❌ {n_bad} names not found. "
            f"Rows with a green match are ticked for you; check the others.")
    bulk_editor(df, ctx, key="upl", check_col="Save?")


def _packing_body():
    st.markdown("### 📦 Bun Preparation & Packing")
    t_tick, t_up, t_one = st.tabs(["📋 Quick tick list", "📤 Upload a file", "✍️ One customer"])
    with t_tick:
        _ticklist_tab()
    with t_up:
        _upload_tab()
    with t_one:
        packing_form("packing_form")

    with st.expander("🛠️ Admin: Fix or Edit Today's Packing"):
        admin_editor(PACKING_FILE, PACKING_COLS, PACKING_NUM_COLS, key="pack",
                     label_cols=["Customer", "Cases_Packed", "Status"])

    st.markdown("---")
    st.subheader("📋 Today's Packing Log")
    df_today = rows_for_day(read_raw(PACKING_FILE, PACKING_COLS), today_kh())
    if df_today.empty:
        st.info("No packing progress logged today yet.")
        return
    show_df(df_today[PACKING_COLS])
    st.markdown("**👷 Cases packed per staff (today)**")
    show_df(df_today.groupby("Prepared_By")["Cases_Packed"].sum().reset_index())


@st.fragment
def tab_packing():
    safe_render(_packing_body, "Packing tab")


# ==========================================
# TAB: DELIVERY
# ==========================================
def _sorted_records(recs):
    return sorted(recs, key=lambda r: (AREA_RANK.get(r["Area"], 9), _REGION_ORDER.get(r["Region"], 99), r["Province"], r["Customer"]))


def delivery_context():
    ctx = packing_context()
    ctx["recs"] = _sorted_records(ctx["df"].to_dict("records")) if not ctx["df"].empty else []
    ctx["assigned"] = current_assignments()
    return ctx


def _claim_tab(me, ctx):
    st.caption("Choose the customers **you** will deliver today, before you start. Other staff will see they are taken. "
               "You can release a customer again if you cannot go.")
    recs = [r for r in ctx["recs"] if r["Status"] != "✅ Sent"]
    f1, f2 = st.columns(2)
    area = f1.radio("Show", ["All", AREA_LABEL[PP], AREA_LABEL["Province"]], horizontal=True, key="claim_area")
    q = f2.text_input("🔎 Search customer", key="claim_q", max_chars=60)
    if area != "All":
        recs = [r for r in recs if r["Area"] == area]
    if q.strip():
        recs = [r for r in recs if q.strip().lower() in r["Customer"].lower()]
    if not recs:
        st.info("No customers to choose right now.")
    else:
        assigned = ctx["assigned"]
        rows = [{"Take ✅": False, "Customer": r["Customer"], "Province": r["Province"], "Status": r["Status"],
                 "Packed": int(r["Packed Cases"]), "Ordered": None if pd.isna(r["កេស"]) else int(r["កេស"]),
                 "Taken by": assigned.get(r["Customer"], "-")} for r in recs]
        d = pd.DataFrame(rows)
        sig = hashlib.md5("|".join(d["Customer"] + d["Taken by"]).encode("utf-8")).hexdigest()[:8]
        edited = st.data_editor(d, hide_index=True, height=min(460, 60 + 36 * len(d)),
                                key=f"claim_ed_{sig}_{st.session_state.get('bulk_key', 0)}",
                                disabled=[c for c in d.columns if c != "Take ✅"],
                                column_config={"Take ✅": st.column_config.CheckboxColumn("Take ✅")})
        n = int(edited["Take ✅"].sum())
        if st.button(f"✅ I will deliver these {n} customer(s)", key="claim_save", type="primary"):
            new, blocked = [], []
            for r in edited.to_dict("records"):
                if not r["Take ✅"]:
                    continue
                owner = assigned.get(r["Customer"])
                if owner == me:
                    continue
                if owner and current_role() != "admin":
                    blocked.append(f"{r['Customer']} (taken by {owner})")
                    continue
                new.append({"Date": now_str(), "Handler": me, "Customer": r["Customer"], "Action": "Assign"})
            if blocked:
                st.warning("Already taken by someone else, skipped: " + "; ".join(blocked[:6]))
            if not new:
                if not blocked:
                    st.warning("Tick at least one customer first.")
            else:
                try:
                    append_rows(ASSIGN_FILE, new)
                    audit("assign", f"{me}: {len(new)} customers")
                    st.session_state["bulk_key"] = st.session_state.get("bulk_key", 0) + 1
                    flash_and_refresh(f"{me} will deliver {len(new)} customers")
                except (RuntimeError, ConflictError, PermissionError) as err:
                    st.error(f"⚠️ Could not save: {err}")

    mine = [r["Customer"] for r in ctx["recs"] if ctx["assigned"].get(r["Customer"]) == me and r["Status"] != "✅ Sent"]
    pool = mine if current_role() != "admin" else [c for c in ctx["assigned"] if c in {r["Customer"] for r in ctx["recs"]}]
    with st.expander(f"↩️ Release customers ({len(mine)} are mine)"):
        rel = st.multiselect("Customers I will NOT deliver after all", pool, key="claim_release")
        if st.button("↩️ Release selected", key="claim_release_btn") and rel:
            try:
                append_rows(ASSIGN_FILE, [{"Date": now_str(), "Handler": me, "Customer": c, "Action": "Release"} for c in rel])
                audit("assign_release", f"{me}: {len(rel)} customers")
                flash_and_refresh(f"Released {len(rel)} customers")
            except (RuntimeError, ConflictError, PermissionError) as err:
                st.error(f"⚠️ Could not save: {err}")


def _send_tab(me, ctx):
    st.caption("Tick the customers whose buns you have **sent**. Expenses can be filled later in step 3.")
    include_free = st.checkbox("Also show customers nobody has taken yet", key="send_free")
    assigned = ctx["assigned"]
    recs = [r for r in ctx["recs"] if r["Status"] != "✅ Sent"
            and (assigned.get(r["Customer"]) == me or (include_free and r["Customer"] not in assigned))]
    if not recs:
        st.info("You have no customers to send. Choose your customers in step 1 first.")
        return
    c1, c2 = st.columns(2)
    default_via = c1.selectbox("Sent with (default)", via_options(), key="send_via")
    verified_by = c2.selectbox("✅ Cases checked by", ["-- Select Staff --"] + OPS_STAFF, key="send_vby")
    rows = []
    for r in recs:
        ordered = None if pd.isna(r["កេស"]) else int(r["កេស"])
        packed, sent = int(r["Packed Cases"]), int(r["Sent Cases"])
        left = (packed - sent) if packed > sent else ((ordered - sent) if (ordered and ordered > sent) else 1)
        rows.append({"Sent ✅": False, "Customer": r["Customer"], "Cases": int(left), "Via": default_via, "Taxi station": "",
                     "Note": "", "Status": r["Status"], "Province": r["Province"]})
    d = pd.DataFrame(rows)
    sig = hashlib.md5(("|".join(d["Customer"]) + default_via).encode("utf-8")).hexdigest()[:8]
    edited = st.data_editor(
        d, hide_index=True, height=min(480, 60 + 36 * len(d)), key=f"send_ed_{sig}_{st.session_state.get('bulk_key', 0)}",
        column_order=["Sent ✅", "Customer", "Cases", "Via", "Taxi station", "Note", "Status"],
        disabled=["Customer", "Status", "Province"],
        column_config={"Sent ✅": st.column_config.CheckboxColumn("Sent ✅"),
                       "Cases": st.column_config.NumberColumn("Cases", min_value=0, max_value=MAX_CASES, step=1),
                       "Via": st.column_config.SelectboxColumn("Via", options=via_options()),
                       "Taxi station": st.column_config.TextColumn("Taxi station", max_chars=MAX_TEXT, help="Only for provincial taxi / bus"),
                       "Note": st.column_config.TextColumn("Note", max_chars=MAX_TEXT)})
    n = int(edited["Sent ✅"].sum())
    st.caption("Cases are filled in from what is packed. Change them if you sent a different number.")
    if st.button(f"🚚 Save {n} delivery(ies) as sent", key="send_save", type="primary"):
        if verified_by == "-- Select Staff --":
            st.error("❌ Please choose who checked the number of cases.")
            return
        out, take, total = [], [], 0
        for r in edited.to_dict("records"):
            cust, cases, via = r["Customer"], _int(r["Cases"]), r["Via"]
            if not r["Sent ✅"] or cases <= 0 or cases > MAX_CASES or via not in via_options():
                continue
            station = safe_text(r["Taxi station"] or "")
            out.append({"Date": now_str(), "Handled_By": me, "Customer": cust, "Cases": cases, "Local_Driver": via,
                        "Taxi_Station": station or "-", "Phnom_Penh_Expense": 0, "Taxi_Expense": 0,
                        "Note": safe_text(r["Note"] or "") or "-", "Verified_By": verified_by,
                        "Expense_Status": expense_status(via, station, 0, 0)})
            total += cases
            if cust not in assigned:
                take.append({"Date": now_str(), "Handler": me, "Customer": cust, "Action": "Assign"})
        if not out:
            st.warning("Tick at least one customer with cases above 0.")
            return
        try:
            append_rows(DATA_FILE, out)
            if take:
                append_rows(ASSIGN_FILE, take)
            waiting = sum(1 for o in out if o["Expense_Status"] == "Pending")
            audit("dispatch_bulk", f"{len(out)} customers, {total} cases, by {me}")
            st.session_state["bulk_key"] = st.session_state.get("bulk_key", 0) + 1
            flash_and_refresh(f"Saved {len(out)} deliveries ({total} cases). {waiting} need expenses - fill them in step 3")
        except (RuntimeError, ConflictError, PermissionError) as err:
            bot_log("error", "Save dispatch (bulk)", str(err), "-")
            st.error(f"⚠️ Could not save: {err}")


def pending_expense_df(who, scope):
    """Deliveries still waiting for expenses. who = staff name or None (everyone); scope = Today | Last 7 days | All waiting."""
    df = read_raw(DATA_FILE, DISPATCH_COLS)
    df = df[df["Expense_Status"] == "Pending"]
    if who:
        df = df[df["Handled_By"] == who]
    if scope == "Today":
        df = df[df["_dt"].dt.normalize() == pd.Timestamp(today_kh())]
    elif scope == "Last 7 days":
        df = df[df["_dt"] >= pd.Timestamp(today_kh() - timedelta(days=7))]
    return df.reset_index(drop=True)


def _expense_tab(me):
    is_admin = current_role() == "admin"
    st.caption("Fill in what you spent for the deliveries you already sent. Tick **Done** for each row you finish, then save.")
    c1, c2 = st.columns(2)
    scope = c1.radio("Show", ["Today", "Last 7 days", "All waiting"], horizontal=True, key="exp_scope")
    who = me
    if is_admin:
        pick = c2.selectbox("Handler", ["(everyone)"] + OPS_STAFF, key="exp_who")
        who = None if pick == "(everyone)" else pick
    elif me == "-- Select Staff --":
        st.info("Choose your name at the top first.")
        return
    df = pending_expense_df(who, scope)
    if df.empty:
        st.success("Nothing is waiting for expenses. 🎉")
        return
    st.info(f"⏳ {len(df)} deliveries are waiting for expenses.")
    rows = [{"Done ✅": False, "Customer": r["Customer"], "When": str(r["Date"])[5:16], "Via": r["Local_Driver"],
             "Taxi station": "" if r["Taxi_Station"] in ("-", "") else r["Taxi_Station"],
             "Phnom Penh ៛": int(r["Phnom_Penh_Expense"]), "Taxi ៛": int(r["Taxi_Expense"]),
             "By": r["Handled_By"], "Date": r["Date"]} for r in df.to_dict("records")]
    d = pd.DataFrame(rows)
    order = ["Done ✅", "Customer", "When", "Via", "Taxi station", "Phnom Penh ៛", "Taxi ៛"] + (["By"] if who is None else [])
    sig = hashlib.md5("|".join(d["Date"] + d["Customer"]).encode("utf-8")).hexdigest()[:8]
    edited = st.data_editor(
        d, hide_index=True, height=min(480, 60 + 36 * len(d)), key=f"exp_ed_{sig}_{st.session_state.get('bulk_key', 0)}",
        column_order=order, disabled=["Customer", "When", "Via", "By", "Date"],
        column_config={"Done ✅": st.column_config.CheckboxColumn("Done ✅"),
                       "Taxi station": st.column_config.TextColumn("Taxi station", max_chars=MAX_TEXT),
                       "Phnom Penh ៛": st.column_config.NumberColumn("Phnom Penh ៛", min_value=0, max_value=MAX_RIEL, step=500),
                       "Taxi ៛": st.column_config.NumberColumn("Taxi ៛", min_value=0, max_value=MAX_RIEL, step=500)})
    n = int(edited["Done ✅"].sum())
    if st.button(f"💾 Save expenses for {n} delivery(ies)", key="exp_save", type="primary"):
        updates, problems, total = {}, [], 0
        for r in edited.to_dict("records"):
            if not r["Done ✅"]:
                continue
            station, pp, tx = safe_text(r["Taxi station"] or ""), _int(r["Phnom Penh ៛"]), _int(r["Taxi ៛"])
            if r["Via"] == BASE_VIA and pp <= 0:
                problems.append(f"{r['Customer']}: enter the Phnom Penh ៛ (Grab/TukTuk)")
            elif station and tx <= 0:
                problems.append(f"{r['Customer']}: enter the Taxi ៛ for {station}")
            else:
                updates[(str(r["Date"]), r["Customer"], r["By"])] = (station or "-", pp, tx)
                total += pp + tx
        if problems:
            st.error("❌ Not saved yet:\n\n" + "\n".join(f"- {p}" for p in problems[:8]))
            return
        if not updates:
            st.warning("Tick **Done** on the rows you have finished first.")
            return

        def _apply(frame):
            for (dt, cust, by), (station, pp, tx) in updates.items():
                m = (frame["Date"].astype(str) == dt) & (frame["Customer"] == cust) & (frame["Handled_By"] == by)
                if not m.any():
                    raise ValueError(f"The delivery of {cust} was changed by someone else. Reload and try again.")
                i = frame.index[m][0]
                frame.loc[i, "Taxi_Station"] = station
                frame.loc[i, "Phnom_Penh_Expense"] = pp
                frame.loc[i, "Taxi_Expense"] = tx
                frame.loc[i, "Expense_Status"] = "Done"
            return frame
        try:
            modify_csv(DATA_FILE, DISPATCH_COLS, _apply)
            audit("expenses_filled", f"{len(updates)} deliveries, {total} riel, by {me}")
            st.session_state["bulk_key"] = st.session_state.get("bulk_key", 0) + 1
            flash_and_refresh(f"Saved expenses for {len(updates)} deliveries (៛{total:,})")
        except (ValueError, RuntimeError, ConflictError, PermissionError) as err:
            st.error(f"❌ {err}")


# ---- Journal fill sheet: expenses/driver in the same order as the Sale Journal ----
DRIVER_CODE = {"ងិន វុទ្ធា": "VUTHEA", "អួន តួ": "TOU"}      # name in this app -> code typed in journal column អ្នកដឹក
JF_COLS = ["Date", "Customer", "Invoice", "អ្នកដឹក", "សេវាដឹក (ចំណាយ)", "សេវាតាក់ស៊ី (ចំណាយ)", "Taxi station", "Note"]


def build_journal_fill(d_from, d_to):
    """(fill_df, unmatched_df) for deliveries between two dates.
    One row per journal invoice, in journal order. A customer's expenses for one day go on its FIRST invoice
    of that day (0 on the others) so nothing is counted twice - the same way the journal is filled by hand."""
    snap, _, _, err = current_snapshot()
    if not snap:
        return None, None, err or "Journal not found"
    disp = read_raw(DATA_FILE, DISPATCH_COLS)
    if disp.empty or "_dt" not in disp.columns:
        return None, None, "No deliveries saved yet"
    disp = disp[(disp["_dt"].dt.normalize() >= pd.Timestamp(d_from)) & (disp["_dt"].dt.normalize() <= pd.Timestamp(d_to))].copy()
    if disp.empty:
        return None, None, "No deliveries between these dates"
    disp["_day"] = disp["_dt"].dt.date
    disp["_cust"] = disp["Customer"].astype(str).map(lambda x: re.sub(r"\s+", " ", x).strip())
    agg = {}
    for (day, cust), g in disp.groupby(["_day", "_cust"], sort=False):
        drv = [DRIVER_CODE.get(str(x).strip(), "") for x in g["Local_Driver"]]
        drv = [x for x in drv if x]
        st_ = [str(x).strip() for x in g["Taxi_Station"] if str(x).strip() not in ("", "-")]
        notes = [str(x).strip() for x in g["Note"] if str(x).strip() not in ("", "-")]
        agg[(day, cust)] = {"drv": drv[-1] if drv else "", "pp": int(g["Phnom_Penh_Expense"].sum()),
                            "taxi": int(g["Taxi_Expense"].sum()), "station": " / ".join(dict.fromkeys(st_)),
                            "note": " / ".join(dict.fromkeys(notes))}
    jr = snap["journal"]
    jr = jr[(jr["Date"] >= d_from) & (jr["Date"] <= d_to)]
    rows, used = [], set()
    for _, r in jr.iterrows():
        key = (r["Date"], r["Customer"])
        a = agg.get(key)
        first = a is not None and key not in used
        if a is not None:
            used.add(key)
        rows.append({"Date": r["Date"], "Customer": r["Customer"], "Invoice": r["Invoice"],
                     "អ្នកដឹក": a["drv"] if a else "",
                     "សេវាដឹក (ចំណាយ)": (a["pp"] if first else (0 if a else None)),
                     "សេវាតាក់ស៊ី (ចំណាយ)": (a["taxi"] if first else (0 if a and a["taxi"] else None)),
                     "Taxi station": a["station"] if first else "", "Note": a["note"] if first else ""})
    fill = pd.DataFrame(rows, columns=JF_COLS)
    miss = [{"Date": k[0], "Customer": k[1], "អ្នកដឹក": v["drv"], "សេវាដឹក (ចំណាយ)": v["pp"],
             "សេវាតាក់ស៊ី (ចំណាយ)": v["taxi"], "Taxi station": v["station"], "Note": v["note"]}
            for k, v in agg.items() if k not in used]
    return fill, pd.DataFrame(miss), None


def _journal_fill_panel():
    with st.expander("📋 Journal fill sheet - driver & expenses for the Sale Journal"):
        st.caption("Gives អ្នកដឹក, សេវាដឹក (ចំណាយ) and សេវាតាក់ស៊ី (ចំណាយ) in the same order as your journal, "
                   "matched by date + customer. Copy the 3 columns into the journal (or look them up by Invoice).")
        c1, c2 = st.columns(2)
        d_from = c1.date_input("From", value=today_kh().replace(day=1), key="jf_from")
        d_to = c2.date_input("To", value=today_kh(), key="jf_to")
        if st.button("Build journal fill sheet", key="jf_go"):
            fill, miss, err = build_journal_fill(d_from, d_to)
            if err:
                st.warning(err)
                return
            st.session_state["jf_result"] = (fill, miss)
        res = st.session_state.get("jf_result")
        if not res:
            return
        fill, miss = res
        has = fill[(fill["អ្នកដឹក"] != "") | fill["សេវាដឹក (ចំណាយ)"].notna() | fill["សេវាតាក់ស៊ី (ចំណាយ)"].notna()]
        st.success(f"{len(has)} journal rows have delivery data (of {len(fill)} rows in range). "
                   f"Pending expenses are 0 until you fill them in the Delivery tab.")
        buf = io.BytesIO()
        with pd.ExcelWriter(buf, engine="openpyxl") as w:
            fill.to_excel(w, index=False, sheet_name="Journal_Fill")
            if not miss.empty:
                miss.to_excel(w, index=False, sheet_name="Not_in_journal")
        st.download_button("📥 Download journal fill sheet (Excel)", data=buf.getvalue(),
                           file_name=f"Journal_Fill_{d_from}_{d_to}.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
        show_df(has)
        if not miss.empty:
            st.warning(f"{len(miss)} delivery(ies) were not found in the journal (name or date differs):")
            show_df(miss)


def _delivery_log():
    with st.expander("🛠️ Admin: Fix or Edit Today's Dispatches"):
        admin_editor(DATA_FILE, DISPATCH_COLS, DISPATCH_NUM_COLS, key="disp",
                     label_cols=["Customer", "Cases"])

    _journal_fill_panel()
    st.subheader("📊 Today's Operations Log")
    df_today = rows_for_day(read_raw(DATA_FILE, DISPATCH_COLS), today_kh())
    total_expense = int(df_today["Phnom_Penh_Expense"].sum() + df_today["Taxi_Expense"].sum()) if not df_today.empty else 0
    waiting = int((df_today["Expense_Status"] == "Pending").sum()) if not df_today.empty else 0
    m1, m2, m3, m4 = st.columns(4)
    kpi(m1, "Total Slips Today", len(df_today))
    kpi(m2, "Total Cases Dispatched (សរុបចំនួនកេស)", int(df_today["Cases"].sum()) if not df_today.empty else 0)
    kpi(m3, "Total Expenses Today (៛)", f"{total_expense:,}")
    kpi(m4, "⏳ Expenses still to fill", waiting)
    if df_today.empty:
        st.info("No deliveries logged today yet.")
        return

    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine="openpyxl") as writer:
        df_today[DISPATCH_COLS].to_excel(writer, index=False, sheet_name="Ops_Log")
    st.download_button("📥 Download Today's Expenses Log (Excel)", data=buf.getvalue(),
                       file_name=f"Operations_Expenses_{today_kh()}.xlsx",
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    show_df(df_today[["Handled_By", "Customer", "Cases", "Note", "Local_Driver", "Taxi_Station",
                      "Phnom_Penh_Expense", "Taxi_Expense", "Expense_Status", "Verified_By"]])
    st.markdown("**👷 Dispatch summary per staff (today)**")
    per_staff = df_today.groupby("Handled_By").agg(
        Slips=("Customer", "count"), Cases=("Cases", "sum"),
        Expenses=("Phnom_Penh_Expense", "sum"), Taxi=("Taxi_Expense", "sum"),
        Waiting=("Expense_Status", lambda x: int((x == "Pending").sum()))).reset_index()
    show_df(per_staff)


def _dispatch_body():
    st.markdown("### 🚚 Delivery")
    me = st.selectbox("👷 I am (choose your name once)", ["-- Select Staff --"] + OPS_STAFF, key="me_staff")
    ctx = delivery_context()
    mine = [r for r in ctx["recs"] if ctx["assigned"].get(r["Customer"]) == me and r["Status"] != "✅ Sent"]
    n_wait = len(pending_expense_df(me, "All waiting")) if me != "-- Select Staff --" else 0
    if me != "-- Select Staff --":
        st.markdown(f"<div class='hk-kpis'><span class='hk-pill'>📌 To send <b>{len(mine)}</b></span>"
                    f"<span class='hk-pill'>⏳ Expenses to fill <b>{n_wait}</b></span></div>", unsafe_allow_html=True)
    t1, t2, t3, t4, t5 = st.tabs(["1️⃣ Choose my customers", "2️⃣ Send", "3️⃣ Fill my expenses",
                                  "✍️ One customer", "📊 Today's log"])
    need_name = me == "-- Select Staff --"
    with t1:
        if need_name:
            st.info("Choose your name at the top first.")
        else:
            _claim_tab(me, ctx)
    with t2:
        if need_name:
            st.info("Choose your name at the top first.")
        else:
            _send_tab(me, ctx)
    with t3:
        _expense_tab(me)
    with t4:
        st.caption("The full form for a single customer. Expenses are optional - leave them empty to fill them later.")
        dispatch_form("expense_form")
    with t5:
        _delivery_log()


@st.fragment
def tab_dispatch():
    safe_render(_dispatch_body, "Delivery tab")


# ==========================================
# TAB: DASHBOARD (search, filter, click a row to update it)
# ==========================================
def _join_unique(series, sep=", ", limit=3):
    vals = [v for v in dict.fromkeys(series) if v and v != "-"]
    if not vals:
        return "-"
    if len(vals) > limit:
        return sep.join(vals[:limit]) + f" +{len(vals) - limit}"
    return sep.join(vals)


DASH_COLUMNS = ["🔥", "Customer", "Area", "Province", "Region", "Invoice", "Status", "កេស", "Packed Cases", "Prepared By",
                "Assigned To", "Sent Cases", "Handled By", "Verified By", "Driver/Station", "Journal Note", "Note", "Time", "Source"]


def build_report(selected_date):
    snap, _, _, err = current_snapshot()
    scheduled, cases_found = {}, False
    if snap:
        cases_found = snap["cases_col_found"]
        j = snap["journal"]
        sub = j[j["Date"] == selected_date]
        for name, g in sub.groupby("Customer", sort=False):
            tot = g["Cases"].sum(min_count=1)
            scheduled[name] = {"cases": int(tot) if pd.notna(tot) else None,
                               "invoice": _join_unique(g["Invoice"]),
                               "remark": _join_unique(g["Remark"], sep=" / ")}

    pack_info = {}
    df_pack = rows_for_day(read_raw(PACKING_FILE, PACKING_COLS), selected_date)
    for cust, g in df_pack.groupby("Customer", sort=False):
        pack_info[cust] = {"cases": int(g["Cases_Packed"].sum()), "by": g["Prepared_By"].iloc[-1],
                           "status": str(g["Status"].iloc[-1])}

    sent_info = {}
    df_disp = rows_for_day(read_raw(DATA_FILE, DISPATCH_COLS), selected_date)
    for cust, g in df_disp.groupby("Customer", sort=False):
        last = g.iloc[-1]
        station = str(last["Taxi_Station"]).strip()
        driver = f"{last['Local_Driver']} ➡️ {station}" if station not in ("-", "") else str(last["Local_Driver"])
        sent_info[cust] = {"cases": int(g["Cases"].sum()), "driver": driver, "note": str(last["Note"]),
                           "by": str(last["Handled_By"]), "verified": str(last["Verified_By"]), "time": last["Time"]}

    areas = areas_lookup(snap)
    overrides = load_location_overrides()
    assigned = current_assignments(selected_date)
    rows = []
    for cust in set(scheduled) | set(pack_info) | set(sent_info):
        p, s, info = pack_info.get(cust), sent_info.get(cust), scheduled.get(cust)
        area, province, region, _how = resolve_location(cust, areas.get(norm_name(cust)), overrides.get(norm_name(cust)))
        packed = p["cases"] if p else 0
        sent = s["cases"] if s else 0
        ordered = info["cases"] if info else None
        remark = info["remark"] if info else "-"
        target = packed if packed > 0 else (ordered or 0)
        if s:
            status = "🔵 Partial" if (target > 0 and sent < target) else "✅ Sent"
        elif p:
            status = "🟠 Packing" if "In Progress" in p["status"] else "🟡 Ready for Delivery"
        else:
            status = "⏳ Pending"
        urgent = any(w.upper() in remark.upper() for w in URGENT_WORDS)
        rows.append({
            "🔥": "🔥" if urgent else "", "Customer": cust, "Area": AREA_LABEL[area], "Province": province,
            "Region": region, "Invoice": info["invoice"] if info else "-",
            "Status": status, "កេស": ordered,
            "Packed Cases": packed, "Prepared By": p["by"] if p else "-", "Assigned To": assigned.get(cust, "-"),
            "Sent Cases": sent, "Handled By": s["by"] if s else "-",
            "Verified By": s["verified"] if s else "-",
            "Driver/Station": s["driver"] if s else "-", "Journal Note": remark,
            "Note": s["note"] if s else "-", "Time": s["time"] if s else "-",
            "Source": "Journal" if info else "⚠️ Not in journal",
        })
    if not rows:
        return pd.DataFrame(), cases_found, err
    df = pd.DataFrame(rows)
    df["កេស"] = pd.array(df["កេស"].tolist(), dtype="Int64")
    df["_a"] = df["Area"].map(AREA_RANK)
    df["_r"] = df["Status"].map(STATUS_RANK)
    df["_u"] = (df["🔥"] == "").astype(int)
    df = df.sort_values(by=["_a", "_r", "_u", "Customer"]).drop(columns=["_a", "_r", "_u"]).reset_index(drop=True)
    return df[DASH_COLUMNS], cases_found, err


def summarize(df, by):
    """Customers / ordered / packed / sent per group (by = 'Area' | 'Region' | 'Province')."""
    if df.empty:
        return pd.DataFrame()
    g = df.groupby(by, sort=False)
    out = g.agg(Customers=("Customer", "count"),
                Delivered=("Status", lambda x: int((x == "✅ Sent").sum())),
                Partial=("Status", lambda x: int((x == "🔵 Partial").sum())),
                Ordered=("កេស", lambda x: int(x.fillna(0).sum())),
                Packed=("Packed Cases", "sum"), Sent=("Sent Cases", "sum")).reset_index()
    out["Waiting"] = out["Customers"] - out["Delivered"]
    out["% delivered"] = (out["Delivered"] * 100 // out["Customers"].clip(lower=1)).astype(int).astype(str) + "%"
    return out.sort_values("Customers", ascending=False).reset_index(drop=True)


def map_data(df, metric):
    """One row per Cambodian province (all 25 + Phnom Penh) with the chosen number for the map."""
    agg = {}
    if not df.empty:
        part = df[df["Province"].isin(PROVINCES)]
        for prov, g in part.groupby("Province"):
            delivered = int((g["Status"] == "✅ Sent").sum())
            agg[prov] = {"customers": len(g), "waiting": len(g) - delivered, "ordered": int(g["កេស"].fillna(0).sum()),
                         "sent": int(g["Sent Cases"].sum())}
    rows = []
    for prov, (lat, lon, region, _) in PROVINCES.items():
        a = agg.get(prov, {"customers": 0, "waiting": 0, "ordered": 0, "sent": 0})
        value = {"Customers": a["customers"], "Customers still waiting": a["waiting"],
                 "Cases ordered (កេស)": a["ordered"], "Cases sent": a["sent"]}[metric]
        color = REGIONS[region][0]
        rgb = [int(color[i:i + 2], 16) for i in (1, 3, 5)]
        rows.append({"province": prov, "region": region, "lat": lat, "lon": lon, "value": value,
                     "customers": a["customers"], "ordered": a["ordered"], "sent": a["sent"], "waiting": a["waiting"],
                     "radius": 6000 + (value ** 0.5) * 5500, "color": rgb + [210 if value else 90],
                     "hexcolor": color, "label": f"{prov} ({value})" if value else ""})
    return pd.DataFrame(rows)


def render_cambodia_map(df, metric):
    dm = map_data(df, metric)
    legend = "  ".join(f"{emo} {name}" for name, (_, emo) in REGIONS.items() if name != "Unassigned")
    st.caption(legend + "   |   bigger circle = bigger number")
    try:
        import pydeck as pdk
        pts = pdk.Layer("ScatterplotLayer", data=dm, get_position="[lon, lat]", get_radius="radius",
                        get_fill_color="color", pickable=True, stroked=True, get_line_color=[255, 255, 255],
                        line_width_min_pixels=1)
        txt = pdk.Layer("TextLayer", data=dm[dm["value"] > 0], get_position="[lon, lat]", get_text="label",
                        get_size=13, get_color=[20, 20, 20, 255], get_pixel_offset=[0, -16])
        deck = pdk.Deck(layers=[pts, txt], map_provider="carto", map_style="light",
                        initial_view_state=pdk.ViewState(latitude=12.55, longitude=104.9, zoom=5.6, pitch=0),
                        tooltip={"html": "<b>{province}</b><br/>{region}<br/>Customers: {customers} "
                                         "(waiting {waiting})<br/>Ordered: {ordered} | Sent: {sent}"})
        try:
            st.pydeck_chart(deck, width="stretch")
        except Exception:
            st.pydeck_chart(deck, use_container_width=True)
    except Exception:
        try:
            st.map(dm, latitude="lat", longitude="lon", size="radius", color="hexcolor")
        except Exception:
            st.bar_chart(dm.set_index("province")["value"])


STATUS_STYLE = {"✅ Sent": ("#2e7d32", "#ffffff"), "🔵 Partial": ("#1565c0", "#ffffff"),
                "🟡 Ready for Delivery": ("#f9a825", "#222222"), "🟠 Packing": ("#ef6c00", "#ffffff"),
                "⏳ Pending": ("#757575", "#ffffff")}
COMPACT_COLUMNS = ["🔥", "Customer", "Province", "Status", "កេស", "Packed Cases", "Assigned To", "Sent Cases", "Invoice"]
_REGION_ORDER = {r: i for i, r in enumerate(REGIONS)}


def is_mobile():
    try:
        ua = (st.context.headers.get("User-Agent") or "").lower()
        return any(k in ua for k in ("mobile", "android", "iphone", "ipad"))
    except Exception:
        return False


def _e(x):
    return html.escape(str(x), quote=True)


def kpi_strip(counts, total):
    items = [("⏳ Pending", "⏳ Pending"), ("🟠 Packing", "🟠 Packing"), ("🟡 Ready", "🟡 Ready for Delivery"),
             ("🔵 Partial", "🔵 Partial"), ("✅ Sent", "✅ Sent")]
    pills = "".join(f"<span class='hk-pill'>{lab} <b>{int(counts.get(key, 0))}</b></span>" for lab, key in items)
    return f"<div class='hk-kpis'>{pills}<span class='hk-pill'>👥 Total <b>{total}</b></span></div>"


def card_html(r):
    bg, fg = STATUS_STYLE.get(r["Status"], ("#757575", "#ffffff"))
    ordered = "-" if pd.isna(r["កេស"]) else int(r["កេស"])
    inv = f" · 🧾 {_e(r['Invoice'])}" if r["Invoice"] not in ("-", "") else ""
    note = f"<div class='hk-note'>📌 {_e(r['Journal Note'])}</div>" if r["Journal Note"] not in ("-", "") else ""
    sent = ""
    if int(r["Sent Cases"]) > 0:
        sent = (f"<div class='hk-note'>🚚 {_e(r['Handled By'])} · {_e(r['Time'])} · {_e(r['Driver/Station'])}"
                f" · ✅ {_e(r['Verified By'])}</div>")
    prep = f" · 👷 {_e(r['Prepared By'])}" if r["Prepared By"] not in ("-", "") else ""
    asg = f"<span>👤 {_e(r['Assigned To'])}</span>" if r.get("Assigned To") not in ("-", "", None) else ""
    return (f"<div class='hk-card' style='border-left:6px solid {bg}'>"
            f"<div class='hk-top'><span class='hk-name'>{'🔥 ' if r['🔥'] else ''}{_e(r['Customer'])}</span>"
            f"<span class='hk-badge' style='background:{bg};color:{fg}'>{_e(r['Status'])}</span></div>"
            f"<div class='hk-sub'>{_e(r['Area'])} · {_e(r['Province'])}{inv}</div>"
            f"<div class='hk-nums'><span>កេស <b>{ordered}</b></span><span>📦 <b>{int(r['Packed Cases'])}</b>{prep}</span>"
            f"<span>🚚 <b>{int(r['Sent Cases'])}</b></span>{asg}</div>{note}{sent}</div>")


def cards_html(df):
    """Cards grouped by Phnom Penh / province. One string without blank lines, every text escaped."""
    parts, last, counts = [], None, df.groupby(["Area", "Province"]).size().to_dict()
    for r in df.to_dict("records"):
        key = (r["Area"], r["Province"])
        if key != last:
            last = key
            title = r["Area"] if r["Province"] == PP else f"{r['Area']} · {r['Province']}"
            parts.append(f"<div class='hk-group'>{_e(title)} ({counts[key]})</div>")
        parts.append(card_html(r))
    return "".join(parts)


def render_cards(df):
    page = 30
    limit = st.session_state.get("card_limit", page)
    d = df.copy()
    d["_a"] = d["Area"].map(AREA_RANK)
    d["_g"] = d["Region"].map(_REGION_ORDER).fillna(99)
    d["_s"] = d["Status"].map(STATUS_RANK)
    d = d.sort_values(["_a", "_g", "Province", "_s", "Customer"]).drop(columns=["_a", "_g", "_s"])
    st.markdown(cards_html(d.head(limit)), unsafe_allow_html=True)
    st.caption(f"Showing {min(limit, len(d))} of {len(d)} customers")
    if len(d) > limit and st.button(f"⬇️ Show {page} more", key="card_more"):
        st.session_state["card_limit"] = limit + page
        try:
            st.rerun(scope="fragment")
        except TypeError:
            st.rerun()


def _dashboard_body():
    can_edit = current_role() in ("staff", "admin")
    mobile = is_mobile()
    st.markdown("### 📊 Master Status Board")
    selected_date = st.date_input("Select Report Date:", value=today_kh(), key="dash_date")
    df_report, cases_found, err = build_report(selected_date)
    if err:
        st.warning(f"Excel problem: {err}")
    if df_report.empty:
        st.info(f"📅 No orders scheduled or found in the journal for {selected_date}.")
        return

    # ---- Phnom Penh / Province view ----
    area_options = ["All", AREA_LABEL[PP], AREA_LABEL["Province"]]
    if (df_report["Area"] == AREA_LABEL["Unknown"]).any():
        area_options.append(AREA_LABEL["Unknown"])
    view = st.radio("Show", area_options, horizontal=True, key="dash_area")
    df_scope = df_report if view == "All" else df_report[df_report["Area"] == view].reset_index(drop=True)
    if df_scope.empty:
        st.info("No customers in this view for the selected date.")
        return

    counts = df_scope["Status"].value_counts()
    total, n_sent = len(df_scope), int(counts.get("✅ Sent", 0))
    st.markdown(kpi_strip(counts, total), unsafe_allow_html=True)
    try:
        st.progress(n_sent / total, text=f"Delivered {n_sent} of {total} customers ({n_sent * 100 // total}%)")
    except TypeError:
        st.progress(n_sent / total)

    with st.expander("📊 Summary: Phnom Penh vs Province, regions and provinces", expanded=not mobile):
        t_area, t_region, t_prov = st.tabs(["By area", "By delivery region", "By province"])
        with t_area:
            show_df(summarize(df_report, "Area"))
        with t_region:
            show_df(summarize(df_scope, "Region"))
        with t_prov:
            show_df(summarize(df_scope, "Province"))
    with st.expander("🗺️ Map of Cambodia", expanded=not mobile):
        metric = st.radio("Circle size shows", ["Customers", "Customers still waiting", "Cases ordered (កេស)", "Cases sent"],
                          horizontal=True, key="map_metric")
        render_cambodia_map(df_scope, metric)

    # ---- search + display style ----
    c1, c2, c3 = st.columns([3, 2, 2])
    q = c1.text_input("🔎 Search customer or invoice", key="dash_q", max_chars=60)
    display = c2.radio("Display", ["📱 Cards", "🖥️ Table"], horizontal=True, index=0 if mobile else 1, key="dash_display")
    with c3:
        st.write("")
        try:
            buf = io.BytesIO()
            with pd.ExcelWriter(buf, engine="openpyxl") as writer:
                df_report.to_excel(writer, index=False, sheet_name="Master_Status")
            st.download_button("📥 Download report (Excel)", data=buf.getvalue(),
                               file_name=f"Master_Report_{selected_date}.xlsx",
                               mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
        except Exception as e:
            st.warning(f"Could not build Excel report: {e}")

    with st.expander("🎚️ Filters: status, region, province"):
        pick_status = st.multiselect("Status filter", list(STATUS_RANK), key="dash_status", placeholder="All statuses")
        pick_region = st.multiselect("Region filter", [r for r in REGIONS if r in set(df_scope["Region"])],
                                     key="dash_region", placeholder="All regions")
        pick_prov = st.multiselect("Province filter", sorted(set(df_scope["Province"])), key="dash_prov",
                                   placeholder="All provinces")

    df_view = df_scope
    if pick_region:
        df_view = df_view[df_view["Region"].isin(pick_region)]
    if pick_prov:
        df_view = df_view[df_view["Province"].isin(pick_prov)]
    if q.strip():
        qq = q.strip()
        m = (df_view["Customer"].str.contains(qq, case=False, regex=False, na=False)
             | df_view["Invoice"].str.contains(qq, case=False, regex=False, na=False))
        df_view = df_view[m]
    if pick_status:
        df_view = df_view[df_view["Status"].isin(pick_status)]
    df_view = df_view.reset_index(drop=True)

    if not cases_found:
        st.caption(f"ℹ️ No column '{JOURNAL_CASES_HEADER}' found in the journal, so ordered cases are empty. "
                   "Change JOURNAL_CASES_HEADER at the top of the file if your header is different.")
    if st.session_state.pop("clear_sel", False):
        st.session_state.pop("dash_table", None)

    event = None
    table_mode = display.endswith("Table")
    if df_view.empty:
        st.info("No customers match your search / filter.")
    elif table_mode:
        all_cols = st.checkbox("Show all columns", key="dash_allcols")
        if can_edit:
            st.caption("👆 Click a row to update it (who prepared, packing cases, who delivered, verify cases).")
        cfg = {
            "🔥": st.column_config.TextColumn("🔥", width="small"),
            "Customer": st.column_config.TextColumn("Customer", width="large"),
            "Area": st.column_config.TextColumn("Area", width="medium"),
            "Province": st.column_config.TextColumn("Province", width="medium"),
            "Region": st.column_config.TextColumn("Region", width="medium"),
            "Invoice": st.column_config.TextColumn("Invoice", width="medium"),
            "Status": st.column_config.TextColumn("Status", width="medium"),
        }
        cols = DASH_COLUMNS if all_cols else COMPACT_COLUMNS
        event = show_df(df_view[cols], height=430, key="dash_table", selectable=can_edit, column_config=cfg)
    else:
        render_cards(df_view)

    if not can_edit:
        return
    if event is None:                                   # cards view (or an old Streamlit): pick from a list
        status_of = dict(zip(df_view["Customer"], df_view["Status"]))
        pick = st.selectbox("✏️ Update a customer (type to search)", ["--"] + df_view["Customer"].tolist()[:400],
                            format_func=lambda c: c if c == "--" else f"{status_of.get(c, '')}  {c}", key="pick_old")
        if pick != "--":
            st.session_state["sel_cust"] = pick
        else:
            st.session_state.pop("sel_cust", None)
    else:
        rows_sel = event.selection.rows
        if rows_sel:
            st.session_state["sel_cust"] = df_view.iloc[rows_sel[0]]["Customer"]

    selected = st.session_state.get("sel_cust")
    if selected not in set(df_report["Customer"]):
        return

    st.markdown("---")
    h1, h2 = st.columns([5, 1])
    h1.subheader(f"✏️ Update: {selected}")
    if h2.button("✖ Close", key="close_panel"):
        st.session_state.pop("sel_cust", None)
        st.session_state["clear_sel"] = True
        st.rerun()

    if selected_date != today_kh():
        st.info("Updates can only be saved for today. Select today's date above.")
        return

    p_row = df_report[df_report["Customer"] == selected].iloc[0]
    ordered_n = int(p_row["កេស"]) if pd.notna(p_row["កេស"]) else None
    packed_n, sent_n = int(p_row["Packed Cases"]), int(p_row["Sent Cases"])
    target_n = packed_n if packed_n > 0 else (ordered_n or 0)
    st.info(f"📍 {p_row['Area']} - {p_row['Province']} ({p_row['Region']})  |  Status: **{p_row['Status']}**  |  "
            f"Invoice: {p_row['Invoice']}  |  កេស ordered: {ordered_n if ordered_n is not None else '-'}  |  "
            f"Packed: {packed_n} (by {p_row['Prepared By']})  |  Sent: {sent_n} (by {p_row['Handled By']}, "
            f"verified by {p_row['Verified By']})")
    if p_row["Journal Note"] not in ("-", ""):
        st.warning(f"📌 Journal note: {p_row['Journal Note']}")
    pack_default = max((ordered_n or 0) - packed_n, 0) or 1
    send_default = (target_n - sent_n) if (target_n - sent_n) > 0 else 1

    t_pack, t_send = st.tabs(["📦 Step 1: Packing (who prepared the buns)",
                              "🚚 Step 2: Send (who delivered + verify កេស)"])
    with t_pack:
        packing_form(f"dash_pack_{selected}_{pack_default}", fixed_customer=selected, default_cases=pack_default)
    with t_send:
        st.caption("Check the កេស number (you can edit it), choose who verified it, then save.")
        dispatch_form(f"dash_send_{selected}_{send_default}", fixed_customer=selected,
                      default_cases=send_default, verify=True)


def tab_dashboard(live):
    def _run():
        safe_render(_dashboard_body, "Dashboard")
    frag = st.fragment(run_every=LIVE_REFRESH_SECONDS)(_run) if live else st.fragment(_run)
    frag()


# ==========================================
# TAB: HEALTH BOT + SECURITY (admin only)
# ==========================================
def _locations_panel():
    st.markdown("### 📍 Customer locations (Phnom Penh / Province)")
    snap, _, _, err = current_snapshot()
    if not snap:
        st.info(f"The journal is not loaded: {err}")
        return
    areas, overrides = areas_lookup(snap), load_location_overrides()
    names = sorted(set(snap["customers"]) | set(snap["journal"]["Customer"]))
    rows = []
    for n in names:
        area, prov, region, how = resolve_location(n, areas.get(norm_name(n)), overrides.get(norm_name(n)))
        rows.append((n, AREA_LABEL[area], prov, region, how))
    df = pd.DataFrame(rows, columns=["Customer", "Area", "Province", "Region", "How we know"])
    unknown = df["Province"].isin(["Unknown province", "Unknown"])
    st.caption(f"{int((~unknown).sum())} of {len(df)} customers have a known place. "
               f"{int(unknown.sum())} still need a province - pick it below and save, the app remembers it.")
    if not snap.get("area_col_found"):
        st.warning("No Province / Phnom Penh column was found in the Master List, so the places come from the customer names only.")
    mode = st.radio("Show", ["Only unknown", "Guessed from a town name (please check)", "Set by admin", "All"],
                    horizontal=True, key="loc_show")
    if mode == "Only unknown":
        sub = df[unknown]
    elif mode.startswith("Guessed"):
        sub = df[df["How we know"].str.startswith("town name")]
    elif mode == "Set by admin":
        sub = df[df["How we know"] == "set by admin"]
    else:
        sub = df
    q = st.text_input("🔎 Search customer", key="loc_q", max_chars=60)
    if q.strip():
        sub = sub[sub["Customer"].str.contains(q.strip(), case=False, regex=False, na=False)]
    sub = sub.head(300).copy()
    sub["Set province"] = ""
    choices = [""] + sorted(PROVINCES) + ["↩ remove my setting"]
    edited = st.data_editor(
        sub, hide_index=True, height=360, key="loc_editor",
        disabled=["Customer", "Area", "Province", "Region", "How we know"],
        column_config={"Set province": st.column_config.SelectboxColumn(
            "Set province", options=choices, help="Choose the province of this customer, then press Save.")})
    if st.button("💾 Save locations", key="loc_save", type="primary"):
        picked = {r["Customer"]: r["Set province"] for _, r in edited.iterrows() if r["Set province"]}
        if not picked:
            st.info("Nothing selected. Choose a province in the 'Set province' column first.")
        else:
            def _apply(cur):
                for cust, prov in picked.items():
                    if prov.startswith("↩"):
                        cur.pop(cust, None)
                    elif prov in PROVINCES:
                        cur[cust] = prov
                return cur
            try:
                modify_locations(_apply)
                audit("locations_set", f"{len(picked)} customers")
                flash_and_refresh(f"Saved {len(picked)} customer locations")
            except (RuntimeError, ConflictError) as err2:
                st.error(f"❌ {err2}")


def _users_panel():
    st.markdown("### 👥 Users & Security")
    try:
        users = load_users()
    except Exception as e:
        st.error(f"Cannot load accounts: {e}")
        return
    me = current_user()
    shown = st.session_state.pop("show_pw", None)
    if shown:
        st.success(f"Temporary password for **{shown[0]}**: `{shown[1]}`  - give it to the person. "
                   "They must choose their own password at the first login. This message appears only once.")
    show_df(pd.DataFrame([{
        "Username": u, "Role": r.get("role"), "Active": "yes" if r.get("active", True) else "NO",
        "Starter password": "yes" if r.get("must_change") else "",
        "Last login": r.get("last_login", ""), "Password changed": r.get("pw_changed", "")}
        for u, r in sorted(users.items())]))

    with st.expander("➕ Add a user"):
        with st.form("add_user_form", clear_on_submit=True):
            nu = st.text_input("Username (3-30 letters/numbers, for example: sokha)", max_chars=30)
            nr = st.selectbox("Role", ROLES, help="staff = packing, delivery, dashboard | viewer = dashboard only | admin = everything")
            npw = st.text_input("Temporary password (leave empty to generate one)", max_chars=100)
            if st.form_submit_button("Create user", type="primary"):
                uname = nu.strip().lower()
                pw = npw.strip() or generate_password()
                if not USERNAME_RE.match(uname):
                    st.error("❌ Username: 3-30 characters, only a-z, 0-9, dot, dash, underscore.")
                elif npw.strip() and password_problem(pw, uname):
                    st.error(f"❌ {password_problem(pw, uname)}")
                else:
                    def _add(u):
                        if uname in u:
                            raise ValueError("That username already exists.")
                        u[uname] = _new_user(nr, pw, must_change=True)
                        return u
                    try:
                        modify_users(_add)
                        audit("user_added", f"{uname} ({nr})")
                        st.session_state["show_pw"] = (uname, pw)
                        flash_and_refresh(f"User {uname} created")
                    except (ValueError, RuntimeError, ConflictError) as err:
                        st.error(f"❌ {err}")

    with st.expander("🔁 Reset password / disable / delete a user"):
        names = sorted(users)
        who = st.selectbox("User", names, key="mng_user")
        tpw = st.text_input("New temporary password (leave empty to generate one)", max_chars=100, key="mng_pw")
        c1, c2, c3 = st.columns(3)
        act = None
        if c1.button("🔁 Reset password", key="mng_reset"):
            act = "reset"
        is_active = users.get(who, {}).get("active", True)
        if c2.button("⏸️ Disable" if is_active else "▶️ Enable", key="mng_toggle"):
            act = "toggle"
        if c3.button("🗑️ Delete user", key="mng_delete"):
            act = "delete"
        if act:
            def _others_have_admin(u):
                return any(r.get("role") == "admin" and r.get("active", True) for n, r in u.items() if n != who)

            def _manage(u):
                if who not in u:
                    raise ValueError("That user no longer exists.")
                if act in ("toggle", "delete") and who == me:
                    raise ValueError("You cannot disable or delete your own account.")
                if act in ("toggle", "delete") and u[who].get("role") == "admin" and u[who].get("active", True) \
                        and not _others_have_admin(u):
                    raise ValueError("At least one active admin must remain.")
                if act == "reset":
                    pw = tpw.strip() or generate_password()
                    prob = password_problem(pw, who) if tpw.strip() else None
                    if prob:
                        raise ValueError(prob)
                    u[who].update(_hash_pw(pw))
                    u[who]["must_change"] = True
                    st.session_state["show_pw"] = (who, pw)
                elif act == "toggle":
                    u[who]["active"] = not u[who].get("active", True)
                elif act == "delete":
                    u.pop(who)
                return u
            try:
                modify_users(_manage)
                audit({"reset": "password_reset", "toggle": "user_toggled", "delete": "user_deleted"}[act], who)
                flash_and_refresh(f"Done: {act} {who}")
            except (ValueError, RuntimeError, ConflictError) as err:
                st.error(f"❌ {err}")

    show_df(pd.DataFrame([
        ("Login", "username + password for everyone"),
        ("Password storage", "scrambled (PBKDF2-SHA256) in users.json - nobody can read them, not even you"),
        ("Password rule", "at least 8 characters, letters and numbers"),
        ("Wrong-password attempts (24h)", str(failed_logins(24))),
        ("Lock-out", f"{MAX_FAILS} wrong attempts -> locked {LOCKOUT_MIN} minutes"),
        ("Auto log-out", f"after {LOGIN_TTL_HOURS} hours"),
        ("Forgot the admin password?", "delete users.json from the data folder: the starter admin account comes back"),
    ], columns=["Setting", "Value"]))


def _bot_body():
    if current_role() != "admin":
        st.info("🔒 Admin only.")
        return
    st.markdown("### 🤖 Health Bot")
    st.caption(f"The bot checks files, names, backups and the Excel journal by itself every {BOT_INTERVAL_MIN} minutes "
               "and repairs what is safe to repair. Every repair is written to the log and a backup is kept.")

    st.info(("☁️ Online mode: data is stored in Dropbox folder " + DROPBOX_FOLDER) if USE_DROPBOX
            else "💻 Local mode: data is stored in the app folder on this computer")
    c1, c2, c3 = st.columns(3)
    if c1.button("🔧 Check & fix now", key="bot_fix"):
        auto_bot.clear()
    only_check = c2.button("👀 Check only (change nothing)", key="bot_check")
    if c3.button("🧹 Clear cache & re-sync Dropbox", key="bot_cache"):
        resync_now()
        try:
            os.remove(os.path.join(CACHE_DIR, "excel_snapshot.pkl"))
        except OSError:
            pass
        st.toast("Cache cleared - everything will be re-read", icon="🧹")

    if only_check:
        findings, suggestions = run_health_check(auto_fix=False)
        st.markdown("**Result (nothing was changed):**")
    else:
        findings, suggestions = auto_bot()
        st.markdown("**Latest automatic check:**")
    show_df(pd.DataFrame(findings))

    if suggestions:
        st.markdown("**Names that look like typos (the bot suggests the Master List name):**")
        show_df(pd.DataFrame(suggestions, columns=["File", "Name in file", "Suggested name"]))
        if st.button("✨ Apply all suggested names", key="bot_apply"):
            apply_name_fixes(suggestions)
            auto_bot.clear()
            flash_and_refresh("Customer names corrected")

    st.markdown("---")
    _locations_panel()
    st.markdown("---")
    _users_panel()

    st.markdown("**🕵️ Audit log (logins, saves, edits, deletes)**")
    try:
        if USE_DROPBOX:
            _log_pull_once(AUDIT_FILE)
            _log_pull_once(BOT_LOG_FILE)
        if os.path.exists(AUDIT_FILE):
            alog = pd.read_csv(AUDIT_FILE, encoding="utf-8-sig").tail(60).iloc[::-1]
            show_df(alog, height=300)
            with open(AUDIT_FILE, "rb") as fh:
                st.download_button("📥 Download audit log", data=fh.read(), file_name="audit_log.csv", mime="text/csv")
        else:
            st.info("No activity recorded yet.")
    except Exception as e:
        st.warning(f"Could not read audit log: {e}")

    st.markdown("**📜 What the bot did recently**")
    try:
        if os.path.exists(BOT_LOG_FILE):
            log = pd.read_csv(BOT_LOG_FILE, encoding="utf-8-sig").tail(40).iloc[::-1]
            show_df(log, height=260)
        else:
            st.info("The bot has not needed to fix anything yet.")
    except Exception as e:
        st.warning(f"Could not read bot log: {e}")


@st.fragment
def tab_bot():
    safe_render(_bot_body, "Bot tab")


# ==========================================
# APP LAYOUT
# ==========================================
st.set_page_config(page_title="Delivery Operations", page_icon="🚚", layout="wide",
                   initial_sidebar_state="collapsed")
st.markdown(CSS, unsafe_allow_html=True)

ROLE = require_login()                     # nothing below runs until the person is logged in

_flash = st.session_state.pop("flash", None)
if _flash:
    st.toast(_flash, icon="✅")

USER = current_user()
with st.sidebar:
    st.markdown(f"### 👤 {USER}")
    st.caption(f"{ROLE_LABEL.get(ROLE, ROLE)} | auto log-out after {LOGIN_TTL_HOURS} h")
    with st.expander("🔑 Change my password"):
        with st.form("chg_pw_form", clear_on_submit=True):
            _c = st.text_input("Current password", type="password", max_chars=100)
            _n1 = st.text_input("New password", type="password", max_chars=100)
            _n2 = st.text_input("New password again", type="password", max_chars=100)
            if st.form_submit_button("Save new password"):
                _err = change_password(USER, _c, _n1, _n2)
                if _err:
                    st.error(f"❌ {_err}")
                else:
                    st.session_state["flash"] = "Password changed"
                    st.rerun()
        st.caption("At least 8 characters, letters and numbers.")
    if st.button("🚪 Log out", key="logout_btn"):
        logout("manual")
        st.rerun()

st.title("🚚 នំប៉ាវហុងកុង Supply Chain Hub")

daily_backup_once(today_kh().strftime("%Y-%m-%d"))
_snap, _src, _xl, _err = current_snapshot()
_file_text = f"📄 {os.path.basename(_xl)}" if (_xl and not _err) else "📄 journal problem"
_chips = f"{'☁️ Dropbox' if USE_DROPBOX else '💻 Local'}  |  {_file_text}  |  🕒 {now_kh():%Y-%m-%d %I:%M %p}"
if ROLE in ("staff", "admin"):
    _findings, _ = auto_bot()
    _fixed = sum(1 for f in _findings if f["Level"] == LEVEL_ICON["fixed"])
    _bad = sum(1 for f in _findings if f["Level"] in (LEVEL_ICON["warn"], LEVEL_ICON["error"]))
    if ROLE == "admin":
        _chips += "  |  " + ("🤖 Bot: all good" if (_fixed == 0 and _bad == 0)
                             else f"🤖 Bot: {_fixed} fixed, {_bad} need a look (see Bot tab)")
st.caption(_chips)

if ROLE == "viewer":
    labels = ["📊 Live Dashboard (Sales)"]
elif ROLE == "staff":
    labels = ["📦 1. Packing Progress (Prep)", "🚚 2. Log Delivery (Ops)", "📊 3. Live Dashboard (Sales)"]
else:
    labels = ["📦 1. Packing Progress (Prep)", "🚚 2. Log Delivery (Ops)", "📊 3. Live Dashboard (Sales)",
              "🤖 4. Admin: Bot, Users & Security"]
_tabs = dict(zip(labels, st.tabs(labels)))

for _label, _tab in _tabs.items():
    with _tab:
        if _label.startswith("📦"):
            tab_packing()
        elif _label.startswith("🚚"):
            tab_dispatch()
        elif _label.startswith("📊"):
            _live = st.checkbox(f"🔄 Live mode (refresh every {LIVE_REFRESH_SECONDS}s)", value=False, key="live_mode")
            tab_dashboard(_live)
        else:
            tab_bot()
