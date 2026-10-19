# ============================================================
#  នំប៉ាវហុងកុង Supply Chain Hub  -  v3: fast, secure, self-healing
#  Run: python -m streamlit run app_reviewed_custom_permissions.py
#  Reviewed: batched selections, independent drafts, strict data checks and atomic saves.
# ============================================================
"""Delivery Operations — reviewed reliability update.

Run: python -m streamlit run app_reviewed_custom_permissions.py
Dependencies: streamlit>=1.37, pandas, openpyxl, xlsxwriter; dropbox for online mode.
Existing users.json accounts remain valid. For a NEW installation, configure a
unique INITIAL_ADMIN_PASSWORD in Streamlit secrets or the server environment,
then sign in as admin and change it. There is no shared starter password.
Ambiguous text dates follow DAYFIRST (True = day/month/year); prefer ISO dates.
The Health Bot runs with an active app session, not as an unattended service.
It preserves damaged records and uncertain duplicates for manual review.
Customer Map includes the supplied NPHK leads as separate location records.
Map corrections are stored in customer_map_registry.json, including Dropbox mode.
"""
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
import math
import logging
import urllib.parse
import urllib.request
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
_APP_SCOPE = hashlib.sha256((CURRENT_DIR + "|" + DROPBOX_FOLDER).encode()).hexdigest()[:16]
DATA_DIR = os.path.join(tempfile.gettempdir(), "hk_supply_hub_data_" + _APP_SCOPE) if USE_DROPBOX else CURRENT_DIR
os.makedirs(DATA_DIR, exist_ok=True)
DATA_FILE = os.path.join(DATA_DIR, "daily_delivery_expenses.csv")
PACKING_FILE = os.path.join(DATA_DIR, "daily_packing_progress.csv")
BACKUP_DIR = os.path.join(CURRENT_DIR, "backups")                 # local mode only (Dropbox mode: <folder>/backups)
BOT_LOG_FILE = os.path.join(DATA_DIR, "bot_log.csv")
AUDIT_FILE = os.path.join(DATA_DIR, "audit_log.csv")
REMEMBER_FILE = os.path.join(DATA_DIR, "remember_tokens.json")     # "keep me logged in" tokens (only a hash is stored)
USERS_FILE = os.path.join(DATA_DIR, "users.json")          # accounts (passwords are stored hashed, never as text)
ASSIGN_FILE = os.path.join(DATA_DIR, "delivery_assignments.csv")   # who will deliver which customer today
HOLD_FILE = os.path.join(DATA_DIR, "customer_holds.csv")           # customers moved to tomorrow / cancelled
MAP_REGISTRY_FILE = os.path.join(DATA_DIR, "customer_map_registry.json")
LOCATIONS_FILE = os.path.join(DATA_DIR, "customer_locations.csv")   # provinces that the admin set by hand
LOG_PUSH_DELAY = 10                                                # seconds before logs are copied to Dropbox
CACHE_DIR = os.path.join(tempfile.gettempdir(), "hk_supply_hub_cache_" + _APP_SCOPE)       # outside Dropbox = faster

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
REMEMBER_DAYS = 30                     # "Keep me logged in" lasts this long (renews every time the person comes back)
COOKIE_TOKEN, COOKIE_USER = "hk_remember", "hk_user"
LOGIN_TTL_HOURS = 12                   # automatic log-out after this many hours
MAX_FAILS = 5                          # wrong codes before a temporary lock-out
LOCKOUT_MIN = 5                        # lock-out length (minutes)
MAX_CASES = 10000
MAX_RIEL = 50_000_000
MAX_TEXT = 200

LOCAL_DRIVERS = ["ងិន វុទ្ធា", "អួន តួ"]
OPS_STAFF = ["ឆែម សំណុក", "សាយ ប៊ុនលី", "ប៉ៅ រីណា", "ពេជ រដ្ឋា", "រ៉ូ សុវណ្ណាឌែន", "ហេង រតនា", "កង សៀន", "ណាត ផានិត"]
# Sales staff can verify case counts before an order is dispatched. They are not delivery handlers.
SALES_STAFF = ["ចែម សារី", "ឃួន សុលីសា", "ថា សុខម៉េង", "ណាង សុបញ្ញា"]
VERIFY_STAFF = OPS_STAFF + SALES_STAFF
# Delivery drivers can also own, claim, send, and review their delivery tasks.
DELIVERY_HANDLERS = OPS_STAFF + LOCAL_DRIVERS

DISPATCH_COLS = ["Date", "Handled_By", "Customer", "Cases", "Local_Driver",
                 "Taxi_Station", "Phnom_Penh_Expense", "Taxi_Expense", "Note", "Verified_By", "Expense_Status"]
DISPATCH_NUM_COLS = ["Cases", "Phnom_Penh_Expense", "Taxi_Expense"]
PACKING_COLS = ["Date", "Prepared_By", "Customer", "Cases_Packed", "Status"]
ASSIGN_COLS = ["Date", "Handler", "Customer", "Action"]
HOLD_COLS = ["Date", "Customer", "Action", "Cases", "Reason", "By"]   # Action: Tomorrow | Cancel | Restore
HOLD_NUM_COLS = ["Cases"]
ST_MOVED, ST_CANCEL = "📅 Moved to tomorrow", "❌ Cancelled"
IGNORE_NEW = ["STAFF", "GENERAL"]            # names that are not real customers: never reported as "new"
NOT_TO_SEND = ("✅ Sent", ST_MOVED, ST_CANCEL)
PACKING_NUM_COLS = ["Cases_Packed"]
NUM_COLS_ALL = set(DISPATCH_NUM_COLS + PACKING_NUM_COLS + HOLD_NUM_COLS)
FILES = {
    "dispatch": (DATA_FILE, DISPATCH_COLS, DISPATCH_NUM_COLS, "Dispatch CSV"),
    "packing": (PACKING_FILE, PACKING_COLS, PACKING_NUM_COLS, "Packing CSV"),
    "assign": (ASSIGN_FILE, ASSIGN_COLS, [], "Assignments CSV"),
    "holds": (HOLD_FILE, HOLD_COLS, HOLD_NUM_COLS, "Moved / cancelled CSV"),
}

STATUS_RANK = {"✅ Sent": 1, "🔵 Part sent": 2, "🟡 Ready for Delivery": 3, "🟠 Packing": 4, "⏳ Pending": 5,
               "📅 Moved to tomorrow": 6, "❌ Cancelled": 7}
ROLE_LABEL = {"admin": "Admin", "staff": "Staff", "sales": "Sales (dashboard/report)", "viewer": "Viewer (read-only)"}
PERMISSION_LABELS = {
    "tasks": "Task access (Packing + Delivery)",
    "view": "View dashboard and task details",
    "edit": "Create, edit, and submit changes",
    "reports": "Reports, summaries, and report exports",
}
DEFAULT_PERMISSIONS_BY_ROLE = {
    "admin": {"tasks": True, "view": True, "edit": True, "reports": True},
    "staff": {"tasks": True, "view": True, "edit": True, "reports": True},
    "sales": {"tasks": False, "view": True, "edit": False, "reports": True},
    "viewer": {"tasks": False, "view": True, "edit": False, "reports": True},
}
PERMISSION_KEYS = tuple(PERMISSION_LABELS)


def default_permissions(role):
    """Copy the baseline capabilities for a role; per-user choices can override them."""
    return dict(DEFAULT_PERMISSIONS_BY_ROLE.get(role, DEFAULT_PERMISSIONS_BY_ROLE["viewer"]))


def effective_permissions(username=None, rec=None):
    """Return saved permissions overlaid on role defaults. Admin accounts always retain full access."""
    who = username or current_user()
    if rec is None:
        try:
            rec = load_users().get(who, {}) if who else {}
        except Exception:
            rec = {}
    role = str((rec or {}).get("role") or (current_role() if who == current_user() else "viewer"))
    if role == "admin":
        return {k: True for k in PERMISSION_KEYS}
    result = default_permissions(role)
    saved = (rec or {}).get("permissions", {})
    if isinstance(saved, dict):
        for key in PERMISSION_KEYS:
            if key in saved:
                result[key] = bool(saved[key])
    return result


def has_permission(permission, username=None):
    """Check an individual capability. Unknown permissions fail closed."""
    if permission not in PERMISSION_KEYS:
        return False
    who = username or current_user()
    if not who:
        return False
    if who == current_user():
        role = current_role()
        if role == "admin":
            return True
        saved = st.session_state.get("user_permissions", {})
        if isinstance(saved, dict):
            result = default_permissions(role)
            for key in PERMISSION_KEYS:
                if key in saved:
                    result[key] = bool(saved[key])
            return bool(result.get(permission, False))
    try:
        return bool(effective_permissions(who).get(permission, False))
    except Exception:
        return False


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
    """Parse consistently; ambiguous text follows DAYFIRST, never today's date.
    Offset-aware timestamps are converted to Cambodia local wall time for CSV filters.
    """
    if v is None or (not isinstance(v, (str, date, datetime)) and pd.isna(v)):
        return pd.NaT
    if isinstance(v, (datetime, pd.Timestamp, date)):
        t = pd.Timestamp(v)
    else:
        text = str(v).strip()
        if not text or text.lower() in ("nan", "nat", "-", "none"):
            return pd.NaT
        iso = bool(re.match(r"^\d{4}[-/]\d{1,2}[-/]\d{1,2}", text))
        t = _try_parse(text, False if iso else DAYFIRST)
        if t is None:
            return pd.NaT
    if pd.isna(t):
        return pd.NaT
    return t.tz_convert(TZ).tz_localize(None) if t.tzinfo is not None else t


def parse_dates(series):
    """Use one stable parser for mixed timestamps, including timezone offsets."""
    return pd.to_datetime(series.map(parse_dt), errors="coerce")


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
    if not os.path.exists(LOCATIONS_FILE):
        return pd.DataFrame(columns=["Customer", "Province"])
    try:
        frame = _read_csv_strict(LOCATIONS_FILE)
        if not {"Customer", "Province"} <= set(frame.columns):
            raise ValueError("missing Customer or Province column")
        return frame
    except Exception as e:
        raise RuntimeError("Customer locations cannot be read safely; original file preserved.") from e


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
            with _sync_state()["lock"], file_lock(LOCATIONS_FILE):
                if USE_DROPBOX:
                    pull(LOCATIONS_FILE, force=True)
                df = _read_loc_df()
                cur = {}
                if {"Customer", "Province"} <= set(df.columns):
                    cur = {str(c).strip(): str(p).strip() for c, p in zip(df["Customer"], df["Province"]) if str(c).strip()}
                new = fn(cur)
                out = pd.DataFrame(sorted(new.items()), columns=["Customer", "Province"])
                _write_atomic(LOCATIONS_FILE, out.to_csv(index=False).encode("utf-8-sig"))
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
        with file_lock(path):
            existing = os.path.exists(path) and os.path.getsize(path) > 0
            with open(path, "a", newline="", encoding="utf-8-sig") as f:
                writer = csv.writer(f)
                if not existing:
                    writer.writerow(cols)
                writer.writerow([safe_text(v, 2000) for v in row])
            if os.path.getsize(path) > max_bytes:
                with open(path, "r", newline="", encoding="utf-8-sig") as f:
                    entries = list(csv.reader(f))
                buffer = io.StringIO(newline="")
                writer = csv.writer(buffer)
                writer.writerow(cols)
                writer.writerows(entries[1:][-keep:])
                _write_atomic(path, buffer.getvalue().encode("utf-8-sig"))
        if USE_DROPBOX:
            _schedule_log_push(path)
    except Exception:
        logging.getLogger(__name__).exception("Could not persist application log %s", os.path.basename(path))


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
DEFAULT_ADMIN_PW = ""  # New installations must supply INITIAL_ADMIN_PASSWORD in secrets/environment.
USERNAME_RE = re.compile(r"^[a-z0-9._-]{3,30}$")
COMMON_PW = {"password", "password1", "12345678", "123456789", "qwerty123", "admin123", "hk2026", "staff2026",
             "hk-admin-7q4mw2", "hk-staff-3rn8zp", "change-me-admin-9x", "11111111", "abcd1234"}
ROLES = ["staff", "sales", "viewer", "admin"]

# Short, English usernames supplied by the business owner. Aliases allow Admin
# to rename earlier account IDs safely while preserving password hashes/roles.
STAFF_ACCOUNT_SPECS = (
    {"username": "somnok", "legacy_usernames": ["samnuk", "ops01"], "name": "ឆែម សំណុក", "role": "staff"},
    {"username": "bunly", "legacy_usernames": ["ops02"], "name": "សាយ ប៊ុនលី", "role": "staff"},
    {"username": "rina", "legacy_usernames": ["ops03"], "name": "ប៉ៅ រីណា", "role": "staff"},
    {"username": "rotha", "legacy_usernames": ["ratha", "ops04"], "name": "ពេជ រដ្ឋា", "role": "staff"},
    {"username": "den", "legacy_usernames": ["sovann", "ops05"], "name": "រ៉ូ សុវណ្ណាឌែន", "role": "staff"},
    {"username": "ratana", "legacy_usernames": ["ops06"], "name": "ហេង រតនា", "role": "staff"},
    {"username": "sien", "legacy_usernames": ["ops07"], "name": "កង សៀន", "role": "staff"},
    {"username": "nith", "legacy_usernames": ["panit", "ops08"], "name": "ណាត ផានិត", "role": "staff"},
    {"username": "vuthea", "legacy_usernames": ["vutha", "delivery1"], "name": "ងិន វុទ្ធា", "role": "staff"},
    {"username": "tuo", "legacy_usernames": ["tou", "delivery2"], "name": "អួន តួ", "role": "staff"},
    {"username": "sary", "legacy_usernames": ["sales01"], "name": "ចែម សារី", "role": "sales"},
    {"username": "lisa", "legacy_usernames": ["solisa", "sales02"], "name": "ឃួន សុលីសា", "role": "sales"},
    {"username": "sokmeng", "legacy_usernames": ["sales03"], "name": "ថា សុខម៉េង", "role": "sales"},
    {"username": "panha", "legacy_usernames": ["sopanha", "sales04"], "name": "ណាង សុបញ្ញា", "role": "sales"},
)


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


def generate_easy_password(username=""):
    """Create a reasonably memorable, unique temporary password for first login."""
    words = ("Mango", "River", "Lotus", "Tiger", "Coffee", "Orange", "Bamboo", "Dragon",
             "Panda", "Coconut", "Silver", "Forest", "Golden", "Rocket", "Cedar", "Happy",
             "Market", "Sunrise", "Velvet", "Lucky", "Jasmine", "Sunset", "Temple", "Bluebird")
    for _ in range(100):
        pw = pysecrets.choice(words) + str(pysecrets.randbelow(9000) + 1000)
        if not password_problem(pw, username):
            return pw
    return generate_password()


def staff_name_for_user(username=None):
    """Return the linked Khmer staff name for this login, if a bulk-created account has one."""
    uname = username or current_user()
    if not uname:
        return ""
    try:
        rec = load_users().get(uname, {})
        return str(rec.get("staff_name") or "").strip()
    except Exception:
        return ""


def _new_user(role, password, must_change):
    return {"role": role, "active": True, "must_change": bool(must_change), "created": now_str(),
            "last_login": "", "permissions": default_permissions(role), **_hash_pw(password)}


def _default_users():
    pw = _secret("INITIAL_ADMIN_PASSWORD")
    if not pw or password_problem(pw, DEFAULT_ADMIN_USER):
        raise RuntimeError("First-time setup: set INITIAL_ADMIN_PASSWORD in the server secrets or environment "
                           "to a unique password with at least 8 characters, letters and numbers. "
                           "Then sign in as admin. Existing accounts are not affected.")
    return {DEFAULT_ADMIN_USER: _new_user("admin", pw, must_change=True)}


def _read_users_file():
    """Only an absent file means first run. Damaged accounts must never be reset."""
    if not os.path.exists(USERS_FILE):
        return None
    try:
        with open(USERS_FILE, "r", encoding="utf-8-sig") as f:
            data = json.load(f)
        users = data.get("users") if isinstance(data, dict) else None
        if not isinstance(users, dict) or not users:
            raise ValueError("the accounts list is empty or invalid")
        for username, rec in users.items():
            if not isinstance(rec, dict) or rec.get("role") not in ROLES:
                raise ValueError(f"invalid account record: {username}")
            if not isinstance(rec.get("active", True), bool):
                raise ValueError(f"invalid active flag: {username}")
            permissions = rec.get("permissions", {})
            if not isinstance(permissions, dict) or any(not isinstance(v, bool) for v in permissions.values()):
                raise ValueError(f"invalid permissions: {username}")
            if not (isinstance(rec.get("salt"), str) and isinstance(rec.get("hash"), str)):
                raise ValueError(f"missing password hash: {username}")
            if len(bytes.fromhex(rec["salt"])) < 16 or len(bytes.fromhex(rec["hash"])) != 32:
                raise ValueError(f"invalid password hash: {username}")
            if not 100_000 <= int(rec.get("iter", 0)) <= 2_000_000:
                raise ValueError(f"invalid password settings: {username}")
        return users
    except (OSError, ValueError, TypeError) as e:
        raise RuntimeError("Accounts file cannot be read safely. Ask Admin to restore a verified backup; "
                           "existing accounts have been preserved.") from e


def save_users(users):
    with _sync_state()["lock"], file_lock(USERS_FILE):
        _write_atomic(USERS_FILE, json.dumps({"users": users}, ensure_ascii=False, indent=1).encode("utf-8"))
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
            with _sync_state()["lock"], file_lock(USERS_FILE):
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
            with _sync_state()["lock"], file_lock(USERS_FILE):
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


# ---- "Keep me logged in": a random token in the phone's browser; the server keeps only its hash ----
def _tok_hash(token):
    return hashlib.sha256(str(token).encode("utf-8")).hexdigest()


def _read_tokens():
    try:
        with open(REMEMBER_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def _modify_tokens(fn):
    """Read-change-save of the token file (retries when Dropbox is busy). Never raises: remembering is a convenience."""
    for attempt in range(4):
        try:
            with _sync_state()["lock"]:
                if USE_DROPBOX:
                    pull(REMEMBER_FILE, force=True)
                data = _read_tokens()
                data = fn(data) or data
                tmp = REMEMBER_FILE + ".tmp"
                with file_lock(REMEMBER_FILE):
                    with open(tmp, "w", encoding="utf-8") as f:
                        json.dump(data, f)
                    os.replace(tmp, REMEMBER_FILE)
                if USE_DROPBOX:
                    push(REMEMBER_FILE)
            return True
        except ConflictError:
            time.sleep(0.2 * (attempt + 1))
        except Exception as e:
            bot_log("warn", "Remember login", str(e)[:120], "skipped")
            return False
    return False


def issue_remember_token(user, pw_stamp):
    token = pysecrets.token_urlsafe(32)
    now = time.time()

    def _add(data):
        for h in [h for h, r in data.items() if r.get("exp", 0) < now]:
            data.pop(h, None)                                   # forget expired phones
        mine = sorted([(r.get("created", 0), h) for h, r in data.items() if r.get("user") == user])
        for _, h in mine[:-9]:
            data.pop(h, None)                                   # at most 10 phones / browsers per person
        data[_tok_hash(token)] = {"user": user, "created": now, "exp": now + REMEMBER_DAYS * 86400, "pw": pw_stamp}
        return data
    return token if _modify_tokens(_add) else None


def _request_cookie(name):
    try:
        return st.context.cookies.get(name)
    except Exception:
        return None


def restore_from_cookie():
    """Logs the person in again from the phone's saved token (after a screen lock, a closed tab, a new day...)."""
    token = _request_cookie(COOKIE_TOKEN)
    if not token:
        return False
    h, now = _tok_hash(token), time.time()
    rec = _read_tokens().get(h)
    try:
        users = load_users()
    except Exception:
        return False
    u = users.get(rec["user"]) if rec else None
    if not rec or rec.get("exp", 0) < now or not u or not u.get("active", True) or rec.get("pw", "") != u.get("pw_changed", ""):
        if rec:
            _modify_tokens(lambda d: (d.pop(h, None), d)[1])
        st.session_state["cookie_cmd"] = ("clear",)
        return False
    st.session_state.update({"user": rec["user"], "role": u["role"], "login_time": now,
                             "must_change": bool(u.get("must_change"))})
    audit("login", f"{u['role']} (remembered)")
    if rec.get("exp", 0) - now < (REMEMBER_DAYS - 1) * 86400:     # renew once a day
        def _renew(d):
            if h in d:
                d[h]["exp"] = now + REMEMBER_DAYS * 86400
            return d
        _modify_tokens(_renew)
    return True


def forget_this_device():
    token = _request_cookie(COOKIE_TOKEN)
    if token:
        _modify_tokens(lambda d: (d.pop(_tok_hash(token), None), d)[1])
    st.session_state["cookie_cmd"] = ("clear",)


def _emit_cookie_cmd():
    """Writes / removes the cookies in the phone's browser (JavaScript, runs once)."""
    cmd = st.session_state.pop("cookie_cmd", None)
    if not cmd:
        return
    age = REMEMBER_DAYS * 86400
    if cmd[0] == "set":
        tok, user = json.dumps(cmd[1]), json.dumps(cmd[2])
        js = (f"var s=(window.parent.location.protocol==='https:')?'; Secure':'';"
              f"window.parent.document.cookie='{COOKIE_TOKEN}='+{tok}+'; max-age={age}; path=/; SameSite=Lax'+s;"
              f"window.parent.document.cookie='{COOKIE_USER}='+encodeURIComponent({user})+'; max-age={age}; path=/; SameSite=Lax'+s;")
    else:
        js = (f"window.parent.document.cookie='{COOKIE_TOKEN}=; max-age=0; path=/';")
    try:
        st.components.v1.html(f"<script>try{{{js}}}catch(e){{}}</script>", height=0)
    except Exception:
        pass


def _clear_session():
    st.session_state.pop("_table_drafts", None)
    st.session_state.pop("_task_preferences", None)
    st.session_state.pop("last_customer_upload_export", None)
    for k in ("role", "user", "login_time", "must_change", "sel_cust", "me_staff", "user_permissions"):
        st.session_state.pop(k, None)


def logout(reason="manual"):
    audit("logout", reason)
    if reason == "manual":
        forget_this_device()                               # a manual log-out also forgets this phone
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
        st.error("Cannot verify account access. Please retry when account storage is available.")
        return False
    if not rec or not rec.get("active", True) or rec.get("role") != role:
        logout("account removed or changed")
        return False
    st.session_state["must_change"] = bool(rec.get("must_change"))
    st.session_state["user_permissions"] = rec.get("permissions", {}) if isinstance(rec.get("permissions", {}), dict) else {}
    return True


def _try_login(username, password, remember=False):
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
        if remember and not rec.get("must_change"):      # starter password: remember only after they choose their own
            tok = issue_remember_token(uname, rec.get("pw_changed", ""))
            if tok:
                st.session_state["cookie_cmd"] = ("set", tok, uname)

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
        last_user = urllib.parse.unquote(_request_cookie(COOKIE_USER) or "")[:40]
        with st.form("login_form"):
            try:
                u = st.text_input("Username", value=last_user, max_chars=40, autocomplete="username")
                p = st.text_input("Password", type="password", max_chars=100, autocomplete="current-password")
            except TypeError:                              # older Streamlit without autocomplete
                u = st.text_input("Username", value=last_user, max_chars=40)
                p = st.text_input("Password", type="password", max_chars=100)
            keep = st.checkbox(f"Keep me logged in on this phone / computer ({REMEMBER_DAYS} days)", value=True)
            go = st.form_submit_button("Log in", type="primary")
        st.caption("Tip: do not tick this on a shared computer. Log out removes it.")
        if go:
            _try_login(u, p, keep)


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
                try:
                    _rec = load_users().get(user, {})
                    _tok = issue_remember_token(user, _rec.get("pw_changed", ""))
                    if _tok:
                        st.session_state["cookie_cmd"] = ("set", _tok, user)
                except Exception:
                    pass
                st.session_state["flash"] = "Password changed. Welcome!"
                st.rerun()
        if st.button("🚪 Log out", key="force_logout"):
            logout("manual")
            st.rerun()


def require_login():
    """Shows the login page (and stops the app) until the person is logged in. Returns the role."""
    if not session_ok():
        restore_from_cookie()                              # phone was locked / tab closed: use the saved token
    _emit_cookie_cmd()
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
@st.cache_resource(show_spinner=False)
def _file_lock_state():
    return {"guard": threading.Lock(), "locks": {}, "local": threading.local()}


@contextlib.contextmanager
def file_lock(path, timeout=6.0):
    """Reentrant thread/process lock. Timeout always refuses the write.
    Lock files remain in place: OS locks are automatically released on process exit.
    """
    path = os.path.abspath(os.fspath(path))
    state = _file_lock_state()
    with state["guard"]:
        mutex = state["locks"].setdefault(path, threading.RLock())
    deadline = time.monotonic() + timeout
    if not mutex.acquire(timeout=max(0.0, timeout)):
        raise RuntimeError("Another save is in progress. Wait a moment and try again.")
    held = state["local"]
    depths = getattr(held, "depths", None)
    if depths is None:
        held.depths = depths = {}
    handle = None
    acquired = False
    try:
        if depths.get(path, 0):
            depths[path] += 1
            try:
                yield
            finally:
                depths[path] -= 1
            return
        handle = open(path + ".lock", "a+b")
        if os.name == "nt":
            import msvcrt
            if os.path.getsize(path + ".lock") == 0:
                handle.write(b"0")
                handle.flush()
        else:
            import fcntl
        while True:
            try:
                if os.name == "nt":
                    handle.seek(0)
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                else:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                acquired = True
                break
            except (BlockingIOError, OSError) as e:
                if time.monotonic() >= deadline:
                    raise RuntimeError("Another save is in progress. No changes were written; try again.") from e
                time.sleep(0.05)
        depths[path] = 1
        try:
            yield
        finally:
            depths.pop(path, None)
    finally:
        if handle is not None:
            if acquired:
                if os.name == "nt":
                    handle.seek(0)
                    msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
                else:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
            handle.close()
        mutex.release()


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
    """A failed write leaves the previous complete file intact."""
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=".hub-", suffix=".tmp", dir=directory)
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        _retry(lambda: os.replace(tmp, path))
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)


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
            if os.path.exists(path) and os.path.getsize(path) > 0:
                S["last_pull"].pop(path, None)
                raise RuntimeError(f"{name} is missing from Dropbox but a local copy exists. "
                                   "Ask Admin to restore the remote file; the local copy was preserved.")
            return
        if S["rev"].get(path) == md.rev and os.path.exists(path):
            return
        downloaded, res = _dbx().files_download(_rpath(name))
        _write_atomic(path, res.content)
        S["rev"][path] = downloaded.rev


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
        name = f"{stamp}_{tag}-{pysecrets.token_hex(3)}_{os.path.basename(path)}"
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


def daily_backup_once(day_str):
    """Retry failed backups, cache only success, and protect accounts/locations too."""
    state = _sync_state()
    failures = []
    with state["lock"]:
        if state.get("backup_day") != day_str:
            state["backup_day"] = day_str
            state["backup_done"] = set()
        done = state.setdefault("backup_done", set())
        files = (DATA_FILE, PACKING_FILE, ASSIGN_FILE, HOLD_FILE, USERS_FILE, LOCATIONS_FILE, MAP_REGISTRY_FILE)
        if USE_DROPBOX:
            try:
                _dbx().files_create_folder_v2(_remote_backup_dir())
            except Exception as e:
                if not _is_conflict(e):
                    return [f"Cannot access backup folder: {str(e)[:120]}"]
        else:
            try:
                os.makedirs(BACKUP_DIR, exist_ok=True)
            except OSError as e:
                return [f"Cannot access backup folder: {str(e)[:120]}"]
        for path in files:
            if path in done:
                continue
            base = os.path.basename(path)
            try:
                if USE_DROPBOX:
                    if remote_meta(base) is None:
                        continue
                    dest = f"{_remote_backup_dir()}/{day_str}_{base}"
                    try:
                        _dbx().files_get_metadata(dest)
                    except Exception as e:
                        if not _is_not_found(e):
                            raise
                        _dbx().files_copy_v2(_rpath(base), dest)
                else:
                    if not os.path.exists(path):
                        continue
                    dest = os.path.join(BACKUP_DIR, f"{day_str}_{base}")
                    if not os.path.exists(dest):
                        with file_lock(path):
                            with open(path, "rb") as f:
                                _write_atomic(dest, f.read())
                done.add(path)
            except Exception as e:
                failures.append(f"{base}: {str(e)[:160]}")
        if not failures and state.get("pruned_day") != day_str:
            prune_backups()
            state["pruned_day"] = day_str
    return failures


# ==========================================
# CSV READ (cached by file change) / WRITE
# ==========================================
def _read_csv_strict(path):
    with open(path, "r", newline="", encoding="utf-8-sig") as f:
        records = csv.reader(f, strict=True)
        header = next(records, None)
        if not header or len(header) != len(set(header)) or any(not c.strip() for c in header):
            raise ValueError("CSV headers are empty or duplicated")
        rows = []
        for row in records:
            if not row:
                continue
            if len(row) != len(header):
                raise ValueError(f"CSV line {records.line_num}: expected {len(header)} fields, found {len(row)}")
            rows.append(row)
    return pd.DataFrame(rows, columns=header)


def _numeric_issues(raw, columns):
    issues = []
    for col in columns:
        if col not in raw:
            continue
        cap = MAX_CASES if "Cases" in col else MAX_RIEL
        values = pd.to_numeric(raw[col], errors="coerce")
        bad = values.isna() | ~values.map(lambda v: math.isfinite(v)) | (values < 0) | (values > cap) | (values % 1 != 0)
        if bad.any():
            lines = ", ".join(str(int(i) + 2) for i in raw.index[bad][:8])
            issues.append(f"{col}: {int(bad.sum())} invalid values (rows {lines}); use whole numbers from 0 to {cap}")
    return issues


def _csv_read(path, cols):
    df = pd.DataFrame()
    if os.path.exists(path):
        try:
            df = _read_csv_strict(path)
            required = {"Date", "Customer"} | {c for c in cols if c in NUM_COLS_ALL}
            if required - set(df.columns):
                raise ValueError("missing required columns: " + ", ".join(sorted(required - set(df.columns))))
            issues = _numeric_issues(df, [c for c in cols if c in NUM_COLS_ALL])
            if issues:
                raise ValueError("; ".join(issues))
        except Exception as e:
            raise RuntimeError(f"{os.path.basename(path)} needs review: {e}. Original data was preserved.") from e
    for c in cols:
        if c not in df.columns:
            df[c] = "0" if c in NUM_COLS_ALL else "-"
    for c in df.columns:
        df[c] = df[c].astype(str).str.strip()
    for c in cols:
        if c == "Date":
            continue
        if c in NUM_COLS_ALL:
            df[c] = pd.to_numeric(df[c], errors="raise").astype("int64")
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
    spec = next((spec for spec in FILES.values() if spec[0] == path), None)
    if spec:
        issues = _numeric_issues(out, spec[2])
        if issues:
            raise RuntimeError("Cannot save: " + "; ".join(issues))
    with _sync_state()["lock"], file_lock(path):
        _write_atomic(path, out.to_csv(index=False).encode("utf-8-sig"))
        if USE_DROPBOX:
            push(path)


def _append_local_many(path, rows):
    """Commit an entire batch atomically, preserving text and unknown columns."""
    with file_lock(path):
        if os.path.exists(path):
            old = _read_csv_strict(path)
            out = pd.concat([old, pd.DataFrame(rows)], ignore_index=True).astype(object)
            out = out.where(out.notna(), "-")
        else:
            out = pd.DataFrame(rows)
        _write_atomic(path, out.to_csv(index=False).encode("utf-8-sig"))


def append_rows(path, rows):
    """Add several rows in ONE save (text is cleaned first). Online: one download, one upload."""
    rows = [{k: (v if k == "Date" or not isinstance(v, str) else safe_text(v)) for k, v in r.items()} for r in rows]
    if not rows:
        return
    spec = next((spec for spec in FILES.values() if spec[0] == path), None)
    if spec:
        raw = pd.DataFrame(rows)
        missing = set(spec[1]) - set(raw.columns)
        if missing:
            raise RuntimeError(f"Cannot save: missing fields {', '.join(sorted(missing))}")
        problems = _numeric_issues(raw, spec[2])
        if problems:
            raise RuntimeError("Cannot save: " + "; ".join(problems))
        if raw["Date"].map(parse_dt).isna().any():
            raise RuntimeError("Cannot save: invalid date. Use YYYY-MM-DD HH:MM:SS.")
        if raw["Customer"].astype(str).str.strip().isin(["", "-", "None", "nan"]).any():
            raise RuntimeError("Cannot save: choose a customer for every row.")
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
            with _sync_state()["lock"], file_lock(path):
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
    key = (SNAPSHOT_VERSION, os.path.abspath(path), mtime_ns, size)
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
        if obj and obj.get("data") and tuple(obj.get("key", ())[:2]) == key[:2]:
            bot_log("fixed", "Excel", f"Could not read journal ({str(e)[:120]}); using last good copy", "used saved copy")
            return obj["data"], "stale"
        raise
    try:
        _write_atomic(cache_file, pickle.dumps({"key": key, "data": data}))
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
    names = list(snap["customers"]) if snap else []
    seen = {norm_name(name) for name in names}
    try:
        for rec in load_map_registry()["records"].values():
            if norm_name(rec["customer"]) not in seen:
                names.append(rec["customer"])
                seen.add(norm_name(rec["customer"]))
    except Exception as e:
        bot_log("warn", "Customer maps", str(e)[:180], "using Master List customer names")
    return sorted(names, key=str.casefold) if names else [f"⚠️ Error: {err or 'Customer lists are empty'}"]


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
    """Diagnose original values first. Never discard rows or guess corrections."""
    path, cols, nums, label = FILES[key]
    base = os.path.basename(path)
    suggestions = []
    if USE_DROPBOX:
        try:
            pull(path, force=True)
        except Exception as e:
            add("error", label, f"Cannot refresh {base}: {str(e)[:100]}", "retry when storage is available; no repair attempted")
            return suggestions
    if not os.path.exists(path):
        if auto_fix:
            save_csv(path, pd.DataFrame(columns=cols))
            add("fixed", label, f"Created missing {base}", "created headers only")
        else:
            add("warn", label, f"{base} does not exist", "create an empty file with headers")
        return suggestions
    try:
        raw = _read_csv_strict(path)
    except Exception as e:
        add("error", label, f"{base}: {str(e)[:240]}", "original preserved; restore a verified backup or correct the source file")
        return suggestions
    missing = [c for c in cols if c not in raw]
    required = {"Date", "Customer", *nums}
    if required.intersection(missing):
        add("error", label, f"{base}: missing required columns {sorted(required.intersection(missing))}", "review the file headers; no values guessed")
        return suggestions
    issues = _numeric_issues(raw, nums)
    for issue in issues:
        add("error", label, f"{base}: {issue}", "correct original values; no numbers were replaced with zero")
    if issues:
        return suggestions
    df = _csv_read(path, cols)
    fixed = df.copy()
    notes = []
    if missing:
        notes.append("added optional columns: " + ", ".join(missing))
    if master:
        canon = canonical_map(master)
        corrected = fixed["Customer"].map(lambda n: canon.get(norm_name(n), n))
        count = int((corrected != fixed["Customer"]).sum())
        fixed["Customer"] = corrected
        if count:
            notes.append(f"normalized spacing/capitalization for {count} customer names")
    duplicate_count = int(raw.duplicated(subset=[c for c in cols if c in raw]).sum())
    if duplicate_count:
        add("warn", label, f"{base}: {duplicate_count} exact repeated records", "review possible duplicates; all records retained")
    if notes:
        if auto_fix:
            if not backup_file(path, "before-fix"):
                add("error", label, "Could not back up " + base, "repair skipped; check storage permissions")
            else:
                save_csv(path, fixed)
                add("fixed", label, f"{base}: " + "; ".join(notes), "saved with backup; all rows retained")
        else:
            add("warn", label, f"{base}: " + "; ".join(notes), "safe normalization available")
    bad_dates = fixed["_dt"].isna()
    if bad_dates.any():
        lines = ", ".join(str(int(i) + 2) for i in fixed.index[bad_dates][:8])
        add("error", label, f"{base}: {int(bad_dates.sum())} unreadable dates (rows {lines})", "correct dates as YYYY-MM-DD HH:MM:SS")
    future = fixed["_dt"] > pd.Timestamp(now_kh().replace(tzinfo=None)) + pd.Timedelta(minutes=5)
    if future.any():
        add("warn", label, f"{base}: {int(future.sum())} records have future timestamps", "check the date and device clock")
    blanks = fixed["Customer"].isin(["", "-", "None", "nan"])
    if blanks.any():
        add("error", label, f"{base}: {int(blanks.sum())} records have no customer", "set a valid customer; records retained")
    allowed = {
        "packing": ("Status", {"In Progress (កំពុងធ្វើ)", "Completed (រួចរាល់)"}),
        "assign": ("Action", {"Assign", "Release"}),
        "holds": ("Action", {"Tomorrow", "Cancel", "Restore", "FinalPacked", "FinalPackedReset", "FinalSent", "FinalReset"}),
    }
    if key in allowed:
        column, values = allowed[key]
        invalid = ~fixed[column].isin(values)
        if invalid.any():
            add("warn", label, f"{base}: {int(invalid.sum())} unknown {column} values", "review status/action spelling")
    if master:
        unknown = sorted(set(fixed["Customer"]) - set(master) - {"-"})
        no_match = []
        for name in unknown[:60]:
            close = difflib.get_close_matches(name, master, n=1, cutoff=0.9)
            if close:
                suggestions.append((key, name, close[0]))
            else:
                no_match.append(name)
        if suggestions:
            add("warn", label, f"{len(suggestions)} possible customer typos", "review each suggested replacement before applying")
        if no_match:
            add("info", label, "Customers absent from Master List: " + ", ".join(no_match[:4]), "review new customers")
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
    except Exception as e:
        add("warn", "Locations", f"Location check could not complete: {str(e)[:160]}", "review location data")

    try:
        registry = load_map_registry()
        location_frame = map_registry_frame(registry)
        status_counts = location_frame["Map status"].value_counts()
        add("info", "Customer maps", f"{len(location_frame)} location records; {int(status_counts.get('Ready pin', 0))} ready pins", "locations imported independently of order counts")
        for status, count in status_counts.items():
            if status != "Ready pin":
                level = "error" if status in ("Invalid map link", "Outside Cambodia area — review", "Multiple pins — review") else "warn"
                add(level, "Customer maps", f"{int(count)} records: {status}", "review in the Customer Map tab; uncertain pins are excluded")
        name_counts = Counter(norm_name(rec["customer"]) for rec in registry["records"].values())
        ambiguous = sum(count > 1 and name not in registry["bindings"] for name, count in name_counts.items())
        if ambiguous:
            add("warn", "Customer map matching", f"{ambiguous} repeated customer names need explicit matching for delivery use", "Admin can match a delivery customer to a specific location ID")
        invalid_bindings = [key for key, rid in registry["bindings"].items() if rid not in registry["records"]]
        if invalid_bindings:
            add("error", "Customer map matching", f"{len(invalid_bindings)} saved matches refer to unavailable locations", "correct saved matches")
    except Exception as map_error:
        add("error", "Customer maps", str(map_error)[:200], "review the map registry; delivery records are preserved")

    # --- CSV files ---
    for key in FILES:
        try:
            with _sync_state()["lock"], file_lock(FILES[key][0]):
                suggestions += _check_csv(add, key, master, auto_fix)
        except Exception as e:
            add("error", FILES[key][3], f"Check failed: {e}", "-")

    # --- backups, locks, disk ---
    if auto_fix:
        backup_failures = daily_backup_once(today_kh().strftime("%Y-%m-%d"))
        for failure in backup_failures:
            add("error", "Backup", failure, "check backup access; failed backups will be retried")
        if not backup_failures:
            add("info", "Backup", "Daily backups completed for available data, accounts and locations", "-")
    elif not glob.glob(os.path.join(BACKUP_DIR, f"{today_kh():%Y-%m-%d}_*")):
        add("warn", "Backup", "No backup made today yet", "would create one")
    try:
        free_gb = shutil.disk_usage(CURRENT_DIR).free / 1e9
        if free_gb < 1:
            add("warn", "Disk", f"Only {free_gb:.1f} GB free on this drive", "free some space")
    except Exception:
        pass

    # --- security ---
    try:
        users = (_read_users_file() if not auto_fix else load_users()) or {}
        if not [u for u, r in users.items() if r.get("role") == "admin" and r.get("active", True)]:
            add("error", "Security", "There is no active admin account", "restore a verified accounts backup; keep the current file for review")
        starters = [u for u, r in users.items() if r.get("must_change")]
        if starters:
            add("warn", "Security", f"Still on a starter password: {', '.join(sorted(starters))}",
                "log in with each account and choose a new password")
        n_fail = failed_logins(1)
        if n_fail >= 15:
            add("warn", "Security", f"{n_fail} wrong-password attempts in the last hour", "see the Audit log; consider changing passwords")
    except Exception as e:
        add("error", "Security", str(e)[:240], "ask Admin to verify the accounts file")
    try:
        major, minor = [int(x) for x in st.__version__.split(".")[:2]]
        if (major, minor) < (1, 37):
            add("warn", "Streamlit", f"Version {st.__version__} is old (fast mode needs 1.37+)", "pip install -U streamlit")
    except Exception:
        pass

    try:
        import importlib.util
        for package in ("openpyxl", "xlsxwriter") + (("dropbox",) if USE_DROPBOX else ()):
            if importlib.util.find_spec(package) is None:
                add("warn", "Dependencies", f"Missing package: {package}", f"install with python -m pip install {package}")
        for directory in {DATA_DIR, CACHE_DIR}:
            os.makedirs(directory, exist_ok=True)
            fd, probe = tempfile.mkstemp(prefix=".hub-probe-", dir=directory)
            os.close(fd)
            os.remove(probe)
    except Exception as e:
        add("error", "Storage", f"Storage check failed: {str(e)[:180]}", "check free space and folder permissions")
    try:
        report, _, report_error = build_report(today_kh())
        if report_error:
            add("warn", "Operations", "Order checks limited: journal unavailable", "restore journal access for complete validation")
        if not report.empty:
            ordered = pd.to_numeric(report["កេស"], errors="coerce")
            sent = pd.to_numeric(report["Sent Cases"], errors="coerce")
            packed = pd.to_numeric(report["Packed Cases"], errors="coerce")
            for mask, message in ((ordered.notna() & (sent > ordered), "sent cases exceed ordered cases"),
                                  (ordered.notna() & (packed > ordered), "packed cases exceed ordered cases"),
                                  ((packed > 0) & (sent > packed), "sent cases exceed packed cases")):
                if mask.any():
                    names = ", ".join(report.loc[mask, "Customer"].astype(str).head(5))
                    add("warn", "Operations", f"{int(mask.sum())} customers: {message} ({names})", "review counts; bot does not change quantities")
    except Exception as e:
        add("error", "Operations", f"Cross-file checks could not complete: {str(e)[:180]}", "resolve source-data errors first")
    if not any(f["Level"] in (LEVEL_ICON["error"], LEVEL_ICON["warn"]) for f in findings):
        add("ok", "All checks", "No unresolved problems found in completed checks", "-")
    ranks = {LEVEL_ICON[k]: i for i, k in enumerate(("error", "warn", "fixed", "ok", "info"))}
    findings.sort(key=lambda f: ranks.get(f["Level"], 9))
    return findings, suggestions


@st.cache_data(ttl=BOT_INTERVAL_MIN * 60, show_spinner=False)
def auto_bot(_token=0):
    """Runs by itself at start-up and then every BOT_INTERVAL_MIN minutes."""
    try:
        result = run_health_check(auto_fix=True)
        _sync_state()["last_health_check"] = now_str()
        return result
    except Exception as e:
        _sync_state()["last_health_check"] = now_str() + " (failed)"
        bot_log("error", "Bot", f"Health check crashed: {e}", "-")
        return [{"Level": LEVEL_ICON["error"], "Check": "Bot", "Message": str(e), "Action": "-"}], []


def apply_name_fixes(suggestions):
    by_file = {}
    for key, bad, good in suggestions:
        by_file.setdefault(key, {})[bad] = good
    for key, mapping in by_file.items():
        path, cols, _, label = FILES[key]
        if not backup_file(path, "before-name-fix"):
            raise RuntimeError("Name correction cancelled because the backup could not be saved.")

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
        # Keep drafts and the current screen intact. Only the explicit Retry button reruns.
        bot_log("error", label, f"{type(e).__name__}: {e}", "diagnostics started")
        if current_role() == "admin":
            st.error(f"⚠️ Problem in {label}: {e}")
        else:
            st.error("⚠️ Something went wrong. The bot is checking the data - press Retry in a moment.")
        flag = f"bot_ran_{label}"
        if time.time() - st.session_state.get(flag, 0) > 60:
            st.session_state[flag] = time.time()
            try:
                run_health_check(auto_fix=False)
                st.cache_data.clear()
                st.info("🤖 Diagnostics complete. Admin can review the Health Bot results. Press Retry.")
            except Exception:
                pass
        if current_role() == "admin":
            with st.expander("Technical details"):
                st.code(traceback.format_exc())
        if st.button("🔁 Retry now", key=f"retry_{label}"):
            st.cache_data.clear()
            st.rerun()


def customer_choices(day=None):
    """(options, label_fn, journal_set) for the customer pickers.
    Customers that have an order in the sale journal for the day come first (🧾); every other customer of the master list
    can still be chosen (marked 'not in journal'), so a delivery is never blocked."""
    snap, _, _, err = current_snapshot()
    day = day or today_kh()
    first, jset = [], set()
    if snap:
        j = snap["journal"]
        first = sorted({n for n in j[j["Date"] == day]["Customer"]}, key=str.casefold)
        jset = set(first)
    rest = [c for c in get_customer_list() if c not in jset]
    options = ["-- Select a Customer --"] + first + rest

    def label(c):
        if c in jset:
            return f"🧾 {c}"
        if c.startswith("--") or c.startswith("⚠️"):
            return c
        return f"{c}   (not in today's journal)"
    return options, label, jset


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


def flash_and_refresh(msg, reset_prefix=None):
    if reset_prefix:
        st.session_state["reset_form_prefix"] = reset_prefix + "_"
    st.session_state["flash"] = msg
    st.session_state["clear_sel"] = True
    st.rerun()


# ==========================================
# FORMS
# ==========================================
BASE_VIA = "Grab/TukTuk"
SELF_DELIVERY = "My own delivery (self-delivered)"
PICKUP_VIA = "Customer pick-up (មកយកខ្លួនឯង)"      # not our delivery: the customer collects the buns


def via_options():
    # Self-delivery is a real delivery task, but it does not require a transport expense.
    return [BASE_VIA, SELF_DELIVERY] + LOCAL_DRIVERS + [PICKUP_VIA]


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
    if not has_permission("edit") or not has_permission("tasks"):
        st.warning("Editing delivery tasks is disabled for your account.")
        return
    k = form_key
    with st.form(form_key, clear_on_submit=False):
        st.markdown("#### Order Details")
        dispatched_by = st.selectbox("Dispatched By:", ["-- Select Staff --"] + DELIVERY_HANDLERS, key=f"{k}_by")
        if fixed_customer is None:
            opts, lab, jset = customer_choices()
            customer_name = st.selectbox(f"Customer Name / ID (Type to search) - 🧾 = has an order in today's sale journal ({len(jset)}):",
                                         opts, format_func=lab, key=f"{k}_cust")
        else:
            customer_name = fixed_customer
            st.markdown(f"**Customer:** {fixed_customer}")
        d_cases = max(0, min(int(default_cases), MAX_CASES))
        cases = st.number_input("ចំនួនកេស (Number of Cases):", min_value=0, max_value=MAX_CASES, step=1,
                                value=d_cases, key=f"{k}_cases_{d_cases}")
        if verify:
            verified_by = st.selectbox("✅ Cases verified by (confirms the កេស number is correct):",
                                       ["-- Select Staff --"] + VERIFY_STAFF, key=f"{k}_vby")
        else:
            verified_by = st.selectbox("Cases verified by (optional):", ["-"] + VERIFY_STAFF, key=f"{k}_vby")

        st.markdown("---")
        st.markdown("#### Transportation Details")
        local_driver = st.selectbox(
            "Delivery method - choose My own delivery if the selected staff member delivers it themselves:",
            ["None (Grab/TukTuk)", SELF_DELIVERY] + LOCAL_DRIVERS + [PICKUP_VIA], key=f"{k}_drv")
        taxi_station = st.text_input("Taxi Station Name (Leave blank if purely local Phnom Penh delivery):",
                                     max_chars=MAX_TEXT, key=f"{k}_taxi")
        delivery_note = st.text_input("📝 Note (Optional: Taxi phone number, plate, or instructions):",
                                      max_chars=MAX_TEXT, key=f"{k}_note")

        st.markdown("#### Expenses (៛ Riel) - optional now, you can fill them later in the Delivery tab")
        st.caption("For My own delivery or a named local driver, leave Phnom Penh transport expense at 0 unless you actually paid a transport fee.")
        pp_expense = st.number_input("1. Phnom Penh Expense (៛) - Enter 0 if using own delivery / local driver:",
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
                    nj = "" if (fixed_customer is not None or customer_name in jset) else "  ⚠️ not in today's sale journal"
                    flash_and_refresh(f"Dispatched by {dispatched_by}: {customer_name} | {cases} កេស{nj}", reset_prefix=k)
                except Exception as save_err:
                    bot_log("error", "Save dispatch", str(save_err), "-")
                    st.error(f"⚠️ Could not save: {save_err}")


def packing_form(form_key, fixed_customer=None, default_cases=1):
    if not has_permission("edit") or not has_permission("tasks"):
        st.warning("Editing packing tasks is disabled for your account.")
        return
    k = form_key
    with st.form(form_key, clear_on_submit=False):
        if fixed_customer is None:
            opts, lab, jset = customer_choices()
            customer = st.selectbox(f"Customer Name / ID (Type to search) - 🧾 = has an order in today's sale journal ({len(jset)}):",
                                    opts, format_func=lab, key=f"{k}_cust")
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
                    nj = "" if (fixed_customer is not None or customer in jset) else "  ⚠️ not in today's sale journal"
                    flash_and_refresh(f"Packing logged: {customer} | {cases_packed} cases | {pack_status}{nj}", reset_prefix=k)
                except Exception as err:
                    bot_log("error", "Save packing", str(err), "-")
                    st.error(f"⚠️ Could not save: {err}")


def admin_editor(path, cols, num_cols, key, label_cols):
    if current_role() != "admin" or not has_permission("edit"):
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
                                                  value=max(0, min(int(current[c]), cap)), step=step, key=wkey)
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


def _draft_id(workflow, scope=""):
    # User and day boundaries prevent yesterday's or another account's draft being submitted.
    token = f"{current_user()}|{today_kh()}|{workflow}|{scope}"
    return hashlib.sha256(token.encode()).hexdigest()[:20]


def _draft_frame(workflow, candidate, scope=""):
    identity = _draft_id(workflow, scope)
    drafts = st.session_state.setdefault("_table_drafts", {})
    if identity not in drafts:
        drafts[identity] = {"frame": candidate.copy(deep=True), "generation": 0}
    draft = drafts[identity]
    return draft["frame"].copy(deep=True), f"draft_editor_{identity}_{draft['generation']}"


def _reset_draft(workflow, scope=""):
    identity = _draft_id(workflow, scope)
    drafts = st.session_state.setdefault("_table_drafts", {})
    old = drafts.get(identity, {})
    drafts[identity] = {"frame": None, "generation": old.get("generation", 0) + 1}


def _task_editor_frame(workflow, candidate, scope=""):
    identity = _draft_id(workflow, scope)
    draft = st.session_state.get("_table_drafts", {}).get(identity)
    if draft is not None and draft.get("frame") is None:
        draft["frame"] = candidate.copy(deep=True)
    return _draft_frame(workflow, candidate, scope)


def _form_preferences(workflow, scope=""):
    return st.session_state.setdefault("_task_preferences", {}).setdefault(_draft_id(workflow, scope), {})


def _has_editor_draft(workflow, scope=""):
    draft = st.session_state.get("_table_drafts", {}).get(_draft_id(workflow, scope), {})
    frame = draft.get("frame")
    return frame is not None and not frame.empty


def _reload_draft_button(workflow, scope=""):
    if st.button("↻ Reload this list", key="reload_" + _draft_id(workflow, scope),
                 help="Read the newest data and clear only this list's unsaved ticks and edits."):
        _reset_draft(workflow, scope)


def bulk_editor(df, ctx, key, check_col="Save?", column_order=None, scope=""):
    """Batch ticks, staff selection and cell edits; only Save sends them to the server."""
    if not has_permission("edit") or not has_permission("tasks"):
        st.warning("Editing packing tasks is disabled for your account.")
        return
    workflow = "packing:" + key
    _reload_draft_button(workflow, scope)
    d, editor_key = _task_editor_frame(workflow, df, scope)
    if d.empty:
        st.info("No customers need packing in this list. Reload to check for new orders.")
        return
    if check_col != "Save?":
        d = d.rename(columns={"Save?": check_col})
    opts = sorted(set(ctx["today"]) | {c for c in d["Customer"] if c})
    st.caption("Tick several customers and edit their cases, then save once. Ticks and typing stay on this screen until you save.")
    preferences = _form_preferences("packing_staff")
    linked = preferences.get("prepared_by") or staff_name_for_user()
    staff_options = ["-- Select Staff --"] + OPS_STAFF
    with st.form("batch_" + editor_key, clear_on_submit=False):
        prepared_by = st.selectbox("👷 Prepared / packed by", staff_options,
            index=staff_options.index(linked) if linked in staff_options else 0, key=f"{key}_by")
        include_all = st.checkbox("Include every customer shown when saving", key=editor_key + "_all",
            help="Applies to the whole list below when you press Save. Otherwise, tick individual rows.")
        editable = (check_col, "Cases") if key == "tick" else (check_col, "Customer", "Status", "Cases")
        edited = st.data_editor(d, hide_index=True, height=min(560, 60 + 36 * len(d)), key=editor_key,
            disabled=[c for c in d.columns if c not in editable], column_order=column_order,
            column_config={check_col: st.column_config.CheckboxColumn(check_col),
                "Customer": st.column_config.SelectboxColumn("Customer", options=opts),
                "Status": st.column_config.SelectboxColumn("Status", options=["Done", "Not yet", "Skip"]),
                "Cases": st.column_config.NumberColumn("Cases", min_value=0, max_value=MAX_CASES, step=1)})
        submitted = st.form_submit_button("💾 Save selected packing records", type="primary")
    if not submitted:
        return
    if prepared_by == "-- Select Staff --":
        st.error("Please choose who prepared these orders. Your ticks and case edits are kept.")
        return
    preferences["prepared_by"] = prepared_by
    valid, recs, total, changed = set(ctx["today"]) | set(ctx["master"]), [], 0, []
    for r in edited.to_dict("records"):
        cust, cases = str(r["Customer"] or "").strip(), _int(r["Cases"])
        if not (include_all or r[check_col]) or r["Status"] == "Skip" or cust not in valid or cases <= 0 or cases > MAX_CASES:
            continue
        if _int(ctx["packed"].get(cust, 0)) != _int(r.get("Already packed", 0)):
            changed.append(cust)
        recs.append({"Date": now_str(), "Prepared_By": prepared_by, "Customer": cust, "Cases_Packed": cases,
                     "Status": "Completed (រួចរាល់)" if r["Status"] == "Done" else "In Progress (កំពុងធ្វើ)"})
        total += cases
    if changed:
        st.error("Packing totals changed for: " + ", ".join(changed[:5]) + ". Reload this list before saving; your current selections are still here.")
        return
    if not recs:
        st.warning("Tick at least one customer with cases above 0, or choose Include every customer shown.")
        return
    try:
        append_rows(PACKING_FILE, recs)
        audit("packing_bulk", f"{len(recs)} customers, {total} cases, by {prepared_by}")
        _reset_draft(workflow, scope)
        flash_and_refresh(f"Saved {len(recs)} packing records ({total} cases)")
    except (RuntimeError, ConflictError, PermissionError) as err:
        bot_log("error", "Save packing (bulk)", str(err), "-")
        st.error(f"Could not save: {err}. Your ticks and edits are kept.")


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
    with st.form("packing_list_options"):
        show_all = st.checkbox("Also show customers that are already packed or sent", key="tick_all")
        if st.form_submit_button("Apply list options"):
            _reset_draft("packing:tick")
    d = df[df["Source"] == "Journal"].copy()
    if not show_all:
        d = d[d["Status"].isin(["⏳ Pending", "🟠 Packing"])]
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
    up = st.file_uploader("Excel (.xlsx) or CSV file", type=["xlsx", "xlsm", "csv", "txt"], key="bulk_upload_file")
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
    bulk_editor(df, ctx, key="upl", check_col="Save?", scope=hashlib.sha256(up.getvalue() + str((sheet, name_col, status_col, cases_col, blank_means, mark_progress)).encode()).hexdigest())


def _packing_body():
    st.markdown("### 📦 Bun Preparation & Packing")
    if not has_permission("edit"):
        if not has_permission("view"):
            st.warning("View is turned off. Enable View to allow read-only access to the packing log, or enable Editing to work on tasks.")
            return
        st.caption("🔒 Read-only packing view — Editing is turned off for your account.")
        df_today = rows_for_day(read_raw(PACKING_FILE, PACKING_COLS), today_kh())
        if df_today.empty:
            st.info("No packing progress logged today yet.")
            return
        show_df(df_today[PACKING_COLS])
        st.markdown("**👷 Cases packed per staff (today)**")
        show_df(df_today.groupby("Prepared_By")["Cases_Packed"].sum().reset_index())
        return
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
    if not has_permission("tasks"):
        st.error("Task access is turned off for your account. Ask Admin to enable it.")
        return
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
    if not has_permission("edit") or not has_permission("tasks"):
        st.warning("Editing delivery tasks is disabled for your account.")
        return
    st.caption("Choose the customers **you** will deliver today, before you start. Other staff will see they are taken. "
               "You can release a customer again if you cannot go.")
    recs = [r for r in ctx["recs"] if r["Status"] not in NOT_TO_SEND]
    with st.form("claim_filters"):
        f1, f2 = st.columns(2)
        area = f1.radio("Show", ["All", AREA_LABEL[PP], AREA_LABEL["Province"]], horizontal=True, key="claim_area")
        q = f2.text_input("🔎 Search customer", key="claim_q", max_chars=60)
        if st.form_submit_button("Apply customer filter"):
            _reset_draft("claim", me)
    if area != "All":
        recs = [r for r in recs if r["Area"] == area]
    if q.strip():
        recs = [r for r in recs if q.strip().lower() in r["Customer"].lower()]
    if not recs and not _has_editor_draft("claim", me):
        st.info("No customers to choose right now.")
    else:
        assigned = ctx["assigned"]
        rows = [{"Take ✅": False, "Customer": r["Customer"], "Province": r["Province"], "Status": r["Status"],
                 "Packed": int(r["Packed Cases"]), "Ordered": None if pd.isna(r["កេស"]) else int(r["កេស"]),
                 "Taken by": assigned.get(r["Customer"], "-")} for r in recs]
        _reload_draft_button("claim", me)
        d, editor_key = _task_editor_frame("claim", pd.DataFrame(rows), me)
        st.caption("Choose all the customers you need, then save once. Ticks do not refresh the page.")
        with st.form("batch_" + editor_key, clear_on_submit=False):
            select_all = st.checkbox("Include every customer shown when saving", key=editor_key + "_all")
            edited = st.data_editor(d, hide_index=True, height=min(560, 60 + 36 * len(d)), key=editor_key,
                disabled=[c for c in d.columns if c != "Take ✅"],
                column_config={"Take ✅": st.column_config.CheckboxColumn("Take ✅")})
            submitted = st.form_submit_button("✅ Save selected delivery customers", type="primary")
        if submitted:
            new, blocked = [], []
            for r in edited.to_dict("records"):
                if not (select_all or r["Take ✅"]):
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
                    _reset_draft("claim", me)
                    flash_and_refresh(f"{me} will deliver {len(new)} customers")
                except (RuntimeError, ConflictError, PermissionError) as err:
                    st.error(f"⚠️ Could not save: {err}")

    mine = [r["Customer"] for r in ctx["recs"] if ctx["assigned"].get(r["Customer"]) == me and r["Status"] not in NOT_TO_SEND]
    pool = mine if current_role() != "admin" else [c for c in ctx["assigned"] if c in {r["Customer"] for r in ctx["recs"]}]
    with st.expander(f"↩️ Release customers ({len(mine)} are mine)"):
        with st.form("release_customers", clear_on_submit=False):
            rel = st.multiselect("Customers I will NOT deliver after all", pool, key="claim_release")
            release = st.form_submit_button("↩️ Release selected")
        if release and rel:
            try:
                append_rows(ASSIGN_FILE, [{"Date": now_str(), "Handler": me, "Customer": c, "Action": "Release"} for c in rel])
                audit("assign_release", f"{me}: {len(rel)} customers")
                flash_and_refresh(f"Released {len(rel)} customers")
            except (RuntimeError, ConflictError, PermissionError) as err:
                st.error(f"⚠️ Could not save: {err}")


def _send_tab(me, ctx):
    if not has_permission("edit") or not has_permission("tasks"):
        st.warning("Editing delivery tasks is disabled for your account.")
        return
    st.caption("Tick the customers whose buns you have **sent**. Choose **My own delivery** when you deliver it yourself; no transport expense is required unless a taxi station is also recorded. Expenses can be filled later in step 3.")
    with st.form("send_list_options"):
        include_free = st.checkbox("Also show customers nobody has taken yet", key="send_free")
        search_send = st.text_input("🔎 Find customer to send", key="send_customer_search", max_chars=60)
        if st.form_submit_button("Apply delivery filter"):
            _reset_draft("send", me)
    assigned = ctx["assigned"]
    recs = [r for r in ctx["recs"] if r["Status"] not in NOT_TO_SEND
            and (assigned.get(r["Customer"]) == me or (include_free and r["Customer"] not in assigned))]
    if search_send.strip():
        q_send = search_send.strip().casefold()
        recs = [r for r in recs if q_send in str(r["Customer"]).casefold()
                or q_send in str(r.get("Province", "")).casefold()]
    if not recs and not _has_editor_draft("send", me):
        st.info("You have no customers to send. Choose your customers in step 1 first.")
        return
    rows = []
    for r in recs:
        ordered = None if pd.isna(r["កេស"]) else int(r["កេស"])
        packed, sent = int(r["Packed Cases"]), int(r["Sent Cases"])
        left = (packed - sent) if packed > sent else ((ordered - sent) if (ordered and ordered > sent) else 1)
        rows.append({"Sent ✅": False, "Customer": r["Customer"], "Cases": int(left), "Via": "Use default", "Taxi station": "",
                     "Note": "", "Status": r["Status"], "Province": r["Province"],
                     "Saved sent cases": sent, "Saved packed cases": packed, "Saved order cases": ordered if ordered is not None else -1})
    _reload_draft_button("send", me)
    d, editor_key = _task_editor_frame("send", pd.DataFrame(rows), me)
    st.caption("Tick several deliveries, edit cases and notes, then save once.")
    preferences = _form_preferences("send_defaults", me)
    via_values = via_options()
    verifier_values = ["-- Select Staff --"] + VERIFY_STAFF
    with st.form("batch_" + editor_key, clear_on_submit=False):
        c1, c2 = st.columns(2)
        default_via = c1.selectbox("Sent with (default)", via_values,
            index=via_values.index(preferences.get("via")) if preferences.get("via") in via_values else 0, key="send_via")
        verified_by = c2.selectbox("✅ Cases checked by", verifier_values,
            index=verifier_values.index(preferences.get("verifier")) if preferences.get("verifier") in verifier_values else 0, key="send_vby")
        select_all_send = st.checkbox("Include every customer shown when saving", key=editor_key + "_all")
        edited = st.data_editor(d, hide_index=True, height=min(560, 60 + 36 * len(d)), key=editor_key,
            column_order=["Sent ✅", "Customer", "Cases", "Via", "Taxi station", "Note", "Status"],
            disabled=["Customer", "Status", "Province", "Saved sent cases", "Saved packed cases", "Saved order cases"],
            column_config={"Sent ✅": st.column_config.CheckboxColumn("Sent ✅"),
                "Cases": st.column_config.NumberColumn("Cases", min_value=0, max_value=MAX_CASES, step=1),
                "Via": st.column_config.SelectboxColumn("Via", options=["Use default"] + via_options()),
                "Taxi station": st.column_config.TextColumn("Taxi station", max_chars=MAX_TEXT),
                "Note": st.column_config.TextColumn("Note", max_chars=MAX_TEXT)})
        submitted = st.form_submit_button("🚚 Save selected deliveries", type="primary")
    if submitted:
        if verified_by == "-- Select Staff --":
            st.error("❌ Please choose who checked the number of cases.")
            return
        preferences.update({"via": default_via, "verifier": verified_by})
        selected_rows = [r for r in edited.to_dict("records") if select_all_send or r["Sent ✅"]]
        fresh = {r["Customer"]: r for r in ctx["recs"]}
        blocked = [r["Customer"] for r in selected_rows if r["Customer"] not in fresh
                   or fresh[r["Customer"]]["Status"] in NOT_TO_SEND
                   or _int(fresh[r["Customer"]]["Sent Cases"]) != _int(r["Saved sent cases"])
                   or _int(fresh[r["Customer"]]["Packed Cases"]) != _int(r["Saved packed cases"])
                   or _int(fresh[r["Customer"]]["កេស"], -1) != _int(r["Saved order cases"], -1)
                   or (assigned.get(r["Customer"]) not in (None, me) and current_role() != "admin")]
        if blocked:
            st.error("These deliveries changed while you were selecting: " + ", ".join(blocked[:5]) + ". Reload this list before saving.")
            return
        out, take, total = [], [], 0
        for r in edited.to_dict("records"):
            cust, cases, via = r["Customer"], _int(r["Cases"]), r["Via"]
            via = default_via if via == "Use default" else via
            if not (select_all_send or r["Sent ✅"]) or cases <= 0 or cases > MAX_CASES or via not in via_options():
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
                try:
                    append_rows(ASSIGN_FILE, take)
                except Exception as assignment_error:
                    bot_log("warn", "Delivery assignments", str(assignment_error),
                            "deliveries saved successfully; assignments need review")
                    st.session_state["assignment_warning"] = "Deliveries were saved. Assignment updates failed; ask Admin to review. Do not resend these deliveries."
            waiting = sum(1 for o in out if o["Expense_Status"] == "Pending")
            audit("dispatch_bulk", f"{len(out)} customers, {total} cases, by {me}")
            _reset_draft("send", me)
            flash_and_refresh(f"Saved {len(out)} deliveries ({total} cases). {waiting} need expenses - fill them in step 3")
        except (RuntimeError, ConflictError, PermissionError) as err:
            bot_log("error", "Save dispatch (bulk)", str(err), "-")
            st.error(f"⚠️ Could not save: {err}")


def pending_expense_df(who, scope, include_done=False):
    """Deliveries still waiting for expenses. who = staff name or None (everyone); scope = Today | Last 7 days | All waiting."""
    df = read_raw(DATA_FILE, DISPATCH_COLS)
    if not include_done:
        df = df[df["Expense_Status"] == "Pending"]
    if who:
        df = df[(df["Handled_By"] == who) | (df["Local_Driver"] == who)]
    if scope == "Today":
        df = df[df["_dt"].dt.normalize() == pd.Timestamp(today_kh())]
    elif scope == "Last 7 days":
        df = df[df["_dt"] >= pd.Timestamp(today_kh() - timedelta(days=7))]
    return df.reset_index(drop=True)


def _expense_tab(me):
    if not has_permission("edit") or not has_permission("tasks"):
        st.warning("Editing delivery expenses is disabled for your account.")
        return
    is_admin = current_role() == "admin"
    st.caption("Fill in expenses for deliveries you already sent. Self-delivered orders need no transport expense unless a taxi station is recorded. Tick **Done** for each row you finish, then save.")
    with st.form("expense_filters"):
        c1, c2 = st.columns(2)
        scope = c1.radio("Show", ["Today", "Last 7 days", "All waiting"], horizontal=True, key="exp_scope")
        show_done = st.checkbox("Also show deliveries with no expense required / already done", key="exp_done")
        who = me
        if is_admin:
            pick = c2.selectbox("Handler", ["(everyone)"] + DELIVERY_HANDLERS, key="exp_who")
            who = None if pick == "(everyone)" else pick
        if st.form_submit_button("Apply expense filter"):
            _reset_draft("expenses", str((who, scope, show_done)))
    if not is_admin and me == "-- Select Staff --":
        st.info("Choose your name at the top first.")
        return
    df = pending_expense_df(who, scope, show_done)
    draft_scope = str((who, scope, show_done))
    if df.empty and not _has_editor_draft("expenses", draft_scope):
        st.success("Nothing is waiting for expenses. 🎉")
        return
    st.info(f"⏳ {len(df)} deliveries to review for expenses.")
    rows = [{"Done ✅": False, "Customer": r["Customer"], "When": str(r["Date"])[5:16], "Via": r["Local_Driver"],
             "Taxi station": "" if r["Taxi_Station"] in ("-", "") else r["Taxi_Station"],
             "Phnom Penh ៛": int(r["Phnom_Penh_Expense"]), "Taxi ៛": int(r["Taxi_Expense"]),
             "By": r["Handled_By"], "Date": r["Date"]} for r in df.to_dict("records")]
    _reload_draft_button("expenses", draft_scope)
    d, editor_key = _task_editor_frame("expenses", pd.DataFrame(rows), draft_scope)
    order = ["Done ✅", "Customer", "When", "Via", "Taxi station", "Phnom Penh ៛", "Taxi ៛"] + (["By"] if who is None else [])
    with st.form("batch_" + editor_key, clear_on_submit=False):
        edited = st.data_editor(d, hide_index=True, height=min(560, 60 + 36 * len(d)), key=editor_key,
            column_order=order, disabled=["Customer", "When", "Via", "By", "Date"],
            column_config={"Done ✅": st.column_config.CheckboxColumn("Done ✅"),
                "Taxi station": st.column_config.TextColumn("Taxi station", max_chars=MAX_TEXT),
                "Phnom Penh ៛": st.column_config.NumberColumn("Phnom Penh ៛", min_value=0, max_value=MAX_RIEL, step=500),
                "Taxi ៛": st.column_config.NumberColumn("Taxi ៛", min_value=0, max_value=MAX_RIEL, step=500)})
        submitted = st.form_submit_button("💾 Save selected expenses", type="primary")
    if submitted:
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
            _reset_draft("expenses", draft_scope)
            flash_and_refresh(f"Saved expenses for {len(updates)} deliveries (៛{total:,})")
        except (ValueError, RuntimeError, ConflictError, PermissionError) as err:
            st.error(f"❌ {err}")


# ---- Journal fill sheet: expenses/driver in the same order as the Sale Journal ----
DRIVER_CODE = {"ងិន វុទ្ធា": "VUTHEA", "អួន តួ": "TOU"}      # name in this app -> code typed in journal column អ្នកដឹក
JF_COLS = ["Date", "Customer", "Invoice", "ចំនួនកេស", "កេស (journal)", "អ្នកដឹក", "សេវាដឹក (ចំណាយ)",
           "សេវាតាក់ស៊ី (ចំណាយ)", "Taxi station", "Note"]


def build_journal_fill(d_from, d_to):
    """(fill_df, unmatched_df, error) for deliveries between two dates.
    One row per journal invoice, in journal order. A customer's expenses for one day go on its FIRST invoice
    of that day (0 on the others) so nothing is counted twice - the same way the journal is filled by hand.
    ចំនួនកេស = cases SENT (from the Delivery tab). When a customer has several invoices that day, the cases sent are
    shared over the invoices by the journal's កេស, so the column adds up to exactly what was sent.
    កេស (journal) = the cases written in the journal for that invoice (to compare)."""
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
                            "note": " / ".join(dict.fromkeys(notes)), "cases": int(g["Cases"].sum())}
    jr = snap["journal"]
    jr = jr[(jr["Date"] >= d_from) & (jr["Date"] <= d_to)]
    # cases sent for each journal row: the customer's sent cases shared over its invoices of that day
    members = {}
    for idx, r in jr.iterrows():
        members.setdefault((r["Date"], r["Customer"]), []).append(idx)
    sent_cases = {}
    for key, idxs in members.items():
        a = agg.get(key)
        if a is None:
            continue
        w = [max(float(jr.at[i, "Cases"]), 0) if pd.notna(jr.at[i, "Cases"]) else 0 for i in idxs]
        if sum(w) == 0:
            w = [1] * len(idxs)
        parts = [int(a["cases"] * x / sum(w)) for x in w]
        parts[0] += a["cases"] - sum(parts)
        sent_cases.update(zip(idxs, parts))
    rows, used = [], set()
    for idx, r in jr.iterrows():
        key = (r["Date"], r["Customer"])
        a = agg.get(key)
        first = a is not None and key not in used
        if a is not None:
            used.add(key)
        rows.append({"Date": r["Date"], "Customer": r["Customer"], "Invoice": r["Invoice"],
                     "ចំនួនកេស": sent_cases.get(idx),
                     "កេស (journal)": (int(r["Cases"]) if pd.notna(r["Cases"]) else None),
                     "អ្នកដឹក": a["drv"] if a else "",
                     "សេវាដឹក (ចំណាយ)": (a["pp"] if first else (0 if a else None)),
                     "សេវាតាក់ស៊ី (ចំណាយ)": (a["taxi"] if first else (0 if a and a["taxi"] else None)),
                     "Taxi station": a["station"] if first else "", "Note": a["note"] if first else ""})
    fill = pd.DataFrame(rows, columns=JF_COLS)
    for c in ("ចំនួនកេស", "កេស (journal)"):
        fill[c] = pd.array(fill[c].tolist(), dtype="Int64")
    miss = [{"Date": k[0], "Customer": k[1], "ចំនួនកេស": v["cases"], "អ្នកដឹក": v["drv"],
             "សេវាដឹក (ចំណាយ)": v["pp"], "សេវាតាក់ស៊ី (ចំណាយ)": v["taxi"], "Taxi station": v["station"], "Note": v["note"]}
            for k, v in agg.items() if k not in used]
    return fill, pd.DataFrame(miss), None


DRIVER_TOTAL_COLS = ["អ្នកដឹក", "Name", "Deliveries", "Customers", "ចំនួនកេស", "កេស via taxi",
                     "សេវាដឹក ៛", "សេវាតាក់ស៊ី ៛"]


def build_driver_totals(d_from, d_to):
    """(by_driver, by_day): how many កេស each driver sent between two dates.
    Uses ALL saved deliveries in those dates (also the ones whose customer is not found in the journal).
    Own drivers show their journal code (VUTHEA / TOU); Grab/TukTuk is its own line."""
    disp = read_raw(DATA_FILE, DISPATCH_COLS)
    if disp.empty or "_dt" not in disp.columns:
        return None, None
    day = disp["_dt"].dt.normalize()
    disp = disp[(day >= pd.Timestamp(d_from)) & (day <= pd.Timestamp(d_to))].copy()
    if disp.empty:
        return None, None
    disp["_day"] = disp["_dt"].dt.date
    names = {code: name for name, code in DRIVER_CODE.items()}

    def who(v):
        v = str(v).strip()
        return DRIVER_CODE.get(v) or (v if v not in ("", "-") else "(not set)")
    disp["_who"] = disp["Local_Driver"].map(who)
    disp["_k"] = disp["_day"].astype(str) + "|" + disp["Customer"].astype(str).map(lambda x: re.sub(r"\s+", " ", x).strip())
    by_taxi = disp["Taxi_Station"].astype(str).str.strip().map(lambda x: x not in ("", "-"))
    disp["_taxi_cases"] = disp["Cases"].where(by_taxi, 0)
    g = disp.groupby("_who", sort=False).agg(
        Deliveries=("Customer", "count"), Customers=("_k", "nunique"), cases=("Cases", "sum"),
        taxi_cases=("_taxi_cases", "sum"), pp=("Phnom_Penh_Expense", "sum"), tx=("Taxi_Expense", "sum")).reset_index()
    g = g.sort_values("cases", ascending=False)
    out = pd.DataFrame({"អ្នកដឹក": g["_who"], "Name": g["_who"].map(lambda x: names.get(x, "")),
                        "Deliveries": g["Deliveries"], "Customers": g["Customers"], "ចំនួនកេស": g["cases"],
                        "កេស via taxi": g["taxi_cases"], "សេវាដឹក ៛": g["pp"], "សេវាតាក់ស៊ី ៛": g["tx"]})
    total = {"អ្នកដឹក": "TOTAL", "Name": "", "Deliveries": int(out["Deliveries"].sum()),
             "Customers": int(disp["_k"].nunique()), "ចំនួនកេស": int(out["ចំនួនកេស"].sum()),
             "កេស via taxi": int(out["កេស via taxi"].sum()), "សេវាដឹក ៛": int(out["សេវាដឹក ៛"].sum()),
             "សេវាតាក់ស៊ី ៛": int(out["សេវាតាក់ស៊ី ៛"].sum())}
    out = pd.concat([out, pd.DataFrame([total])], ignore_index=True)[DRIVER_TOTAL_COLS]
    piv = disp.pivot_table(index="_day", columns="_who", values="Cases", aggfunc="sum", fill_value=0).astype(int)
    piv["TOTAL"] = piv.sum(axis=1)
    piv = piv.reset_index().rename(columns={"_day": "Date"})
    return out, piv


def _journal_fill_panel():
    with st.expander("📋 Journal fill sheet - driver & expenses for the Sale Journal"):
        st.caption("Gives អ្នកដឹក, សេវាដឹក (ចំណាយ) and សេវាតាក់ស៊ី (ចំណាយ) in the same order as your journal, "
                   "matched by date + customer. ចំនួនកេស shows the cases sent. Copy the 3 columns into the journal "
                   "(or look them up by Invoice).")
        c1, c2 = st.columns(2)
        d_from = c1.date_input("From", value=today_kh().replace(day=1), key="jf_from")
        d_to = c2.date_input("To", value=today_kh(), key="jf_to")
        if st.button("Build journal fill sheet", key="jf_go"):
            fill, miss, err = build_journal_fill(d_from, d_to)
            if err:
                st.warning(err)
                return
            drv, drv_day = build_driver_totals(d_from, d_to)
            st.session_state["jf_result2"] = (fill, miss, drv, drv_day, d_from, d_to)
        res = st.session_state.get("jf_result2")
        if not res:
            return
        fill, miss, drv, drv_day, r_from, r_to = res
        has = fill[(fill["អ្នកដឹក"] != "") | fill["ចំនួនកេស"].notna() | fill["សេវាដឹក (ចំណាយ)"].notna()
                   | fill["សេវាតាក់ស៊ី (ចំណាយ)"].notna()]
        sent_total = int(drv.iloc[-1]["ចំនួនកេស"]) if drv is not None and not drv.empty else 0
        in_table = int(fill["ចំនួនកេស"].fillna(0).sum())
        st.success(f"{len(has)} journal rows have delivery data (of {len(fill)} rows in range). "
                   f"Pending expenses are 0 until you fill them in the Delivery tab.")
        st.markdown(f"<div class='hk-kpis'><span class='hk-pill'>📦 កេស sent <b>{sent_total}</b></span>"
                    f"<span class='hk-pill'>🧾 In the table below <b>{in_table}</b></span>"
                    f"<span class='hk-pill'>❓ Not found in journal <b>{sent_total - in_table}</b></span></div>",
                    unsafe_allow_html=True)
        if drv is not None:
            st.markdown("**👷 Total by driver - how many កេស each one sent**")
            show_df(drv)
            if drv_day is not None and len(drv_day) > 1:
                with st.expander("📅 By driver and by day"):
                    show_df(drv_day)
        buf = io.BytesIO()
        with pd.ExcelWriter(buf, engine="openpyxl") as w:
            fill.to_excel(w, index=False, sheet_name="Journal_Fill")
            if drv is not None:
                drv.to_excel(w, index=False, sheet_name="By_driver")
                drv_day.to_excel(w, index=False, sheet_name="By_driver_by_day")
            if not miss.empty:
                miss.to_excel(w, index=False, sheet_name="Not_in_journal")
        st.download_button("📥 Download journal fill sheet (Excel)", data=buf.getvalue(),
                           file_name=f"Journal_Fill_{r_from}_{r_to}.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
        show_df(has)
        if not miss.empty:
            st.warning(f"{len(miss)} delivery(ies) were not found in the journal (name or date differs):")
            show_df(miss)


def _delivery_log():
    """Today's operation records, with detail and report features controlled per user."""
    can_view = has_permission("view")
    can_reports = has_permission("reports")
    if current_role() == "admin" and has_permission("edit"):
        with st.expander("🛠️ Admin: Fix or Edit Today's Dispatches"):
            admin_editor(DATA_FILE, DISPATCH_COLS, DISPATCH_NUM_COLS, key="disp",
                         label_cols=["Customer", "Cases"])

    if can_reports:
        _journal_fill_panel()
    elif can_view:
        st.caption("Journal fill report is disabled for your account.")

    st.subheader("📊 Today's Operations Log")
    df_today = rows_for_day(read_raw(DATA_FILE, DISPATCH_COLS), today_kh())
    total_expense = int(df_today["Phnom_Penh_Expense"].sum() + df_today["Taxi_Expense"].sum()) if not df_today.empty else 0
    waiting = int((df_today["Expense_Status"] == "Pending").sum()) if not df_today.empty else 0
    if can_reports:
        m1, m2, m3, m4 = st.columns(4)
        kpi(m1, "Total Slips Today", len(df_today))
        kpi(m2, "Total Cases Dispatched (សរុបចំនួនកេស)", int(df_today["Cases"].sum()) if not df_today.empty else 0)
        kpi(m3, "Total Expenses Today (៛)", f"{total_expense:,}")
        kpi(m4, "⏳ Expenses still to fill", waiting)
    if df_today.empty:
        st.info("No deliveries logged today yet.")
        return

    if can_reports:
        buf = io.BytesIO()
        with pd.ExcelWriter(buf, engine="openpyxl") as writer:
            df_today[DISPATCH_COLS].to_excel(writer, index=False, sheet_name="Ops_Log")
        st.download_button("📥 Download Today's Expenses Log (Excel)", data=buf.getvalue(),
                           file_name=f"Operations_Expenses_{today_kh()}.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    if can_view:
        show_df(df_today[["Handled_By", "Customer", "Cases", "Note", "Local_Driver", "Taxi_Station",
                          "Phnom_Penh_Expense", "Taxi_Expense", "Expense_Status", "Verified_By"]])
    if can_reports:
        st.markdown("**👷 Dispatch summary per staff (today)**")
        per_staff = df_today.groupby("Handled_By").agg(
            Slips=("Customer", "count"), Cases=("Cases", "sum"),
            Expenses=("Phnom_Penh_Expense", "sum"), Taxi=("Taxi_Expense", "sum"),
            Waiting=("Expense_Status", lambda x: int((x == "Pending").sum()))).reset_index()
        show_df(per_staff)

    if can_view:
        st.markdown("**🔎 Check completed delivery tasks by staff**")
        recorded_staff = [str(x).strip() for x in df_today["Handled_By"].dropna().tolist()
                          if str(x).strip() and str(x).strip() not in ("-", "nan", "None")]
        staff_options = ["-- Select Staff --"] + sorted(set(DELIVERY_HANDLERS).union(recorded_staff))
        selected_staff = st.selectbox(
            "Select staff name to see their completed tasks",
            staff_options,
            key="dispatch_completed_staff",
        )
        if selected_staff == "-- Select Staff --":
            st.caption("Choose a staff member to see the customers and cases they dispatched today.")
        else:
            staff_tasks = df_today[df_today["Handled_By"].astype(str).str.strip() == selected_staff].copy()
            if staff_tasks.empty:
                st.info(f"No delivery tasks recorded for {selected_staff} today.")
            else:
                cases_done = int(pd.to_numeric(staff_tasks["Cases"], errors="coerce").fillna(0).sum())
                expense_waiting = int((staff_tasks["Expense_Status"] == "Pending").sum())
                k1, k2, k3 = st.columns(3)
                kpi(k1, "Completed delivery slips", len(staff_tasks))
                kpi(k2, "Cases dispatched", cases_done)
                kpi(k3, "Expenses still pending", expense_waiting)
                task_cols = [c for c in ["Time", "Customer", "Cases", "Note", "Local_Driver", "Taxi_Station",
                                         "Phnom_Penh_Expense", "Taxi_Expense", "Expense_Status", "Verified_By"]
                             if c in staff_tasks.columns]
                show_df(staff_tasks[task_cols])

def _dispatch_body():
    if not has_permission("tasks") or not has_permission("edit"):
        st.warning("Delivery task editing is disabled for your account.")
        return
    st.markdown("### 🚚 Delivery")
    linked_staff = staff_name_for_user()
    default_staff_index = DELIVERY_HANDLERS.index(linked_staff) + 1 if linked_staff in DELIVERY_HANDLERS else 0
    me = st.selectbox("👷 I am (choose your name once — office staff or delivery driver)",
                      ["-- Select Staff --"] + DELIVERY_HANDLERS, index=default_staff_index, key="me_staff")
    st.caption("Both delivery drivers can select their own names here, choose customers, mark deliveries as sent, and check any expenses under their names.")
    ctx = delivery_context()
    mine = [r for r in ctx["recs"] if ctx["assigned"].get(r["Customer"]) == me and r["Status"] not in NOT_TO_SEND]
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
    if not has_permission("tasks"):
        st.error("Task access is turned off for your account. Ask Admin to enable it.")
        return
    if not has_permission("edit"):
        if not has_permission("view") and not has_permission("reports"):
            st.warning("Task access is enabled, but View, Editing, and Reports are all turned off.")
            return
        safe_render(_delivery_log, "Delivery read-only log")
        return
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


DASH_COLUMNS = ["🔥", "Customer", "In Master", "Area", "Province", "Region", "Invoice", "Status", "កេស", "Packed Cases", "Packed Note", "Prepared By",
                "Assigned To", "Sent Cases", "Left to send", "Sent Note", "Handled By", "Verified By", "Driver/Station", "Taxi Station", "Taxi No.", "Journal Note", "Moved/Cancel Reason", "Note", "Time", "Source", "Map status", "Map link", "Directions", "Location ID"]


def build_report(selected_date):
    try:
        report_map_registry = load_map_registry()
    except Exception:
        report_map_registry = None
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

    # customers moved here from yesterday (they may not be in today's journal)
    holds = current_holds(selected_date)
    finals = current_final(selected_date)
    finals_p = current_final(selected_date, "Packed")
    for cust, h in current_holds(selected_date - timedelta(days=1)).items():
        if h["action"] != "Tomorrow":
            continue
        prev = f"📅 Moved from {selected_date - timedelta(days=1)}" + (f" ({h['reason']})" if h["reason"] not in ("", "-") else "")
        if cust in scheduled:
            scheduled[cust]["remark"] = _join_unique([scheduled[cust]["remark"], prev], sep=" / ")
            if h["cases"] > 0:
                scheduled[cust]["cases"] = (scheduled[cust]["cases"] or 0) + h["cases"]
        else:
            scheduled[cust] = {"cases": h["cases"] or None, "invoice": "-", "remark": prev}

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
        notes = [str(x).strip() for x in g["Note"] if str(x).strip() not in ("", "-")]
        stations = [str(x).strip() for x in g["Taxi_Station"] if str(x).strip() not in ("", "-")]
        verifiers = [str(x).strip() for x in g["Verified_By"].tolist()
                     if str(x).strip() not in ("", "-", "nan", "None")]
        sent_info[cust] = {"cases": int(g["Cases"].sum()), "driver": driver, "note": str(last["Note"]),
                           "station": " / ".join(dict.fromkeys(stations)), "taxi_no": " / ".join(dict.fromkeys(notes)),
                           "by": str(last["Handled_By"]), "verified": " / ".join(dict.fromkeys(verifiers)) or "-",
                           "time": last["Time"]}

    areas = areas_lookup(snap)
    overrides = load_location_overrides()
    assigned = current_assignments(selected_date)
    master_names = {norm_name(n) for n in snap["customers"]} if snap else set()
    ignore = {norm_name(n) for n in IGNORE_NEW}
    rows = []
    for cust in set(scheduled) | set(pack_info) | set(sent_info) | set(finals) | set(finals_p):
        p, s, info = pack_info.get(cust), sent_info.get(cust), scheduled.get(cust)
        area, province, region, _how = resolve_location(cust, areas.get(norm_name(cust)), overrides.get(norm_name(cust)))
        if province in ("Unknown", "Unknown province") and report_map_registry is not None:
            imported_province = mapped_customer_province(cust, report_map_registry)
            if imported_province in PROVINCES:
                province = imported_province
                area = PP if province == PP else "Province"
                region = region_of(province)
        finp = finals_p.get(cust)
        sys_packed = p["cases"] if p else 0
        packed = finp["cases"] if finp else sys_packed          # a hand-set FINAL packed number replaces the packing logs
        sys_sent = s["cases"] if s else 0
        fin = finals.get(cust)
        sent = fin["cases"] if fin else sys_sent               # a hand-set FINAL number replaces the sum of the delivery slips
        ordered = info["cases"] if info else None
        remark = info["remark"] if info else "-"
        target = packed if packed > 0 else (ordered or 0)
        if sent > 0 or (s and not fin):
            status = "🔵 Part sent" if (target > 0 and sent < target) else "✅ Sent"
        elif p or finp:
            status = "🟠 Packing" if (p and not finp and "In Progress" in p["status"]) else "🟡 Ready for Delivery"
        else:
            status = "⏳ Pending"
        h = holds.get(cust)
        if h:
            status = ST_MOVED if h["action"] == "Tomorrow" else ST_CANCEL
        urgent = any(w.upper() in remark.upper() for w in URGENT_WORDS)
        rows.append({
            "🔥": "🔥" if urgent else "", "Customer": cust,
            "In Master": "🆕 NEW" if (master_names and norm_name(cust) not in master_names and norm_name(cust) not in ignore) else "✅",
            "Area": AREA_LABEL[area], "Province": province,
            "Region": region, "Invoice": info["invoice"] if info else "-",
            "Status": status, "កេស": ordered,
            "Packed Cases": packed, "Packed Note": (f"✏️ final packed {packed} (logs total {sys_packed}) by {finp['by']}: {finp['reason']}" if finp else ""),
            "Prepared By": p["by"] if p else (finp["by"] if finp else "-"), "Assigned To": assigned.get(cust, "-"),
            "Sent Cases": sent, "Left to send": (max(target - sent, 0) if (s or fin) else 0),
            "Sent Note": (f"✏️ final {sent} (slips total {sys_sent}) by {fin['by']}: {fin['reason']}" if fin else ""), "Handled By": s["by"] if s else "-",
            "Verified By": s["verified"] if s else "-",
            "Driver/Station": s["driver"] if s else "-",
            "Taxi Station": (s["station"] if s else "") if area == "Province" else "",
            "Taxi No.": (s["taxi_no"] if s else "") if area == "Province" else "",
            "Journal Note": remark,
            "Moved/Cancel Reason": (f"{h['reason']} (by {h['by']})" if h else ""),
            "Note": s["note"] if s else "-", "Time": s["time"] if s else "-",
            "Source": "Journal" if info else "⚠️ Not in journal",
        })
    if not rows:
        return pd.DataFrame(), cases_found, err
    df = pd.DataFrame(rows)
    try:
        df = attach_customer_maps(df, report_map_registry)
    except Exception as map_error:
        bot_log("error", "Customer maps", str(map_error)[:180], "delivery records remain available")
        for col in ("Map status", "Map link", "Directions", "Location ID"):
            df[col] = "Map registry unavailable" if col == "Map status" else ""
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
                Part_sent=("Status", lambda x: int((x == "🔵 Part sent").sum())),
                Ordered=("កេស", lambda x: int(x.fillna(0).sum())),
                Packed=("Packed Cases", "sum"), Sent=("Sent Cases", "sum")).reset_index()
    held = g["Status"].apply(lambda x: int(x.isin([ST_MOVED, ST_CANCEL]).sum())).values
    out["Waiting"] = out["Customers"] - out["Delivered"] - held
    out["% delivered"] = (out["Delivered"] * 100 // out["Customers"].clip(lower=1)).astype(int).astype(str) + "%"
    return out.sort_values("Customers", ascending=False).reset_index(drop=True)


def map_data(df, metric):
    """One row per Cambodian province (all 25 + Phnom Penh) with the chosen number for the map."""
    agg = {}
    if not df.empty:
        part = df[df["Province"].isin(PROVINCES)]
        for prov, g in part.groupby("Province"):
            delivered = int((g["Status"] == "✅ Sent").sum())
            held = int(g["Status"].isin([ST_MOVED, ST_CANCEL]).sum())
            agg[prov] = {"customers": len(g), "waiting": len(g) - delivered - held, "ordered": int(g["កេស"].fillna(0).sum()),
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


def current_final(day, kind="Sent"):
    """{customer: {"cases","reason","by"}} - the FINAL number of កេស sent (kind="Sent") or packed (kind="Packed"),
    set by hand. The last Final<kind> / Final<kind>Reset of each customer wins."""
    df = rows_for_day(read_raw(HOLD_FILE, HOLD_COLS), day)
    out = {}
    for r in df.to_dict("records"):
        if r["Action"] == f"Final{kind}":
            out[r["Customer"]] = {"cases": max(_int(r["Cases"]), 0), "reason": str(r["Reason"]), "by": str(r["By"])}
        elif r["Action"] == ("FinalReset" if kind == "Sent" else f"Final{kind}Reset"):
            out.pop(r["Customer"], None)
    return out


def current_holds(day):
    """{customer: {"action","cases","reason","by"}} for a day. The last Tomorrow / Cancel / Restore of each customer wins."""
    df = rows_for_day(read_raw(HOLD_FILE, HOLD_COLS), day)
    out = {}
    for r in df.to_dict("records"):
        if r["Action"] in ("Tomorrow", "Cancel"):
            out[r["Customer"]] = {"action": r["Action"], "cases": _int(r["Cases"]), "reason": str(r["Reason"]), "by": str(r["By"])}
        elif r["Action"] == "Restore":
            out.pop(r["Customer"], None)
    return out


STATUS_STYLE = {"✅ Sent": ("#2e7d32", "#ffffff"), "🔵 Part sent": ("#1565c0", "#ffffff"),
                "🟡 Ready for Delivery": ("#f9a825", "#222222"), "🟠 Packing": ("#ef6c00", "#ffffff"),
                "⏳ Pending": ("#757575", "#ffffff"), "📅 Moved to tomorrow": ("#6a1b9a", "#ffffff"),
                "❌ Cancelled": ("#b71c1c", "#ffffff")}
COMPACT_COLUMNS = ["🔥", "Customer", "In Master", "Province", "Status", "កេស", "Packed Cases", "Sent Cases", "Left to send", "Verified By", "Taxi Station", "Taxi No.", "Assigned To", "Invoice", "Map link", "Directions", "Map status"]
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
             ("🔵 Part sent", "🔵 Part sent"), ("✅ Sent", "✅ Sent"), ("📅 Moved", ST_MOVED), ("❌ Cancelled", ST_CANCEL)]
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
        if r.get("Taxi No.") not in ("", "-", None):
            sent += f"<div class='hk-note'>🚕 Taxi no.: <b>{_e(r['Taxi No.'])}</b></div>"
    location_link = r.get("Directions") or r.get("Map link")
    if trusted_map_url(location_link):
        sent += f"<div class='hk-note'><a href='{_e(location_link)}' target='_blank' rel='noopener noreferrer'>📍 Open customer map / directions</a></div>"
    elif r.get("Map status") == "Repeated name — choose location":
        sent += "<div class='hk-note'>📍 Repeated name: Admin must choose the correct location.</div>"
    prep = f" · 👷 {_e(r['Prepared By'])}" if r["Prepared By"] not in ("-", "") else ""
    asg = f"<span>👤 {_e(r['Assigned To'])}</span>" if r.get("Assigned To") not in ("-", "", None) else ""
    return (f"<div class='hk-card' style='border-left:6px solid {bg}'>"
            f"<div class='hk-top'><span class='hk-name'>{'🔥 ' if r['🔥'] else ''}{_e(r['Customer'])}</span>"
            f"<span class='hk-badge' style='background:{bg};color:{fg}'>{_e(r['Status'])}</span></div>"
            f"<div class='hk-sub'>{_e(r['Area'])} · {_e(r['Province'])}{inv}{' · 🆕 NEW customer (not in master)' if r.get('In Master') == '🆕 NEW' else ''}</div>"
            f"<div class='hk-nums'><span>កេស <b>{ordered}</b></span><span>📦 <b>{int(r['Packed Cases'])}</b>{' ✏️' if r.get('Packed Note') else ''}{prep}</span>"
            f"<span>🚚 sent <b>{int(r['Sent Cases'])}</b>{' ✏️' if r.get('Sent Note') else ''}{(' · <b>' + str(int(r['Left to send'])) + ' left</b>') if r['Status'] == '🔵 Part sent' else ''}</span>{asg}</div>{note}{sent}</div>")


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


def render_cards(df, editable=False, df_report=None, selected_date=None):
    """Cards. With editable=True every card has a 'Check / Edit' button and the panel opens right under that card.
    Returns True when the open panel was drawn inside a card."""
    page = 30
    limit = st.session_state.get("card_limit", page)
    d = df.copy()
    d["_a"] = d["Area"].map(AREA_RANK)
    d["_g"] = d["Region"].map(_REGION_ORDER).fillna(99)
    d["_s"] = d["Status"].map(STATUS_RANK)
    d = d.sort_values(["_a", "_g", "Province", "_s", "Customer"]).drop(columns=["_a", "_g", "_s"])
    shown = d.head(limit)
    drawn = False
    if not editable:
        st.markdown(cards_html(shown), unsafe_allow_html=True)
    else:
        counts, last = shown.groupby(["Area", "Province"]).size().to_dict(), None
        for r in shown.to_dict("records"):
            key = (r["Area"], r["Province"])
            if key != last:
                last = key
                title = r["Area"] if r["Province"] == PP else f"{r['Area']} · {r['Province']}"
                st.markdown(f"<div class='hk-group'>{_e(title)} ({counts[key]})</div>", unsafe_allow_html=True)
            st.markdown(card_html(r), unsafe_allow_html=True)
            cust = r["Customer"]
            if st.button("✏️ Check / Edit", key=f"cardedit_{cust}"):
                st.session_state["sel_cust"] = cust
            if st.session_state.get("sel_cust") == cust:
                with st.container(border=True):
                    _update_panel(cust, df_report, selected_date)
                drawn = True
    st.caption(f"Showing {min(limit, len(d))} of {len(d)} customers")
    if len(d) > limit and st.button(f"⬇️ Show {page} more", key="card_more"):
        st.session_state["card_limit"] = limit + page
        try:
            st.rerun(scope="fragment")
        except TypeError:
            st.rerun()
    return drawn


def _reports_only_body():
    """For users allowed to see reports but not the general customer dashboard."""
    st.markdown("### 📑 Reports")
    selected_date = st.date_input("Select Report Date:", value=today_kh(), key="reports_only_date")
    df_report, cases_found, err = build_report(selected_date)
    if err:
        st.warning(f"Excel problem: {err}")
    if df_report.empty:
        st.info(f"No orders scheduled or found in the journal for {selected_date}.")
        return
    counts = df_report["Status"].value_counts()
    rows = [{"Metric": "Customers", "Value": len(df_report)},
            {"Metric": "Cases ordered", "Value": int(df_report["កេស"].fillna(0).sum())},
            {"Metric": "Cases packed", "Value": int(df_report["Packed Cases"].sum())},
            {"Metric": "Cases sent", "Value": int(df_report["Sent Cases"].sum())}]
    rows.extend({"Metric": status, "Value": int(counts.get(status, 0))} for status in STATUS_RANK)
    show_df(pd.DataFrame(rows))
    if not has_permission("reports"):
        return
    try:
        st.download_button("📥 Download detailed report (Excel)", data=build_report_excel(df_report, selected_date),
                           file_name=f"Master_Report_{selected_date}.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    except Exception as e:
        st.warning(f"Could not build Excel report: {e}")


def _dashboard_body():
    if not has_permission("view"):
        if has_permission("reports"):
            _reports_only_body()
        else:
            st.info("Dashboard viewing is turned off for your account. Ask Admin to enable View or Reports.")
        return
    # Dashboard customer-update panels change packing/delivery status, so require both Tasks and Editing.
    can_edit = has_permission("edit") and has_permission("tasks")
    can_reports = has_permission("reports")
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
    total, n_sent = len(df_scope) - int(counts.get(ST_CANCEL, 0)), int(counts.get("✅ Sent", 0))
    total = max(total, 1)
    st.markdown(kpi_strip(counts, total), unsafe_allow_html=True)
    with st.expander("ℹ️ What do the statuses mean?"):
        st.markdown(
            "- ⏳ **Pending** - ordered in the journal, nothing packed yet\n"
            "- 🟠 **Packing** - being packed now\n"
            "- 🟡 **Ready** - packed, waiting to be sent\n"
            "- 🔵 **Part sent** - *some* of the កេស were sent but **not all yet** (the card shows how many are left). "
            "Send the rest, or move the rest to tomorrow.\n"
            "- ✅ **Sent** - everything was sent (or the customer picked it up)\n"
            "- 📅 **Moved to tomorrow** / ❌ **Cancelled** - not delivered today\n\n"
            "🏪 If the customer collects it themselves, choose **Customer pick-up** as the driver when you save the delivery.")
    st_keys = [k for k in STATUS_RANK if int(counts.get(k, 0)) > 0]
    pick_one = st.radio("👆 Click a status to see its customers in the table", ["All"] + st_keys, horizontal=True,
                        key="dash_status_pick",
                        format_func=lambda k: f"All ({total})" if k == "All" else f"{k.split(' ')[0]} {k.split(' ', 1)[1]} ({int(counts.get(k, 0))})")
    try:
        st.progress(n_sent / total, text=f"Delivered {n_sent} of {total} customers ({n_sent * 100 // total}%)")
    except TypeError:
        st.progress(n_sent / total)

    if can_reports:
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

    if has_permission("edit"):
        _new_customers_panel(df_report, selected_date)

    # ---- search + display style ----
    c1, c2, c3 = st.columns([3, 2, 2])
    q = c1.text_input("🔎 Search", key="dash_q", max_chars=60,
                      placeholder="customer, invoice, province, taxi station, taxi no., staff... (several words = all must match)")
    display = c2.radio("Display", ["📱 Cards", "🖥️ Table"], horizontal=True, index=0 if mobile else 1, key="dash_display")
    with c3:
        st.write("")
        if can_reports:
            try:
                st.download_button("📥 Download detailed report (Excel)", data=build_report_excel(df_report, selected_date),
                                   file_name=f"Master_Report_{selected_date}.xlsx",
                                   mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            except Exception as e:
                st.warning(f"Could not build Excel report: {e}")
        else:
            st.caption("Report download disabled")

    with st.expander("🎚️ Filters: region, province, verifier"):
        pick_status = [] if pick_one == "All" else [pick_one]
        pick_region = st.multiselect("Region filter", [r for r in REGIONS if r in set(df_scope["Region"])],
                                     key="dash_region", placeholder="All regions")
        pick_prov = st.multiselect("Province filter", sorted(set(df_scope["Province"])), key="dash_prov",
                                   placeholder="All provinces")
        verifier_values = sorted({str(v).strip() for v in df_scope["Verified By"].dropna()
                                  if str(v).strip() not in ("", "-", "nan", "None")})
        verifier_filter = st.selectbox("Cases verified by", ["All verifiers"] + verifier_values,
                                       key="dash_verified_filter")

    df_view = df_scope
    if pick_region:
        df_view = df_view[df_view["Region"].isin(pick_region)]
    if pick_prov:
        df_view = df_view[df_view["Province"].isin(pick_prov)]
    if verifier_filter != "All verifiers":
        df_view = df_view[df_view["Verified By"].astype(str).str.contains(verifier_filter, case=False, regex=False, na=False)]
    if q.strip():
        hay = df_view[["Customer", "Invoice", "Province", "Region", "Taxi Station", "Taxi No.", "Handled By",
                       "Prepared By", "Assigned To", "Driver/Station", "Verified By", "Status"]].astype(str).agg(" ".join, axis=1)
        m = pd.Series(True, index=df_view.index)
        for word in q.strip().split():
            m &= hay.str.contains(word, case=False, regex=False, na=False)
        df_view = df_view[m]
        st.caption(f"🔎 {len(df_view)} customer(s) found")
    if pick_status:
        df_view = df_view[df_view["Status"].isin(pick_status)]
    df_view = df_view.reset_index(drop=True)

    if not cases_found:
        st.caption(f"ℹ️ No column '{JOURNAL_CASES_HEADER}' found in the journal, so ordered cases are empty. "
                   "Change JOURNAL_CASES_HEADER at the top of the file if your header is different.")
    # a different list (new filter / search / date) must not keep the row that was ticked in the old list
    sig = (str(selected_date), view, pick_one, q.strip(), tuple(pick_region), tuple(pick_prov), verifier_filter, display, len(df_view))
    if st.session_state.get("dash_sig") != sig:
        st.session_state["dash_sig"] = sig
        st.session_state["clear_sel"] = True
    if st.session_state.pop("clear_sel", False):
        st.session_state.pop("dash_table", None)

    event = None
    shown_inline = False
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
            "Taxi Station": st.column_config.TextColumn("Taxi Station", width="medium"),
            "Taxi No.": st.column_config.TextColumn("Taxi No. (phone/plate)", width="medium"),
            "Map link": st.column_config.LinkColumn("Open map", display_text="Open map"),
            "Directions": st.column_config.LinkColumn("Directions", display_text="Directions"),
        }
        cols = DASH_COLUMNS if all_cols else COMPACT_COLUMNS
        event = show_df(df_view[cols], height=430, key="dash_table", selectable=can_edit, column_config=cfg)
    else:
        shown_inline = render_cards(df_view, editable=can_edit, df_report=df_report, selected_date=selected_date)

    if not can_edit:
        return
    if event is None and not table_mode:
        pass                                            # cards view: every card has its own Check / Edit button
    elif event is None:                                 # old Streamlit without row-click: pick from a list
        status_of = dict(zip(df_view["Customer"], df_view["Status"]))
        pick = st.selectbox("✏️ Update a customer (type to search)", ["--"] + df_view["Customer"].tolist()[:400],
                            format_func=lambda c: c if c == "--" else f"{status_of.get(c, '')}  {c}", key="pick_old")
        if pick != "--":
            st.session_state["sel_cust"] = pick
        else:
            st.session_state.pop("sel_cust", None)
    else:
        rows_sel = [i for i in event.selection.rows if 0 <= i < len(df_view)]   # old selection can be longer than the new list
        if rows_sel:
            st.session_state["sel_cust"] = df_view.iloc[rows_sel[0]]["Customer"]

    selected = st.session_state.get("sel_cust")
    if selected in set(df_report["Customer"]) and not shown_inline:
        _update_panel(selected, df_report, selected_date)


def _update_panel(selected, df_report, selected_date):
    """Check / edit one customer: packing, sending, move to tomorrow / cancel."""
    if not has_permission("edit") or not has_permission("view") or not has_permission("tasks"):
        st.info("Editing this customer is disabled for your account or Task access is turned off.")
        return

    st.markdown("---")
    h1, h2 = st.columns([5, 1])
    h1.subheader(f"✏️ Update: {selected}")
    if h2.button("✖ Close", key=f"close_panel_{selected}"):
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
    map_link = p_row.get("Directions") or p_row.get("Map link")
    if trusted_map_url(map_link):
        st.link_button("Open customer map / directions", map_link)
    else:
        st.caption("Customer location: " + str(p_row.get("Map status", "not matched")))
    if p_row["Journal Note"] not in ("-", ""):
        st.warning(f"📌 Journal note: {p_row['Journal Note']}")
    pack_default = max((ordered_n or 0) - packed_n, 0) or 1
    send_default = (target_n - sent_n) if (target_n - sent_n) > 0 else 1

    st.markdown(f"#### 🚚 Final sent: **{sent_n} កេស**  ·  ordered {ordered_n if ordered_n is not None else '-'}  ·  "
                f"packed {packed_n}  ·  left to send **{max(target_n - sent_n, 0)}**"
                + (f"   \n✏️ {p_row['Sent Note']}" if p_row["Sent Note"] else "")
                + (f"   \n✏️ {p_row['Packed Note']}" if p_row["Packed Note"] else ""))
    t_pack, t_send, t_final, t_hold = st.tabs(["📦 Step 1: Packing (who prepared the buns)",
                                               "🚚 Step 2: Send (who delivered + verify កេស)",
                                               "✏️ Edit final packed / sent",
                                               "📅 Move to tomorrow / ❌ Cancel"])
    with t_pack:
        packing_form(f"dash_pack_{selected}_{pack_default}", fixed_customer=selected, default_cases=pack_default)
    with t_send:
        st.caption("Check the កេស number (you can edit it), choose who verified it, then save.")
        dispatch_form(f"dash_send_{selected}_{send_default}", fixed_customer=selected,
                      default_cases=send_default, verify=True)
    with t_final:
        _final_panel(selected, p_row)
    with t_hold:
        _hold_panel(selected, p_row, target_n - sent_n)


IMPORT_HEADERS = ["Prefix ID", "Customer ID", "Customer Name", "Customer Name (Second Language)", "Currency Code",
                  "Receivable Account", "Price Code", "Customer Group Code", "Payment Term Code", "Payment Method Code",
                  "Customer Zone Code", "Credit Limit", "Contact Name", "Telephone 1", "Telephone 2", "Email", "Fax", "Website",
                  "Note", "Tax Number", "Profile Picture", "Invoice to Address", "House No", "Street", "Village", "Commune",
                  "District / City", "Province / Capital", "Country / Region",
                  "Quotation / Sales Order picks up price from latest order", "Sales Invoicing picks up price from latest invoice",
                  "Allow issuing invoice over credit limit", "Allow issuing invoice over due date", "Inactive"]
TYPE_GENERAL, TYPE_DEALER = "General customer", "Dealer"


def new_customer_names(snap, day=None):
    """Names typed in the journal that are not in the Master List (optionally only one day). Sorted, no repeats."""
    if not snap:
        return []
    master = {norm_name(n) for n in snap["customers"]}
    ignore = {norm_name(n) for n in IGNORE_NEW}
    j = snap["journal"]
    if day is not None:
        j = j[j["Date"] == day]
    out = {}
    for n in j["Customer"]:
        k = norm_name(n)
        if k and k not in master and k not in ignore:
            out.setdefault(k, n)
    return sorted(out.values(), key=str.casefold)


def build_master_upload(rows, start_no):
    """rows = [(name, type, phone)]. Excel in the same layout as your customer import sheet."""
    recs = []
    for i, (name, typ, phone) in enumerate(rows):
        r = {h: None for h in IMPORT_HEADERS}
        r.update({"Prefix ID": "DEFAULT", "Customer ID": f"C-{start_no + i:05d}", "Customer Name": name,
                  "Customer Name (Second Language)": name, "Currency Code": "KHR", "Receivable Account": "105010",
                  "Price Code": "DEALER", "Customer Group Code": "DEALER" if typ == TYPE_DEALER else "GEN_KHR",
                  "Payment Term Code": "1D", "Payment Method Code": "BANK", "Credit Limit": 0,
                  "Telephone 1": phone or None,
                  "Quotation / Sales Order picks up price from latest order": 0,
                  "Sales Invoicing picks up price from latest invoice": 0,
                  "Allow issuing invoice over credit limit": 0, "Allow issuing invoice over due date": 0, "Inactive": 0})
        recs.append(r)
    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine="openpyxl") as w:
        pd.DataFrame(recs, columns=IMPORT_HEADERS).to_excel(w, index=False, sheet_name="SHEET1")
    return buf.getvalue()


def _new_customers_panel(df_report, selected_date):
    """Alert for names that sales typed in the journal but that are not in the Master List yet."""
    if not has_permission("edit"):
        return
    snap, _, _, _ = current_snapshot()
    if not snap:
        return
    whole = st.session_state.get("new_all", False)
    names = new_customer_names(snap, None if whole else selected_date)
    if not names and not whole:
        return
    n_txt = f"{len(names)} customer name(s) in the journal {'(all dates)' if whole else f'for {selected_date}'} are NOT in the Master List"
    if names:
        st.warning(f"🆕 {n_txt}. Sales must add them to the master data as **General customer** or **Dealer** "
                   "(open the box below, choose the type, download the upload file).")
    with st.expander(f"🆕 New customers to add to master data ({len(names)})", expanded=bool(names)):
        st.checkbox("Check the whole journal (all dates), not only the selected day", key="new_all")
        if not names:
            st.success("Every customer in the journal is already in the Master List. ✅")
            return
        master_list = list(snap["customers"])
        rows = []
        for n in names:
            sim = difflib.get_close_matches(n, master_list, n=1, cutoff=0.85)
            rows.append({"Add": not sim, "Customer name": n, "Type": TYPE_GENERAL, "Phone (optional)": "",
                         "⚠️ Looks like (already in master?)": sim[0] if sim else ""})
        with st.form("new_customer_export_form", clear_on_submit=False):
            edited = st.data_editor(
                pd.DataFrame(rows), hide_index=True, height=min(80 + 36 * len(rows), 420), key=f"new_cust_{len(rows)}_{whole}",
                disabled=["Customer name", "⚠️ Looks like (already in master?)"],
                column_config={"Type": st.column_config.SelectboxColumn("Type", options=[TYPE_GENERAL, TYPE_DEALER], required=True),
                               "Add": st.column_config.CheckboxColumn("Add", help="Untick if it is only a spelling mistake")})
            st.caption("⚠️ If a name 'looks like' one already in the master, it is probably a spelling mistake in the journal - "
                       "fix the journal name instead of adding a duplicate (those rows start unticked).")
            start = st.number_input("Next customer number (C-xxxxx) in your accounting system", min_value=1, max_value=999999,
                                    value=1315, step=1, key="new_cust_start")
            build_export = st.form_submit_button("Build customer upload file")
        if not build_export:
            saved_export = st.session_state.get("last_customer_upload_export")
            if saved_export:
                st.caption("Last built upload file: " + saved_export["built"])
                st.download_button("Download last built customer upload file", data=saved_export["data"],
                    file_name=saved_export["name"], mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
            return
        pick = edited[edited["Add"]]
        if pick.empty:
            st.info("Tick at least one customer to make the upload file.")
        else:
            data = build_master_upload([(r["Customer name"], r["Type"], r["Phone (optional)"]) for _, r in pick.iterrows()],
                                       int(start))
            st.session_state["last_customer_upload_export"] = {"data": data, "built": now_str(),
                "name": f"New_Customers_{selected_date}.xlsx"}
            st.download_button(f"📥 Download upload file for master data ({len(pick)} customers)", data=data,
                               file_name=f"New_Customers_{selected_date}.xlsx",
                               mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", key="new_cust_dl")


def _final_panel(selected, p_row):
    """Set the FINAL កេស packed and the FINAL កេស sent for this customer today (fixes a wrong / double / missing entry)."""
    st.markdown("##### 📦 Final packed")
    st.caption("Packed less (or more) than ordered? Set the real number packed. The customer is then judged against what "
               "was packed, so a short order is not shown as 'left to send'.")
    packed_n = int(p_row["Packed Cases"])
    with st.form(f"final_packed_{selected}", clear_on_submit=False):
        pc1, pc2 = st.columns(2)
        fp = pc1.number_input("Final កេស packed", min_value=0, max_value=MAX_CASES, step=1, value=packed_n, key=f"finp_n_{selected}_{packed_n}")
        pwhy = pc2.selectbox("Reason", ["Not enough stock", "Packed less than the order", "Customer asked for less",
                                        "Packing log was wrong", "Packed more", "Other"], key=f"finp_r_{selected}")
        pnote = st.text_input("Extra note (optional)", max_chars=80, key=f"finp_t_{selected}")
        pwho = st.selectbox("Who is editing?", ["-- Select Staff --"] + OPS_STAFF, key=f"finp_w_{selected}")
        q1, q2 = st.columns(2)
        if q1.form_submit_button("💾 Save final packed", type="primary"):
            if pwho.startswith("--"):
                st.error("Choose your name first.")
            else:
                try:
                    append_row(HOLD_FILE, {"Date": now_str(), "Customer": selected, "Action": "FinalPacked", "Cases": int(fp),
                                           "Reason": pwhy + (f" - {pnote.strip()}" if pnote.strip() else ""), "By": pwho})
                    audit("final_packed", f"{pwho}: {selected} -> {int(fp)} (was {packed_n})")
                    flash_and_refresh(f"{selected}: final packed = {int(fp)} កេស")
                except (RuntimeError, ConflictError) as e:
                    st.error(f"❌ {e}")
        if p_row["Packed Note"] and q2.form_submit_button("↩ Back to the packing logs"):
            if pwho.startswith("--"):
                st.error("Choose your name first.")
            else:
                try:
                    append_row(HOLD_FILE, {"Date": now_str(), "Customer": selected, "Action": "FinalPackedReset", "Cases": 0,
                                           "Reason": "-", "By": pwho})
                    audit("final_packed_reset", f"{pwho}: {selected}")
                    flash_and_refresh(f"{selected}: back to the packing logs")
                except (RuntimeError, ConflictError) as e:
                    st.error(f"❌ {e}")
    st.markdown("---")
    st.markdown("##### 🚚 Final sent")
    sent_n = int(p_row["Sent Cases"])
    st.caption("Use this when the total sent is wrong (a slip was entered twice, forgotten, or the customer got more / less). "
               "The number you save here becomes the final កេស sent for this customer today. The delivery slips stay as they are.")
    with st.form(f"final_sent_{selected}", clear_on_submit=False):
        c1, c2 = st.columns(2)
        final = c1.number_input("Final កេស sent", min_value=0, max_value=MAX_CASES, step=1, value=sent_n, key=f"fin_n_{selected}_{sent_n}")
        why = c2.selectbox("Reason", ["Counted again at the truck", "Slip entered twice", "A slip was missing",
                                      "Customer returned some", "Extra items added", "Other"], key=f"fin_r_{selected}")
        note = st.text_input("Extra note (optional)", max_chars=80, key=f"fin_t_{selected}")
        who = st.selectbox("Who is editing?", ["-- Select Staff --"] + OPS_STAFF, key=f"fin_w_{selected}")
        b1, b2 = st.columns(2)
        if b1.form_submit_button("💾 Save final sent", type="primary"):
            if who.startswith("--"):
                st.error("Choose your name first.")
            else:
                try:
                    append_row(HOLD_FILE, {"Date": now_str(), "Customer": selected, "Action": "FinalSent", "Cases": int(final),
                                           "Reason": why + (f" - {note.strip()}" if note.strip() else ""), "By": who})
                    audit("final_sent", f"{who}: {selected} -> {int(final)} (was {sent_n})")
                    flash_and_refresh(f"{selected}: final sent = {int(final)} កេស")
                except (RuntimeError, ConflictError) as e:
                    st.error(f"❌ {e}")
        if p_row["Sent Note"] and b2.form_submit_button("↩ Back to the total of the slips"):
            if who.startswith("--"):
                st.error("Choose your name first.")
            else:
                try:
                    append_row(HOLD_FILE, {"Date": now_str(), "Customer": selected, "Action": "FinalReset", "Cases": 0,
                                           "Reason": "-", "By": who})
                    audit("final_reset", f"{who}: {selected}")
                    flash_and_refresh(f"{selected}: back to the slips total")
                except (RuntimeError, ConflictError) as e:
                    st.error(f"❌ {e}")


def _hold_panel(selected, p_row, left):
    """Move a customer to tomorrow, cancel the order, or bring it back."""
    status = p_row["Status"]
    if status in (ST_MOVED, ST_CANCEL):
        st.warning(f"This customer is now **{status}** - {p_row['Moved/Cancel Reason'] or 'no reason written'}")
        with st.form(f"restore_customer_{selected}", clear_on_submit=False):
            c1, c2 = st.columns(2)
            who = c1.selectbox("Who is doing this?", ["-- Select Staff --"] + OPS_STAFF, key=f"hold_who_{selected}")
            if c2.form_submit_button("↩ Put back as normal (today)"):
                if who.startswith("--"):
                    st.error("Choose your name first.")
                else:
                    try:
                        append_row(HOLD_FILE, {"Date": now_str(), "Customer": selected, "Action": "Restore", "Cases": 0,
                                               "Reason": "-", "By": who})
                        audit("hold_restore", f"{who}: {selected}")
                        flash_and_refresh(f"{selected} is back on today's list")
                    except (RuntimeError, ConflictError) as e:
                        st.error(f"❌ {e}")
        return
    if status == "✅ Sent":
        st.success("This customer is already fully sent - nothing to move or cancel.")
        return
    st.caption("📅 **Tomorrow**: the customer leaves today's to-send lists and appears automatically on tomorrow's board "
               "with the remaining កេស.  ❌ **Cancel**: the order is closed and not counted as waiting.  "
               "Everything stays in the report with your reason, so you can see it later.")
    with st.form(f"hold_customer_{selected}", clear_on_submit=False):
        action = st.radio("What do you want to do?", ["📅 Move to tomorrow", "❌ Cancel the order"], horizontal=True,
                          key=f"hold_act_{selected}")
        c1, c2 = st.columns(2)
        reason = c1.selectbox("Reason", ["Customer asked to wait", "Not enough stock", "Cannot reach customer",
                                         "Transport problem", "Customer cancelled", "Other"], key=f"hold_reason_{selected}")
        extra = c2.text_input("Extra note (optional)", max_chars=80, key=f"hold_note_{selected}")
        cases = st.number_input("កេស to carry to tomorrow (ignored when cancelling)", min_value=0, max_value=MAX_CASES, step=1,
                                value=max(int(left), 0), key=f"hold_cases_{selected}")
        who = st.selectbox("Who is doing this?", ["-- Select Staff --"] + OPS_STAFF, key=f"hold_who2_{selected}")
        if st.form_submit_button("💾 Save move / cancellation", type="primary"):
            if who.startswith("--"):
                st.error("Choose your name first.")
                return
            act = "Tomorrow" if action.startswith("📅") else "Cancel"
            why = reason + (f" - {extra.strip()}" if extra.strip() else "")
            try:
                append_row(HOLD_FILE, {"Date": now_str(), "Customer": selected, "Action": act, "Cases": int(cases) if act == "Tomorrow" else 0,
                                       "Reason": why, "By": who})
                audit("hold_" + act.lower(), f"{who}: {selected} ({why})")
                st.session_state.pop("sel_cust", None)
                st.session_state["clear_sel"] = True
                flash_and_refresh(f"{selected}: {'moved to tomorrow' if act == 'Tomorrow' else 'cancelled'}")
            except (RuntimeError, ConflictError) as e:
                st.error(f"❌ {e}")


def build_report_excel(df, day):
    """Nicely formatted multi-sheet Excel: Summary, All customers, one sheet per status, Province taxi, Deliveries & expenses."""
    from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
    from openpyxl.utils import get_column_letter
    disp = rows_for_day(read_raw(DATA_FILE, DISPATCH_COLS), day)
    disp = disp[DISPATCH_COLS + ["Time"]] if not disp.empty else pd.DataFrame(columns=DISPATCH_COLS + ["Time"])
    clean = df.drop(columns=[c for c in ("🔥",) if c in df.columns]).copy()
    clean.insert(0, "🔥", df["🔥"])
    total = len(df)
    n = lambda stt: int((df["Status"] == stt).sum())
    summary = [["Report date", str(day)], ["Customers", total]]
    summary += [[k, n(k)] for k in STATUS_RANK]
    summary += [["Cases ordered (កេស)", int(df["កេស"].fillna(0).sum())], ["Cases packed", int(df["Packed Cases"].sum())],
                ["Cases sent", int(df["Sent Cases"].sum())],
                ["Phnom Penh expense (៛)", int(disp["Phnom_Penh_Expense"].sum()) if not disp.empty else 0],
                ["Taxi expense (៛)", int(disp["Taxi_Expense"].sum()) if not disp.empty else 0],
                ["Expenses still to fill", int((disp["Expense_Status"] == "Pending").sum()) if not disp.empty else 0]]
    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine="openpyxl") as w:
        pd.DataFrame(summary, columns=["Item", "Value"]).to_excel(w, index=False, sheet_name="Summary", startrow=0)
        r0 = len(summary) + 3
        for title, by in (("By area", "Area"), ("By region", "Region"), ("By province", "Province")):
            t = summarize(df, by)
            t.to_excel(w, index=False, sheet_name="Summary", startrow=r0)
            w.sheets["Summary"].cell(row=r0, column=1).value = by
            r0 += len(t) + 3
        clean.to_excel(w, index=False, sheet_name="All customers")
        for stt, short in ((ST_MOVED, "Moved tomorrow"), (ST_CANCEL, "Cancelled"), ("⏳ Pending", "Pending"),
                           ("🟡 Ready for Delivery", "Ready"), ("🔵 Part sent", "Part sent"), ("✅ Sent", "Sent")):
            part = clean[clean["Status"] == stt]
            if not part.empty:
                part.to_excel(w, index=False, sheet_name=short)
        prov = clean[clean["Area"] == AREA_LABEL["Province"]][["Customer", "Province", "Region", "Status", "កេស", "Sent Cases",
                                                              "Taxi Station", "Taxi No.", "Driver/Station", "Invoice"]]
        if not prov.empty:
            prov.to_excel(w, index=False, sheet_name="Province taxi")
        if not disp.empty:
            disp.to_excel(w, index=False, sheet_name="Deliveries & expenses")
        colors = {k: v[0].lstrip("#") for k, v in STATUS_STYLE.items()}
        thin = Side(style="thin", color="DDDDDD")
        for ws in w.book.worksheets:
            hdr_fill = PatternFill("solid", fgColor="1F3864")
            for c in ws[1]:
                c.font, c.fill = Font(bold=True, color="FFFFFF"), hdr_fill
                c.alignment = Alignment(wrap_text=True, vertical="center")
            ws.freeze_panes = "A2"
            if ws.title != "Summary":
                ws.auto_filter.ref = ws.dimensions
            for i, col in enumerate(ws.columns, 1):
                width = max((len(str(c.value)) for c in list(col)[:200] if c.value is not None), default=8)
                ws.column_dimensions[get_column_letter(i)].width = min(max(width + 2, 8), 45)
            heads = [c.value for c in ws[1]]
            if "Status" in heads:
                si = heads.index("Status") + 1
                for row in ws.iter_rows(min_row=2):
                    cell = row[si - 1]
                    if cell.value in colors:
                        cell.fill = PatternFill("solid", fgColor=colors[cell.value])
                        cell.font = Font(bold=True, color="222222" if cell.value == "🟡 Ready for Delivery" else "FFFFFF")
                    for c in row:
                        c.border = Border(bottom=thin)
            for h_name in ("Phnom_Penh_Expense", "Taxi_Expense"):
                if h_name in heads:
                    for row in ws.iter_rows(min_row=2, min_col=heads.index(h_name) + 1, max_col=heads.index(h_name) + 1):
                        row[0].number_format = "#,##0"
        ws = w.book["Summary"]
        ws.column_dimensions["A"].width = 30
    return buf.getvalue()


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
    with st.form("province_filters"):
        mode = st.radio("Show", ["Only unknown", "Guessed from a town name (please check)", "Set by admin", "All"],
                        horizontal=True, key="loc_show")
        q = st.text_input("🔎 Search customer", key="loc_q", max_chars=60)
        if st.form_submit_button("Apply location filter"):
            _reset_draft("admin_locations")
    if mode == "Only unknown":
        sub = df[unknown]
    elif mode.startswith("Guessed"):
        sub = df[df["How we know"].str.startswith("town name")]
    elif mode == "Set by admin":
        sub = df[df["How we know"] == "set by admin"]
    else:
        sub = df
    if q.strip():
        sub = sub[sub["Customer"].str.contains(q.strip(), case=False, regex=False, na=False)]
    sub = sub.head(300).copy()
    sub["Set province"] = ""
    choices = [""] + sorted(PROVINCES) + ["↩ remove my setting"]
    _reload_draft_button("admin_locations")
    sub, editor_key = _task_editor_frame("admin_locations", sub)
    with st.form("batch_" + editor_key, clear_on_submit=False):
        edited = st.data_editor(
            sub, hide_index=True, height=360, key=editor_key,
            disabled=["Customer", "Area", "Province", "Region", "How we know"],
            column_config={"Set province": st.column_config.SelectboxColumn(
                "Set province", options=choices, help="Choose the province of this customer, then press Save.")})
        submitted = st.form_submit_button("💾 Save locations", type="primary")
    if submitted:
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
                _reset_draft("admin_locations")
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

    st.markdown("#### 👥 Quick setup for all staff")
    st.caption("Creates or updates all 14 staff accounts with your chosen English usernames. "
               "Temporary password for every staff member: 12345. Everyone must choose a stronger personal password on first login. "
               "Clicking the setup button again resets these 14 matching staff accounts back to the temporary password.")
    if st.button("✅ Create / reset all 14 staff logins (temporary password: 12345)",
                 key="create_all_staff_accounts", type="primary"):
        outcome = {"created": [], "updated": [], "renamed": [], "skipped": [], "credentials": []}
        st.session_state.pop("staff_account_setup_credentials", None)

        def _create_team_accounts(u):
            created, updated, renamed, skipped, credentials = [], [], [], [], []
            temp_pw = "12345"
            for spec in STAFF_ACCOUNT_SPECS:
                uname = spec["username"]
                if uname in u:
                    rec = u.get(uname, {})
                    stored_staff_name = str(rec.get("staff_name") or "").strip()
                    # These 14 usernames were explicitly chosen by the owner for these staff.
                    # If an account was manually created earlier and has no staff_name metadata,
                    # attach it to the requested staff entry rather than leaving a duplicate/conflict.
                    same_person = (stored_staff_name == spec["name"] or not stored_staff_name)
                    if same_person:
                        # Known staff account: reset its temporary password and enforce a change at login.
                        rec.update(_hash_pw(temp_pw))
                        rec.update({"role": spec["role"], "active": rec.get("active", True),
                                    "must_change": True, "staff_name": spec["name"]})
                        u[uname] = rec
                        updated.append({"Staff name": spec["name"], "Username": uname})
                        credentials.append({"Staff name": spec["name"], "Username": uname,
                                            "Role": ROLE_LABEL.get(spec["role"], spec["role"]),
                                            "Temporary password": temp_pw})
                    else:
                        skipped.append({"Staff name": spec["name"], "Username": uname,
                                        "Reason": "Username is already used by another account; left unchanged"})
                    continue

                # Only migrate an older account when its saved staff name and role match this person.
                aliases = spec.get("legacy_usernames") or ([spec["legacy_username"]] if spec.get("legacy_username") else [])
                legacy = None
                for alias in aliases:
                    if alias == uname or alias not in u:
                        continue
                    legacy_rec = u.get(alias, {})
                    if (str(legacy_rec.get("staff_name") or "").strip() == spec["name"] and
                            legacy_rec.get("role") == spec["role"]):
                        legacy = alias
                        break
                if legacy:
                    rec = u.pop(legacy)
                    rec.update(_hash_pw(temp_pw))
                    rec.update({"role": spec["role"], "active": rec.get("active", True),
                                "must_change": True, "staff_name": spec["name"]})
                    u[uname] = rec
                    renamed.append({"Staff name": spec["name"], "Old username": legacy, "New username": uname})
                else:
                    rec = _new_user(spec["role"], temp_pw, must_change=True)
                    rec["staff_name"] = spec["name"]
                    u[uname] = rec
                    created.append({"Staff name": spec["name"], "Username": uname})
                credentials.append({"Staff name": spec["name"], "Username": uname,
                                    "Role": ROLE_LABEL.get(spec["role"], spec["role"]),
                                    "Temporary password": temp_pw})

            outcome["created"] = created
            outcome["updated"] = updated
            outcome["renamed"] = renamed
            outcome["skipped"] = skipped
            outcome["credentials"] = credentials
            return u

        try:
            modify_users(_create_team_accounts)
            st.session_state["staff_account_setup_result"] = {
                "created_count": len(outcome["created"]),
                "updated_count": len(outcome["updated"]) + len(outcome["renamed"]),
                "renamed": outcome["renamed"],
                "skipped": outcome["skipped"],
            }
            if outcome["credentials"]:
                st.session_state["staff_account_setup_credentials"] = outcome["credentials"]
            audit("staff_accounts_bulk_created_or_reset",
                  f"created={len(outcome['created'])}, updated={len(outcome['updated'])}, "
                  f"renamed={len(outcome['renamed'])}, skipped={len(outcome['skipped'])}")
            st.rerun()
        except (ValueError, RuntimeError, ConflictError, PermissionError) as err:
            st.error(f"❌ Could not create/reset staff accounts: {err}")

    setup_result = st.session_state.get("staff_account_setup_result")
    if setup_result:
        st.info(f"Created {setup_result['created_count']} new account(s), reset {setup_result.get('updated_count', 0)} existing staff account(s), "
                f"renamed {len(setup_result.get('renamed', []))} old username(s), and skipped {len(setup_result['skipped'])} username conflict(s). "
                "Every account changed by this setup must change its password at first login.")
        if setup_result.get("renamed"):
            with st.expander("View renamed staff usernames"):
                show_df(pd.DataFrame(setup_result["renamed"]))
        if setup_result["skipped"]:
            with st.expander("View skipped accounts"):
                show_df(pd.DataFrame(setup_result["skipped"]))
    credentials = st.session_state.get("staff_account_setup_credentials")
    if credentials:
        st.warning("Temporary password for the listed staff accounts is 12345. Give each username only to its owner. "
                   "This password is intentionally temporary and each person is forced to set a stronger personal password before using the app. "
                   "Clicking the setup button again will reset the listed matching accounts to 12345.")
        cred_df = pd.DataFrame(credentials)
        st.dataframe(cred_df, hide_index=True, use_container_width=True)
        st.download_button("⬇️ Download staff login list (CSV)", data=cred_df.to_csv(index=False).encode("utf-8-sig"),
                           file_name="staff_initial_logins.csv", mime="text/csv", key="download_staff_initial_logins")
        if st.button("🙈 Hide temporary passwords", key="hide_staff_initial_logins"):
            st.session_state.pop("staff_account_setup_credentials", None)
            st.rerun()

    show_df(pd.DataFrame([{
        "Staff name": r.get("staff_name", ""), "Username": u, "Role": r.get("role"),
        "Active": "yes" if r.get("active", True) else "NO",
        "Tasks": "ON" if effective_permissions(u, r).get("tasks") else "OFF",
        "View": "ON" if effective_permissions(u, r).get("view") else "OFF",
        "Edit": "ON" if effective_permissions(u, r).get("edit") else "OFF",
        "Reports": "ON" if effective_permissions(u, r).get("reports") else "OFF",
        "Starter password": "yes" if r.get("must_change") else "",
        "Last login": r.get("last_login", ""), "Password changed": r.get("pw_changed", "")}
        for u, r in sorted(users.items())]))

    with st.expander("🔐 Turn each user's permissions ON / OFF", expanded=True):
        st.caption("Choose a username, tick only the abilities they need, then save. Changes take effect when their app refreshes. Admin accounts always keep all permissions to prevent locking out the business owner.")
        perm_user = st.selectbox("Select user to customize", sorted(users), key="perm_user_select")
        perm_rec = users.get(perm_user, {})
        perm_values = effective_permissions(perm_user, perm_rec)
        is_admin_target = perm_rec.get("role") == "admin"
        if is_admin_target:
            st.info("Admin permissions are always ON for security and account recovery.")
        with st.form(f"permissions_form_{perm_user}"):
            p_tasks = st.checkbox(PERMISSION_LABELS["tasks"], value=perm_values["tasks"], key=f"perm_tasks_{perm_user}", disabled=is_admin_target)
            p_view = st.checkbox(PERMISSION_LABELS["view"], value=perm_values["view"], key=f"perm_view_{perm_user}", disabled=is_admin_target)
            p_edit = st.checkbox(PERMISSION_LABELS["edit"], value=perm_values["edit"], key=f"perm_edit_{perm_user}", disabled=is_admin_target)
            p_reports = st.checkbox(PERMISSION_LABELS["reports"], value=perm_values["reports"], key=f"perm_reports_{perm_user}", disabled=is_admin_target)
            save_perms = st.form_submit_button("💾 Save permissions", type="primary")
        if save_perms:
            if is_admin_target:
                st.info("Admin access remains fully enabled.")
            else:
                new_perms = {"tasks": p_tasks, "view": p_view, "edit": p_edit, "reports": p_reports}
                def _save_perms(u):
                    if perm_user not in u:
                        raise ValueError("That user no longer exists. Refresh and try again.")
                    if u[perm_user].get("role") == "admin":
                        u[perm_user]["permissions"] = {k: True for k in PERMISSION_KEYS}
                    else:
                        u[perm_user]["permissions"] = dict(new_perms)
                    return u
                try:
                    modify_users(_save_perms)
                    audit("user_permissions_changed", f"{perm_user}: " + ", ".join(f"{k}={'ON' if v else 'OFF'}" for k, v in new_perms.items()))
                    flash_and_refresh(f"Permissions saved for {perm_user}")
                except (ValueError, RuntimeError, ConflictError) as err:
                    st.error(f"❌ Could not save permissions: {err}")

    with st.expander("➕ Add a user"):
        with st.form("add_user_form", clear_on_submit=True):
            nu = st.text_input("Username (3-30 letters/numbers, for example: sokha)", max_chars=30)
            nr = st.selectbox("Role", ROLES, help="staff = packing + delivery + dashboard | sales = dashboard/reports only; delivery staff record the chosen verifier | viewer = dashboard only | admin = everything")
            npw = st.text_input("Temporary password (default: 12345; user must change it at first login)",
                                value="12345", max_chars=100)
            if st.form_submit_button("Create user", type="primary"):
                uname = nu.strip().lower()
                pw = npw.strip() or "12345"
                if not USERNAME_RE.match(uname):
                    st.error("❌ Username: 3-30 characters, only a-z, 0-9, dot, dash, underscore.")
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
        tpw = st.text_input("New temporary password (default: 12345; user must change it at first login)",
                            value="12345", max_chars=100, key="mng_pw")
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
                    # Temporary password may be simple because login is blocked until the user replaces it.
                    pw = tpw.strip() or "12345"
                    u[who].update(_hash_pw(pw))
                    u[who]["must_change"] = True
                    u[who]["pw_changed"] = now_str()          # signs this person out of every saved phone
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
        ("Temporary staff password", "12345; each staff account must change it at first login"),
        ("Personal password rule", "at least 8 characters with letters and numbers"),
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
    st.caption(f"Checks files, numeric values, dates, accounts and order totals every {BOT_INTERVAL_MIN} minutes "
               "while this app is open. Safe repairs keep backups. Damaged rows, uncertain duplicates and quantities require review.")

    st.info(("☁️ Online mode: data is stored in Dropbox folder " + DROPBOX_FOLDER) if USE_DROPBOX
            else "💻 Local mode: data is stored in the app folder on this computer")
    c1, c2, c3 = st.columns(3)
    if c1.button("🔧 Check & fix now", key="bot_fix"):
        auto_bot.clear()
    only_check = c2.button("👀 Diagnose records only", key="bot_check")
    if c3.button("🧹 Clear cache & re-sync Dropbox", key="bot_cache"):
        resync_now()
        try:
            os.remove(os.path.join(CACHE_DIR, "excel_snapshot.pkl"))
        except OSError:
            pass
        st.toast("Cache cleared - everything will be re-read", icon="🧹")

    if only_check:
        findings, suggestions = run_health_check(auto_fix=False)
        st.markdown("**Diagnostic result (business records preserved):**")
    else:
        findings, suggestions = auto_bot()
        st.markdown("**Health check result:**")
    if only_check:
        st.session_state["health_diagnostic_result"] = (findings, suggestions, now_str())
    elif "health_diagnostic_result" in st.session_state and not st.session_state.get("bot_fix"):
        findings, suggestions, checked = st.session_state["health_diagnostic_result"]
        st.caption(f"Showing diagnostic result from {checked}. Use Check & fix now for a fresh repair check.")
    else:
        st.session_state.pop("health_diagnostic_result", None)
    counts = [sum(f["Level"] == LEVEL_ICON[level] for f in findings) for level in ("error", "warn", "fixed")]
    for column, title, value in zip(st.columns(3), ("Errors", "Warnings", "Safely fixed"), counts):
        column.metric(title, value)
    st.caption("Last automatic check: " + _sync_state().get("last_health_check", "not completed"))
    attention_only = st.checkbox("Show errors and warnings only", value=True, key="health_attention")
    visible = [f for f in findings if f["Level"] in (LEVEL_ICON["error"], LEVEL_ICON["warn"])] if attention_only else findings
    if visible:
        show_df(pd.DataFrame(visible))
    else:
        st.success("No unresolved warnings or errors in this result.")
    st.download_button("Download health report", data=json.dumps({"exported_at": now_str(), "findings": findings},
                       ensure_ascii=False, indent=2), file_name="health_report.json", mime="application/json")

    if suggestions:
        st.markdown("**Names that look like typos (the bot suggests the Master List name):**")
        show_df(pd.DataFrame(suggestions, columns=["File", "Name in file", "Suggested name"]))
        with st.form("review_name_corrections", clear_on_submit=False):
            selected_fixes = st.data_editor(
                pd.DataFrame([{"Apply?": False, "File": key, "Name in file": bad, "Suggested name": good}
                              for key, bad, good in suggestions]), hide_index=True,
                disabled=["File", "Name in file", "Suggested name"], key="name_fix_review")
            apply_names = st.form_submit_button("Apply selected name corrections")
        if apply_names:
            chosen = [(r["File"], r["Name in file"], r["Suggested name"])
                      for r in selected_fixes.to_dict("records") if r["Apply?"]]
            if not chosen:
                st.warning("Select the corrections you have reviewed first.")
                return
            apply_name_fixes(chosen)
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



_MAP_SEED_JSON = r"""[
{"id": "nphk-20261015-0001", "customer": "CHHIM SAYORN ទួលគោក", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 3, "lead_no": 1},
{"id": "nphk-20261015-0002", "customer": "MO", "province": "", "url": "https://maps.google.com/maps?q=11.518901,104.876871&ll=11.518901,104.876871&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 4, "lead_no": 2},
{"id": "nphk-20261015-0003", "customer": "ស្រីលីន ក្រចេះ", "province": "ក្រចេះ", "url": "https://maps.app.goo.gl/fmUAVum6c6joAkR36", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 5, "lead_no": 3, "resolved_url": "https://www.google.com/maps/place/12%C2%B029'29.9%22N+106%C2%B003'55.5%22E/@12.491629,106.065429,1302m/data=!3m1!1e3!4m4!3m3!8m2!3d12.491629!4d106.065429?entry=tts&g_ep=EgoyMDI2MTAxMS4wIPu8ASoASAFQAw%3D%3D&skid=1e0918d0-4a09-4bb6-8f0f-94836d11cbc9", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0004", "customer": "LY MEY", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.528484,104.957959&ll=11.528484,104.957959&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 6, "lead_no": 4},
{"id": "nphk-20261015-0005", "customer": "SEANG HAI ផ្សារព្រែកថ្មី កៀនស្វាយ", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/PDtGo2oRZGsm7acz7", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 7, "lead_no": 5, "resolved_url": "https://www.google.com/maps/place/11%C2%B017'10.1%22N+105%C2%B008'22.8%22E/@11.286135,105.139678,1336m/data=!3m1!1e3!4m4!3m3!8m2!3d11.286135!4d105.139678?entry=tts&g_ep=EgoyMDI2MTAwNS4wIPu8ASoASAFQAw%3D%3D&skid=471f9c7b-a880-4720-86ad-18b986c57d7e", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0006", "customer": "ម៉ៅ ចន្ធី ក្រុងស្វាយរៀង", "province": "ស្វាយរៀង", "url": "https://goo.gl/maps/qDgJr3DkWZx5Adxk8?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 8, "lead_no": 6, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.045241,105.817289&entry=gps&g_ep=CAESBzI2LjM4LjEYACDXggMqvQEsOTQyNjc3MjcsOTQyOTIxOTUsOTQyOTk1MzIsMTAwNzk2NDk4LDEwMDc5Nzc2MSwxMDA3OTY1MzUsOTQyODA1NzYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksMTAwODA4NjU0LDk0Mjc1MTY4LDk0Mjc5NjE5LDEwMDgzNTcwNCwxMDA4MjUwMjUsMTAwODIwMjM3LDEwMDgyMjQ5NCwxMDA4Mjc5NzVCAktI&skid=f4dac2ed-dd5f-44b5-a5f6-2eed44ffbb83&shorturl=1"},
{"id": "nphk-20261015-0007", "customer": "SREY TUCH", "province": "កំពង់ធំ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 9, "lead_no": 7},
{"id": "nphk-20261015-0008", "customer": "MAO SREYNICH វិទ្យាល័យជាតិ បាត់ដំបង", "province": "បាត់ដំបង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 10, "lead_no": 8},
{"id": "nphk-20261015-0009", "customer": "SAIFONG កប់ស្រូវ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 11, "lead_no": 9},
{"id": "nphk-20261015-0010", "customer": "UNG RAKSMEY ជិតព្តលានថ្មី", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/GmRUA4t1Ur12HmBL8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 12, "lead_no": 10, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0011", "customer": "SUO SORPHOIN បារាយណ៍ កំពង់ធំ", "province": "កំពង់ធំ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 13, "lead_no": 11},
{"id": "nphk-20261015-0012", "customer": "SREYDIN KEO", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.503340,103.611797&ll=13.503340,103.611797&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 14, "lead_no": 12},
{"id": "nphk-20261015-0013", "customer": "HAPPY DAILY MART គួរស្រូវ2", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 15, "lead_no": 13},
{"id": "nphk-20261015-0014", "customer": "KHEANG SIRONG ឡែម", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.084906,102.458952&ll=13.084906,102.458952&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 16, "lead_no": 14},
{"id": "nphk-20261015-0015", "customer": "KANNITHA កំពង់ធំ", "province": "កំពង់ធំ", "url": "https://maps.google.com/maps?q=12.636423,104.984085&ll=12.636423,104.984085&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 17, "lead_no": 15},
{"id": "nphk-20261015-0016", "customer": "UDOM ចោមចៅ 2", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.512740,104.832276&ll=11.512740,104.832276&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 18, "lead_no": 16},
{"id": "nphk-20261015-0017", "customer": "KA A HAA  ប៉ោយប៉ែត", "province": "ប៉ោយប៉ែត", "url": "https://maps.app.goo.gl/Uxi5KWEpv66pXFA88?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 19, "lead_no": 17, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=13.6678058,102.5769887&entry=gps&shh=CAE&lucs=,94297699,100795621,94231188,94280568,47071704,94218641,100808654,94282134,94286869,100820247,100822504&g_ep=CAISEjI2LjM2LjMuOTczNTQ4ODUxMBgAIIgnKmcsOTQyOTc2OTksMTAwNzk1NjIxLDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDEwMDgwODY1NCw5NDI4MjEzNCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=a31a787a-77bd-449e-be40-54093ba48748&g_st=ic"},
{"id": "nphk-20261015-0018", "customer": "GO MART បឹងត្របែក ផ្លូវ99", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.535772,104.922233&ll=11.535772,104.922233&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 20, "lead_no": 18},
{"id": "nphk-20261015-0019", "customer": "បញ្ញា កេង ភូមិល្ងើន ព្រៃវែង", "province": "ព្រៃវែង", "url": "https://maps.google.com/maps?q=11.690391,105.438458&ll=11.690391,105.438458&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 21, "lead_no": 19},
{"id": "nphk-20261015-0020", "customer": "PHUONG KUNTHEARY ព្រែកព្នៅ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/LJ74DCFMqnvFXP9UA?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 22, "lead_no": 20, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0021", "customer": "NICH NICH តាខ្មៅ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.465950,104.957160&ll=11.465950,104.957160&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 23, "lead_no": 21},
{"id": "nphk-20261015-0022", "customer": "MR ONEDAY បុរៅមហាសែនសុខ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.576133,104.836465&ll=11.576133,104.836465&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 24, "lead_no": 22},
{"id": "nphk-20261015-0023", "customer": "YI MALUX កំពង៉ធំ", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/2nMtvtDqXFVukG4L7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 25, "lead_no": 23, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=12.7915973,104.8399923&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,100821555,47071704,94218641,94282134,100835699,94286869,100820247,100822504&g_ep=CAISEjI2LjM4LjEuOTgwODE1NDQ1MBgAINeCAypnLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDEwMDgyMTU1NSw0NzA3MTcwNCw5NDIxODY0MSw5NDI4MjEzNCwxMDA4MzU2OTksOTQyODY4NjksMTAwODIwMjQ3LDEwMDgyMjUwNEICS0g%3D&skid=8df3a248-85c2-4840-a679-81d16bec1236&g_st=it"},
{"id": "nphk-20261015-0024", "customer": "ROMDOUL SAM ផ្សារឈូក", "province": "", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 26, "lead_no": 24},
{"id": "nphk-20261015-0025", "customer": "JEE LEANG ព្រះវិហារ", "province": "ព្រះវិហារ", "url": "https://maps.google.com/maps?q=14.238279,104.731919&ll=14.238279,104.731919&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 27, "lead_no": 25},
{"id": "nphk-20261015-0026", "customer": "SOK NITA MACH ឈូកវ៉ា2", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 28, "lead_no": 26},
{"id": "nphk-20261015-0027", "customer": "SOKAN THUCH កំរៀង បាត់ដំបង", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.085018,102.484079&ll=13.085018,102.484079&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 29, "lead_no": 27},
{"id": "nphk-20261015-0028", "customer": "Mey ព្រែកព្នៅ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 30, "lead_no": 28},
{"id": "nphk-20261015-0029", "customer": "DALIN KE តាំងគោក កំពង់ធំ", "province": "", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 31, "lead_no": 29},
{"id": "nphk-20261015-0030", "customer": "ទ្រី ផារី កំបូល3", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.476493,104.787410&ll=11.476493,104.787410&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 32, "lead_no": 30},
{"id": "nphk-20261015-0031", "customer": "JEE LANG", "province": "ព្រះវិហារ", "url": "https://maps.google.com/maps?q=14.238279,104.731919&ll=14.238279,104.731919&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 33, "lead_no": 31},
{"id": "nphk-20261015-0032", "customer": "KIT KHUNNY ផ្សារសៃវ៉ា តាកែវ", "province": "តាកែវ", "url": "https://goo.gl/maps/gbvYaR8rvmEdhRfZ7?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 34, "lead_no": 32, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.162750,104.875431&entry=gps&g_ep=CAESBzI2LjMxLjIYACCdtwgqlQEsOTQyNjc3MjcsOTQyOTIxOTUsOTQyOTk1MzIsMTAwNzk2NDk4LDEwMDc5Nzc2MSwxMDA3OTY1MzUsOTQyODA1NzYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksMTAwODE1NjQwLDEwMDgyMDIzN0ICS0g%3D&skid=d96271f7-d43f-4f33-9d71-07cf20c3a6db&shorturl=1"},
{"id": "nphk-20261015-0033", "customer": "CHHIM SAYORN ឈូកមាស", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/WQ64GazKVkia1Exp7?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 35, "lead_no": 33, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0034", "customer": "THING បុរីសុខសាន្ដ ព្រែកឯក", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.502566,105.007372&ll=11.502566,105.007372&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 36, "lead_no": 34},
{"id": "nphk-20261015-0035", "customer": "SOTHEANY", "province": "ភ្នំពេញ", "url": "https://mapshttps://maps.google.com/maps?q=11.575709,104.878839&ll=11.575709,104.878839&z=16.google.com/maps?q=11.575709,104.878839&ll=11.575709,104.878839&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 37, "lead_no": 35},
{"id": "nphk-20261015-0036", "customer": "SOTHEANY", "province": "", "url": "https://maps.google.com/maps?q=11.575709,104.878839&ll=11.575709,104.878839&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 38, "lead_no": 36},
{"id": "nphk-20261015-0037", "customer": "Neang leasmy ផ្សារកាបី ក្រចេះ", "province": "ក្រចេះ", "url": "https://maps.google.com/maps?q=12.136423,106.724029&ll=12.136423,106.724029&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 39, "lead_no": 37},
{"id": "nphk-20261015-0038", "customer": "VIN CHHAY", "province": "កំពង់ចាម", "url": "https://maps.app.goo.gl/TXhEBGjgrrLcCqBw9?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 40, "lead_no": 38, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0039", "customer": "OAM RATHANA ពោធិចិនតុង", "province": "បន្ទាយមានជ័យ", "url": "https://maps.app.goo.gl/gzZoTR5wCD66J1dN7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 41, "lead_no": 39, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0040", "customer": "LY KA ព្រែកលាប", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.639355,104.913023&ll=11.639355,104.913023&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 42, "lead_no": 40},
{"id": "nphk-20261015-0041", "customer": "SOVANN ផ្សារឈូកមាស", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/jhGjeq9rWcimk3oLA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 43, "lead_no": 41, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0042", "customer": "សៀន ម៉ាណារី ស្រុកគិរីសាគ", "province": "កោះកុង", "url": "https://maps.google.com/maps?q=10.992248,103.209119&ll=10.992248,103.209119&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 44, "lead_no": 42},
{"id": "nphk-20261015-0043", "customer": "MAO SREYNICH សកលវិទ្យាល័យបាត់ដំបង", "province": "បាត់ដំបង", "url": "https://maps.app.goo.gl/4HG2iRYneSnRYfXj7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 45, "lead_no": 43, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0044", "customer": "VIN CHHAY កំពង់ចាម", "province": "កំពង់ចាម", "url": "https://maps.app.goo.gl/TXhEBGjgrrLcCqBw9?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 46, "lead_no": 44, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0045", "customer": "MENG ពោធិចិនតុង", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/gzwEf5gT6t4KKCk8A", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 47, "lead_no": 45, "resolved_url": "https://www.google.com/maps/place/Baksey+Sur+Coffee,+Street+105K,+Phnom+Penh+12411/data=!4m6!3m5!1s0x31094f15d4c93275:0x23695e4d2b611f3d!7e2!8m2!3d11.5805894!4d104.8413159!18m1!1e1?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI2LjM0LjQYACCenQoqqQEsOTQyNjc3MjcsOTQyOTIxOTUsOTQyOTk1MzIsMTAwNzk2NDk4LDEwMDc5Nzc2MSwxMDA3OTY1MzUsOTQyODA1NzYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksMTAwODE1NjQwLDEwMDgyMDIzNywxMDA4MjI0OTQsMTAwODI3OTcxQgJLSA%3D%3D&skid=2ac11cf9-1253-4a1c-8785-3fcc1d430f34", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0046", "customer": "OURN SAMBARTH  ពោធិចិនតុង", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.540697,104.828358&ll=11.540697,104.828358&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 48, "lead_no": 46},
{"id": "nphk-20261015-0047", "customer": "CHENDA ល្វាឯម", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/x6iKxNbJZAqTX7kt8?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 49, "lead_no": 47, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0048", "customer": "THOURNG SREYNIN ព្រែកអញ្ចាញ", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/dBDZdmKtCWgfKu646?g_st=ac", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 50, "lead_no": 48, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0049", "customer": "HANG KY", "province": "ស្វាយរៀង", "url": "https://maps.google.com/maps?q=11.037891,106.010845&ll=11.037891,106.010845&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 51, "lead_no": 49},
{"id": "nphk-20261015-0050", "customer": "CHHAY HENG ផ្លូវភ្លោះអូឬស្សី", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.558024,104.917652&ll=11.558024,104.917652&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 52, "lead_no": 50},
{"id": "nphk-20261015-0051", "customer": "AU HANG ក្រាំងធ្នុងសែនសុខ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/mB9KagZxV7fV1R2Q9?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 53, "lead_no": 51, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0052", "customer": "VANNAK", "province": "កែប", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 54, "lead_no": 52},
{"id": "nphk-20261015-0053", "customer": "GRACE SOTHEA ស្រុកស្ទឹងហាវ", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.724686,103.619956&ll=10.724686,103.619956&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 55, "lead_no": 53},
{"id": "nphk-20261015-0054", "customer": "PHIM PHIM ស្រុកអង្គរជ័យ", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.893829,104.557942&ll=10.893829,104.557942&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 56, "lead_no": 54},
{"id": "nphk-20261015-0055", "customer": "RACHANA ROUS ព្រែកព្នៅ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.700776,104.840686&ll=11.700776,104.840686&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 57, "lead_no": 55},
{"id": "nphk-20261015-0056", "customer": "SREY DAV បុរីមរកត", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.506111,104.854668&ll=11.506111,104.854668&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 58, "lead_no": 56},
{"id": "nphk-20261015-0057", "customer": "SOKON KHENG សៀមរាប", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.386937,103.818032&ll=13.386937,103.818032&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 59, "lead_no": 57},
{"id": "nphk-20261015-0058", "customer": "ពន្លក សាលាគ្រួស សៀមរាប", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.373448,103.840442&ll=13.373448,103.840442&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 60, "lead_no": 58},
{"id": "nphk-20261015-0059", "customer": "ដេប៉ូតេលា ស្រុកទ្រាំង តាកែវ", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=10.844594,104.793359&ll=10.844594,104.793359&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 61, "lead_no": 59},
{"id": "nphk-20261015-0060", "customer": "ស្រីកែវ TK STORE ជម្ពូវ័ន", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.533179,104.821585&ll=11.533179,104.821585&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 62, "lead_no": 60},
{"id": "nphk-20261015-0061", "customer": "YU PICH វត្ដពោធិវង្ស បាត់ដំបង", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.117192,103.197449&ll=13.117192,103.197449&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 63, "lead_no": 61},
{"id": "nphk-20261015-0062", "customer": "ដើប៉ូតេលា តំបន់ដូងកឹង ព្រៃវែង", "province": "ព្រៃវែង", "url": "https://maps.google.com/maps?q=11.574062,105.566996&ll=11.574062,105.566996&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 64, "lead_no": 62},
{"id": "nphk-20261015-0063", "customer": "DIVERSE CAFÉ ព្រែកលាប", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.652636,104.915455&ll=11.652636,104.915455&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 65, "lead_no": 63},
{"id": "nphk-20261015-0064", "customer": "MO NYMEAN ព្រះនេត្រព្រះ", "province": "បន្ទាយមានជ័យ", "url": "https://maps.google.com/maps?q=13.627369,103.184197&ll=13.627369,103.184197&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 66, "lead_no": 64},
{"id": "nphk-20261015-0065", "customer": "SAVIMEX អង្គរជ័យ", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.769698,104.637231&ll=10.769698,104.637231&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 67, "lead_no": 65},
{"id": "nphk-20261015-0066", "customer": "EII TY COFFEE កំពងចម្លងកំពង់គរ ឆ្លូង", "province": "ស្ទឹងត្រែង", "url": "https://maps.google.com/maps?q=12.274468,105.963532&ll=12.274468,105.963532&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 68, "lead_no": 66},
{"id": "nphk-20261015-0067", "customer": "SO NITA ផ្សារស្វៃវ៉ា តាកែវ", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 69, "lead_no": 67},
{"id": "nphk-20261015-0068", "customer": "RACHANA ចល័ចរ កាហ្វេ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/sjag1gLzbBWAMx5M9?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 70, "lead_no": 68, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0069", "customer": "THEARA គូស្រូវ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/eEPLivNuFr8u1YJj7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 71, "lead_no": 69, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.4406193,104.8933391&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,100821559,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMzLjEuOTYxODkxNDMyMBgAINeCAypnLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDEwMDgyMTU1OSw0NzA3MTcwNCw5NDIxODY0MSw5NDI4MjEzNCwxMDA4MTM0NjQsOTQyODY4NjksMTAwODIwMjQ3LDEwMDgyMjUwNEICS0g%3D&skid=562076a0-e81b-4b3f-8dc7-4bb785a7780d&g_st=it"},
{"id": "nphk-20261015-0070", "customer": "LONG KR", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 72, "lead_no": 70},
{"id": "nphk-20261015-0071", "customer": "KHANN LINA ព្រែកក្ដាម កោះចិន", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.797184,104.824930&ll=11.797184,104.824930&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 73, "lead_no": 71},
{"id": "nphk-20261015-0072", "customer": "កាហ្វេ ននោង គង់ពិសី កំពង់ស្ពឺ", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/pxFHvDwi9G7Hs91R8?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 74, "lead_no": 72, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0073", "customer": "VA KHIM", "province": "កំពង់ស្ពឺ", "url": "https://maps.apple/p/HMUUc2MNszxsA9", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 75, "lead_no": 73, "resolved_url": "https://maps.apple.com/place?coordinate=11.808148,104.164605&name=My%20Location&map=h", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0074", "customer": "OUN MOEW", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.824266,104.740841&ll=11.824266,104.740841&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 76, "lead_no": 74},
{"id": "nphk-20261015-0075", "customer": "LIM CHANDANIN", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/PmW5CBFBoYRjd3Cf7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 77, "lead_no": 75, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0076", "customer": "ម៉ាក់ ភាលីង ព្រែកខ្វិត", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.637028,104.914454&ll=11.637028,104.914454&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 78, "lead_no": 76},
{"id": "nphk-20261015-0077", "customer": "LIM LONG ចោមចៅ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.501629,104.805441&ll=11.501629,104.805441&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 79, "lead_no": 77},
{"id": "nphk-20261015-0078", "customer": "SENG SOCHEATA", "province": "តាកែវ", "url": "https://maps.app.goo.gl/Lp78ajNn4dBvtVQV9", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 80, "lead_no": 78, "resolved_url": "https://www.google.com/maps/place/%E1%9E%80%E1%9E%B6%E1%9E%A0%E1%9F%92%E1%9E%9C%E1%9F%81%E1%9E%87%E1%9E%BE%E1%9E%84%E1%9E%97%E1%9F%92%E1%9E%93%E1%9F%86+(+Phnom+Chisor),+%E1%9E%97%E1%9E%BC%E1%9E%98%E1%9E%B7%E1%9E%85%E1%9E%93%E1%9F%92%E1%9E%9B%E1%9E%B6%E1%9E%8F%E1%9F%8B%E1%9E%8A%E1%9F%83/data=!4m6!3m5!1s0x31096fa4b8adf96b:0x6892c91ef0646c11!7e2!8m2!3d11.1938885!4d104.8197216!18m1!1e1?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI2LjMyLjYYACDXggMqqQEsOTQyNjc3MjcsOTQyOTIxOTUsOTQyOTk1MzIsMTAwNzk2NDk4LDEwMDc5Nzc2MSwxMDA3OTY1MzUsOTQyODA1NzYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksMTAwODE1NjM1LDEwMDgyMDIzNywxMDA4MjI0OTQsMTAwODI3OTc1QgJLSA%3D%3D&skid=3d0963c4-712f-43c5-8313-44f264849faf", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0079", "customer": "PTT សំរោងយ៉ោង", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 81, "lead_no": 79},
{"id": "nphk-20261015-0080", "customer": "LAPU COFFEE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/UuuFFWmKT4z7rjVF9?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 82, "lead_no": 80, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0081", "customer": "LIYA YAYA", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.609303,103.516902&ll=10.609303,103.516902&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 83, "lead_no": 81},
{"id": "nphk-20261015-0082", "customer": "SREY POV", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/z9WqBm1a11XAh56B7?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 84, "lead_no": 82, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0083", "customer": "J.T WO.S MART ( VISAL CHAN )", "province": "បាក់ទូក", "url": "https://maps.google.com/maps?q=11.566293,104.911586&ll=11.566293,104.911586&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 85, "lead_no": 83},
{"id": "nphk-20261015-0084", "customer": "SUON SODALIN បាត់ដំបង", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.080248,103.204883&ll=13.080248,103.204883&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 86, "lead_no": 84},
{"id": "nphk-20261015-0085", "customer": "SO CHEATA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/ZgGDSsJoBTydd8Xy5?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 87, "lead_no": 85, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0086", "customer": "MEY", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 88, "lead_no": 86},
{"id": "nphk-20261015-0087", "customer": "អាង ឈឹម ត្រែងត្រយឹង កំពង់ស្ពឺ", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.278807,104.206944&ll=11.278807,104.206944&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 89, "lead_no": 87},
{"id": "nphk-20261015-0088", "customer": "ពុំ ស្រីនិត អូរពី កំពង់សោម", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=12.401523,105.435468&ll=12.401523,105.435468&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 90, "lead_no": 88},
{"id": "nphk-20261015-0089", "customer": "SOK KHEA ពន្ធធានាគា សៀមរាប", "province": "សៀមរាប", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 91, "lead_no": 89},
{"id": "nphk-20261015-0090", "customer": "HENG SINHUNSY វត្តភ្នំ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.575317,104.924417&ll=11.575317,104.924417&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 92, "lead_no": 90},
{"id": "nphk-20261015-0091", "customer": "ផារី", "province": "បាត់ដំបង", "url": "https://maps.app.goo.gl/zefjMLN3XkciapeJ8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 93, "lead_no": 91, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=13.0959807,103.1974225&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822499&g_ep=CAISEjI2LjMyLjUuOTU4MDQ3MzAzMBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNDk5QgJLSA%3D%3D&skid=84634bb2-1ebd-49be-8866-2e37e993cb01&g_st=ic"},
{"id": "nphk-20261015-0092", "customer": "HAK KANHA តាកែវ", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.162067,104.952845&ll=11.162067,104.952845&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 94, "lead_no": 92},
{"id": "nphk-20261015-0093", "customer": "SREY KHUOCH TEP ប៉ោយប៉ែត", "province": "ប៉ោយប៉ែត", "url": "https://maps.google.com/maps?q=13.668493,102.586271&ll=13.668493,102.586271&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 95, "lead_no": 93},
{"id": "nphk-20261015-0094", "customer": "SENG SENG", "province": "បាត់ដំបង", "url": "https://maps.app.goo.gl/jrAMs7zVAtUUdR7y7?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 96, "lead_no": 94, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=13.1070474,103.2002063&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813469,94286869,100820247,100822504&g_ep=CAISEjI2LjMzLjEuOTYxODkxNDMyMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY5LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=b8d76539-ae41-4157-8433-bb843fba92e5&g_st=ic"},
{"id": "nphk-20261015-0095", "customer": "AH NUCH", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.513692,104.855439&ll=11.513692,104.855439&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 97, "lead_no": 95},
{"id": "nphk-20261015-0096", "customer": "PEOU SOKNY ស្រុកសំបូរ ក្រចេះ", "province": "ក្រចេះ", "url": "https://maps.app.goo.gl/vx3HamdRP5JEKWMR7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 98, "lead_no": 96, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0097", "customer": "SERM SOPI វង្វង់មូលតាពញាក្រែក", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/NfppBsyFiy2z7DDf6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 99, "lead_no": 97, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0098", "customer": "ផារី បាត់ដំបង", "province": "បាត់ដំបង", "url": "https://maps.app.goo.gl/wWvEN5N3MQ7DxLJYA?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 100, "lead_no": 98, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0099", "customer": "PHANNA PHATH ស្វាយរៀង", "province": "ស្វាយរៀង", "url": "https://maps.app.goo.gl/zmqevLisEfN52oweA?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 101, "lead_no": 99, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0100", "customer": "CROIS CAFÉ 271", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 102, "lead_no": 100},
{"id": "nphk-20261015-0101", "customer": "SREY PICH ទួលពង្រ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/TWdw6Ka1RmUhoRg66?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 103, "lead_no": 101, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0102", "customer": "ង៉ែត ញាណ ថ្មបាំង ក្រចេះ", "province": "ក្រចេះ", "url": "https://maps.app.goo.gl/SS9GfTdZNtVAFr9P6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 104, "lead_no": 102, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0103", "customer": "HENG SONY", "province": "កំពត", "url": "https://maps.app.goo.gl/Lj7axsZME21ZYRFF8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 105, "lead_no": 103, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0104", "customer": "MONITA TANN សាលាកំរើក សៀមរាប", "province": "សៀមរាប", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 106, "lead_no": 104},
{"id": "nphk-20261015-0105", "customer": "POV POV", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.833427,104.451803&ll=10.833427,104.451803&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 107, "lead_no": 105},
{"id": "nphk-20261015-0106", "customer": "WAYU STEAM&SAUNA", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.619675,104.174688&ll=10.619675,104.174688&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 108, "lead_no": 106},
{"id": "nphk-20261015-0107", "customer": "សុជាតា​ អ៊ុយ ផ្សារក្រគរ", "province": "ពោធិ៍សាត់", "url": "https://maps.google.com/maps?q=42.553084,0.000008&ll=42.553084,0.000008&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 109, "lead_no": 107},
{"id": "nphk-20261015-0108", "customer": "NAMHENG CHEANG", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/i9nQMiwhVVT1TXrC6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 110, "lead_no": 108, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0109", "customer": "ម៉ីង ទៀង អូត្រេះ", "province": "ព្រះសីហនុ", "url": "https://maps.app.goo.gl/Z6NP579sHZCEAh2T8?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 111, "lead_no": 109, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=10.5617710,103.5578800&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjUuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=bb1c7680-220a-4d5e-a17c-7cc7802a3b69&g_st=ifm"},
{"id": "nphk-20261015-0110", "customer": "PHAN NA វត្តអង្គតាមិញ", "province": "ភ្នំពេញ", "url": "https://www.google.com/maps/place/11%C2%B032'45.3%22N+104%C2%B051'37.1%22E/@11.545903,104.860301,16z/data=!4m4!3m3!8m2!3d11.545903!4d104.860301?entry=ttu&g_ep=EgoyMDI2MDgwNS4xIKXMDSoASAFQAw%3D%3D", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 112, "lead_no": 110},
{"id": "nphk-20261015-0111", "customer": "LY SOK", "province": "ព្រៃវែង", "url": "https://maps.google.com/maps?q=11.259908,105.274687&ll=11.259908,105.274687&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 113, "lead_no": 111},
{"id": "nphk-20261015-0112", "customer": "ឌុល សុវណ្ណនិត ផ្សារស្ពឺ កំពង់ចាម", "province": "កំពង់ចាម", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 114, "lead_no": 112},
{"id": "nphk-20261015-0113", "customer": "OUK PONLEU", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.455301,105.000743&ll=11.455301,105.000743&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 115, "lead_no": 113},
{"id": "nphk-20261015-0114", "customer": "UTH SIEMHONG", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 116, "lead_no": 114},
{"id": "nphk-20261015-0115", "customer": "CHUNGMEI LY", "province": "កំពង់ឆ្នាំង", "url": "https://maps.app.goo.gl/ZmrGSK5sVVtmgTEk6?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 117, "lead_no": 115, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0116", "customer": "CHHING GERRA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/K87quDujsBvqACYNA?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 118, "lead_no": 116, "resolved_url": "https://www.google.com/maps/place/11.530821,104.923610/data=!4m6!3m5!1s0!7e2!8m2!3d11.5308207!4d104.9236105!17m2!4m1!1e3!18m1!1e1?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBjI2LjcuNRgAIPrsDSqLASw5NDI2NzcyNyw5NDI5MjE5NSw5NDI5OTUzMiwxMDA3OTY0OTgsMTAwNzk3NzU3LDEwMDc5NjUzNSw5NDI4MDU3Niw5NDIwNzM5NCw5NDIwNzUwNiw5NDIwODUwNiw5NDIxODY1Myw5NDIyOTgzOSw5NDI3NTE2OCw5NDI3OTYxOSwxMDA3OTE0ODNCAktI&skid=db4e1f9c-e742-41e7-9dc2-f2ccbfdd7d81&g_st=afm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0117", "customer": "MAK NANA", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 119, "lead_no": 117},
{"id": "nphk-20261015-0118", "customer": "ម៉ាក់ ម៉ីយ៉ីង", "province": "កំពង់ចាម", "url": "https://maps.google.com/maps?q=12.301544,105.568075&ll=12.301544,105.568075&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 120, "lead_no": 118},
{"id": "nphk-20261015-0119", "customer": "NONG DAVY", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 121, "lead_no": 119},
{"id": "nphk-20261015-0120", "customer": "VA KHIM", "province": "កំពង់ស្ពឺ", "url": "https://maps.apple/p/HMUUc2MNszxsA9", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 122, "lead_no": 120, "resolved_url": "https://maps.apple.com/place?coordinate=11.808148,104.164605&name=My%20Location&map=h", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0121", "customer": "KA ANGEL កៀនស្វាយ", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.511703,105.053247&ll=11.511703,105.053247&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 123, "lead_no": 121},
{"id": "nphk-20261015-0122", "customer": "KET KIKO បឹងកេងកង", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/yJvqVu1YvTzH5C7V7?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 124, "lead_no": 122, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0123", "customer": "SOU SARITH", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 125, "lead_no": 123},
{"id": "nphk-20261015-0124", "customer": "MTD ផ្សារថ្នល់បត់ផ្លូវលេខ 3", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/5QUa2mZBaYoGDYNN8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 126, "lead_no": 124, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0125", "customer": "នំបុ័ងភ្នំពេញ តាំងក្រសាំង", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 127, "lead_no": 125},
{"id": "nphk-20261015-0126", "customer": "គីម លី បាត់ដំបង", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.083099,102.999665&ll=13.083099,102.999665&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 128, "lead_no": 126},
{"id": "nphk-20261015-0127", "customer": "SOK SOPAL", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.511290,104.948149&ll=11.511290,104.948149&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 129, "lead_no": 127},
{"id": "nphk-20261015-0128", "customer": "EUNG PANHA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/W8PsRuJ5HxSBeVCJ8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 130, "lead_no": 128, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5829590,104.8961900&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b7b2efa2-9ad3-4950-8ee7-b55d8302f3f2&g_st=it"},
{"id": "nphk-20261015-0129", "customer": "KIMSRIV ផ្សារសំរោងយ៉ោង តាកែវ", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.261598,104.823676&ll=11.261598,104.823676&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 131, "lead_no": 129},
{"id": "nphk-20261015-0130", "customer": "NAK បុរីសន្និភាព2", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.498163,104.838022&ll=11.498163,104.838022&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 132, "lead_no": 130},
{"id": "nphk-20261015-0131", "customer": "EM SOMANEA", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/91JPz7XRkFUJ3hZw6?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 133, "lead_no": 131, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0132", "customer": "ម៉ាក់ ចាងមី ត្រពាំងចក កំពង់ស្ពឺ", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.239745,104.643002&ll=11.239745,104.643002&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 134, "lead_no": 132},
{"id": "nphk-20261015-0133", "customer": "PICH CHENDA", "province": "ពោធិ៍សាត់", "url": "https://maps.app.goo.gl/757BEYZaDhipUhnJ9?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 135, "lead_no": 133, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=12.5334662,104.2041783&entry=gps&shh=CAE&lucs=,94297699,100795625,94231188,94280568,47071704,94218641,94282134,100813469,94286869&g_ep=CAISEjI2LjI4LjAuOTQyOTUxNTM4MBgAINeCAypTLDk0Mjk3Njk5LDEwMDc5NTYyNSw5NDIzMTE4OCw5NDI4MDU2OCw0NzA3MTcwNCw5NDIxODY0MSw5NDI4MjEzNCwxMDA4MTM0NjksOTQyODY4NjlCAktI&skid=e49f29dc-569d-46b3-a0eb-d1b7a4351966&g_st=ic"},
{"id": "nphk-20261015-0134", "customer": "នំបុ័ងភ្នំពេញ 271", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/KCXihY4Kx8eoncbEA", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 136, "lead_no": 134, "resolved_url": "https://www.google.com/maps/place/PP+BAKERY+271/@11.5332483,104.9071686,14.5z/data=!4m7!3m6!1s0x310950c20f9e82db:0xdc58f04469f5ce81!8m2!3d11.5277491!4d104.9160724!15sCknhnpPhn4bhnpThnrvhn5DhnoThnpfhn5LhnpPhn4bhnpbhn4Hhnokg4Z6P4Z624Z-G4Z6E4Z6A4Z-S4Z6a4Z6f4Z624Z-G4Z6EWk0iS-Gek-GfhuGelOGeu-GfkOGehCDhnpfhn5LhnpPhn4bhnpbhn4Hhnokg4Z6P4Z624Z-G4Z6EIOGegOGfkuGemuGen-GetuGfhuGehJIBBmJha2VyeeABAA!16s%2Fg%2F11c1n85lvk!18m1!1e1?entry=tts&g_ep=EgoyMDI2MDgwMy4wIPu8ASoASAFQAw%3D%3D&skid=4083d675-daef-4553-a1e9-f84454b3b35e", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0135", "customer": "NUN KUNTHEA", "province": "ស្វាយរៀង", "url": "https://maps.google.com/maps?q=11.132092,105.772899&ll=11.132092,105.772899&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 137, "lead_no": 135},
{"id": "nphk-20261015-0136", "customer": "SOPHYA EM ព្រែកឯង", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Uqw8Z8jMZan7YipU7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 138, "lead_no": 136, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0137", "customer": "VUTHEA SOY ជម្ពូវ័ន", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.527918,104.812967&ll=11.527918,104.812967&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 139, "lead_no": 137},
{"id": "nphk-20261015-0138", "customer": "SAM SY CHENDA ស្រុកបាកាន ពោធិសាត់", "province": "ពោធិ៍សាត់", "url": "https://maps.google.com/maps?q=12.619310,103.758999&ll=12.619310,103.758999&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 140, "lead_no": 138},
{"id": "nphk-20261015-0139", "customer": "ហម វណ្ណា ស្តុបលំហែ កំពង់ចាម", "province": "កំពង់ចាម", "url": "https://maps.app.goo.gl/i8QeKNF89QizTJqK8?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 141, "lead_no": 139, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0140", "customer": "PANG MARADY", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/ewGgY6QsLx6YZ35H9?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 142, "lead_no": 140, "resolved_url": "https://www.google.com/maps/place/11.358034,104.868378/data=!4m6!3m5!1s0!7e2!8m2!3d11.3580344!4d104.8683784!18m1!1e1?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI2LjIxLjEYACD67A0qiwEsOTQyNjc3MjcsOTQyOTIxOTUsOTQyOTk1MzIsMTAwNzk2NDk4LDEwMDc5Nzc2MSwxMDA3OTY1MzUsOTQyODA1NzYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksMTAwODE1NjM1QgJLSA%3D%3D&skid=d00a9381-d3bf-43a1-9146-3bd7450fe55b&g_st=atm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0141", "customer": "HEAN NAVOEUN កំពង់ធំ", "province": "កំពង់ធំ", "url": "https://maps.google.com/maps?q=12.707084,104.868824&ll=12.707084,104.868824&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 143, "lead_no": 141},
{"id": "nphk-20261015-0142", "customer": "KIM GECH ការ៉ាសលាងឡាន ចំការស្ពៃ កំពង់សោម", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.617040,103.526751&ll=10.617040,103.526751&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 144, "lead_no": 142},
{"id": "nphk-20261015-0143", "customer": "THIM SOVANNARY កាំកូ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.592292,104.896368&ll=11.592292,104.896368&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 145, "lead_no": 143},
{"id": "nphk-20261015-0144", "customer": "THE STATION COFFEE សែនសុខ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/G7YGtvwJTWXvTcY87?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 146, "lead_no": 144, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0145", "customer": "AH THOEUN សំរោងអណ្ដែត", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.578700,104.858464&ll=11.578700,104.858464&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 147, "lead_no": 145},
{"id": "nphk-20261015-0146", "customer": "ផ្ទះនំបញ្ខុក ឈូកមាស", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.575450,104.851054&ll=11.575450,104.851054&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 148, "lead_no": 146},
{"id": "nphk-20261015-0147", "customer": "ចំរើន គីមរ៉ុង ក្រុងបានលុង", "province": "រតនគិរី", "url": "https://maps.google.com/maps?q=13.742653,107.006545&ll=13.742653,107.006545&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 149, "lead_no": 147},
{"id": "nphk-20261015-0148", "customer": "LENG KANHA មេសាង ព្រៃវែង", "province": "ព្រៃវែង", "url": "https://maps.google.com/maps?q=11.327202,105.543926&ll=11.327202,105.543926&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 150, "lead_no": 148},
{"id": "nphk-20261015-0149", "customer": "SU KIM កំពត", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.613714,104.181695&ll=10.613714,104.181695&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 151, "lead_no": 149},
{"id": "nphk-20261015-0150", "customer": "SREY LEAK ក្រចេះ", "province": "ក្រចេះ", "url": "https://maps.google.com/maps?q=12.785226,106.277055&ll=12.785226,106.277055&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 152, "lead_no": 150},
{"id": "nphk-20261015-0151", "customer": "អា ហន ពោធិ៍សាត់", "province": "ពោធិ៍សាត់", "url": "https://maps.google.com/maps?q=12.537006,103.916276&ll=12.537006,103.916276&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 153, "lead_no": 151},
{"id": "nphk-20261015-0152", "customer": "DA NY ស្អាង", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.358377,104.983906&ll=11.358377,104.983906&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 154, "lead_no": 152},
{"id": "nphk-20261015-0153", "customer": "វត្តី វត្តី សន្ទុក ស្អាង", "province": "កំពង់ធំ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 155, "lead_no": 153},
{"id": "nphk-20261015-0154", "customer": "THIDA LUCKY ច្បាអំពៅ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.512853,104.945805&ll=11.512853,104.945805&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 156, "lead_no": 154},
{"id": "nphk-20261015-0155", "customer": "THEARY ស្រុកបាកាន ពោធិសាត់", "province": "ពោធិ៍សាត់", "url": "https://maps.google.com/maps?q=12.598427,103.791926&ll=12.598427,103.791926&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 157, "lead_no": 155},
{"id": "nphk-20261015-0156", "customer": "DARY CHHORN កំពង់ចាម", "province": "កំពង់ចាម", "url": "https://maps.apple/p/cJ2dtuy-2EYT-d", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 158, "lead_no": 156, "resolved_url": "https://maps.apple.com/place?address=National%20Highway%207,%20Kampong%20Cham,%20Cambodia&coordinate=11.999801,105.445177&name=National%20Highway%207&map=explore", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0157", "customer": "ដានី កាហ្វេ ស្វាយរៀងទន្លេវៃគោ", "province": "ស្វាយរៀង", "url": "https://maps.app.goo.gl/cRvmWaXJPm8eLnzt5?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 159, "lead_no": 157, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0158", "customer": "ប៊ី យី ទម្លាប់តាកែវ", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=10.646703,104.870825&ll=10.646703,104.870825&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 160, "lead_no": 158},
{"id": "nphk-20261015-0159", "customer": "SIVLANG LIM ឈូកមាស", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.568755,104.853572&ll=11.568755,104.853572&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 161, "lead_no": 159},
{"id": "nphk-20261015-0160", "customer": "VILA LUY សៀមរាប", "province": "សៀមរាប", "url": "https://share.google/OiDS85CUqBuGJQyyZ", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 162, "lead_no": 160, "resolution_note": "Map link redirected outside the supported map providers."},
{"id": "nphk-20261015-0161", "customer": "THE FRESS ទួលសង្កែ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/ThGiKiBBoPqxx1Ty5?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 163, "lead_no": 161, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5954700,104.9145390&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=cbc638e8-c340-46e0-8511-252b997b52ed&g_st=it"},
{"id": "nphk-20261015-0162", "customer": "NK NK បឹងកង", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.582141,104.890701&ll=11.582141,104.890701&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 164, "lead_no": 162},
{"id": "nphk-20261015-0163", "customer": "JAY UNG ស្ពានអាកាស 7មករា", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/d7ZWzt3xmSWDeRKZA?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 165, "lead_no": 163, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5645881,104.8887910&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100799877,94286869&g_ep=CAISEjI2LjIxLjEuOTE3Mzg1NDY3MBgAINeCAypJLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDc5OTg3Nyw5NDI4Njg2OUICS0g%3D&skid=534d4e3e-ecbd-4e21-ab15-b7760b468a9a&g_st=ic"},
{"id": "nphk-20261015-0164", "customer": "ជា ទិត្យ សូម៉ាតឿន(ABC ព្រៃស)", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 166, "lead_no": 164},
{"id": "nphk-20261015-0165", "customer": "SENG WANDEAN ឬស្សីកែវ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/UPgiHG9jrx51SbVBA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 167, "lead_no": 165, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.6032710,104.9133091&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,100808659,94282134,94286869,100813014&g_ep=CAISEjI2LjIzLjQuOTI0MzY0MTg2MBgAINeCAypTLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDEwMDgwODY1OSw5NDI4MjEzNCw5NDI4Njg2OSwxMDA4MTMwMTRCAktI&skid=51c53ec1-1275-43e3-918a-5998ddf905de&g_st=it"},
{"id": "nphk-20261015-0166", "customer": "LIM LONG កាន់ណាបាត់ដំបង", "province": "បាត់ដំបង", "url": "https://maps.app.goo.gl/4vUfyVs638ZBPAvH6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 168, "lead_no": 166, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=12.8777222,103.3779722&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,100809209,94218641,94282134,100799872,94286869&g_ep=CAISEjI2LjIwLjQuOTEzODcwMjQ0MBgAINeCAypTLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDEwMDgwOTIwOSw5NDIxODY0MSw5NDI4MjEzNCwxMDA3OTk4NzIsOTQyODY4NjlCAktI&skid=eecf08ac-384f-46e5-abeb-31c6acb4f409&g_st=it"},
{"id": "nphk-20261015-0167", "customer": "MR.DAD COFFEE ច្បារអំពៅ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/tHQQMgeftfR1LewGA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 169, "lead_no": 167, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5312136,104.9475468&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,100808654,94282134,100813469,94286869&g_ep=CAISEjI2LjIxLjEuOTE3Mzg1NDY3MBgAIIgnKlMsOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsMTAwODA4NjU0LDk0MjgyMTM0LDEwMDgxMzQ2OSw5NDI4Njg2OUICS0g%3D&skid=7e77bd63-1c15-4a81-a567-a593895bfadc&g_st=it"},
{"id": "nphk-20261015-0168", "customer": "JING SMALL GIRL ផ្សារចំបក់ តាកែវ", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.240991,104.811197&ll=11.240991,104.811197&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 170, "lead_no": 168},
{"id": "nphk-20261015-0169", "customer": "ពន្លឺ ជីវិតរីករាយ ផ្សារកន្ទួត កំពង់ស្ពឺ", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/AGZamepQ3QjC9Lnd6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 171, "lead_no": 169, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0170", "customer": "KARONAK អូសោម", "province": "ពោធិ៍សាត់", "url": "https://maps.google.com/maps?q=12.078757,103.187278&ll=12.078757,103.187278&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 172, "lead_no": 170},
{"id": "nphk-20261015-0171", "customer": "LEAP LEAP អូឡាំពីក", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/H7S5S75ECm5Ravjr7?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 173, "lead_no": 171, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0172", "customer": "ING KIMLEANG ឬស្សីកែវ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.614956,104.911557&ll=11.614956,104.911557&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 174, "lead_no": 172},
{"id": "nphk-20261015-0173", "customer": "VUOCHLY បឹងស្នោរ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.514152,104.966048&ll=11.514152,104.966048&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 175, "lead_no": 173},
{"id": "nphk-20261015-0174", "customer": "MONUNEATH ទូលគោក", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/rAYhP91Sn5difDmCA?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 176, "lead_no": 174, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0175", "customer": "VIN MART ទួលគោក", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Vribzjn6Hub5NTv98?g_st=ac", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 177, "lead_no": 175, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0176", "customer": "L MENG ផ្លូវជាសុភារា", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/xZ46JJPNjjsE4Nvf9?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 178, "lead_no": 176, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0177", "customer": "SREYLEAP SENG", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.500618,104.789379&ll=11.500618,104.789379&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 179, "lead_no": 177},
{"id": "nphk-20261015-0178", "customer": "BUNNE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/CtujqdSPzu24JnJj7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 180, "lead_no": 178, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0179", "customer": "MAICHA CAFE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/cJVXK3zxfVpkEQKb8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 181, "lead_no": 179, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0180", "customer": "HAK NYTA", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.559623,104.855221&ll=11.559623,104.855221&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 182, "lead_no": 180},
{"id": "nphk-20261015-0181", "customer": "មឿន ភារ៉ា", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.475030,104.749737&ll=11.475030,104.749737&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 183, "lead_no": 181},
{"id": "nphk-20261015-0182", "customer": "CHANDOEUN MAO", "province": "មណ្ឌលគិរី", "url": "https://g.co/kgs/dWm9tK4", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 184, "lead_no": 182, "resolution_note": "Map link redirected outside the supported map providers."},
{"id": "nphk-20261015-0183", "customer": "CHAN THY", "province": "ប៉ោយប៉ែត", "url": "https://www.google.com/maps/place/JHVG%2B964+Meguiar's+krong+poi+pet,+AH1,+Krong+Poi+Pet/@13.6433782,102.5755929,16z/data=!4m6!3m5!1s0x311b17cce72c87ab:0xab95aea274f14834!8m2!3d13.6433782!4d102.5755929!16s%2Fg%2F11mx5xnrv2?hl=en-KH&gl=kh", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 185, "lead_no": 183},
{"id": "nphk-20261015-0184", "customer": "LY Ly", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.570794,104.919895&ll=11.570794,104.919895&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 186, "lead_no": 184},
{"id": "nphk-20261015-0185", "customer": "YOEURN SOKYENG", "province": "ស្វាយរៀង", "url": "https://maps.app.goo.gl/QtjJ4HhUkfJmTzgx6?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 187, "lead_no": 185, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0186", "customer": "KE SOKHA", "province": "ត្បូងឃ្មុំ", "url": "https://maps.google.com/maps?q=12.020603,105.883518&ll=12.020603,105.883518&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 188, "lead_no": 186},
{"id": "nphk-20261015-0187", "customer": "CHANBO VIBOL", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 189, "lead_no": 187},
{"id": "nphk-20261015-0188", "customer": "LONG SOKHOM", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.235964,104.868356&ll=11.235964,104.868356&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 190, "lead_no": 188},
{"id": "nphk-20261015-0189", "customer": "ងឿន វណ្ណរ៉េត", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.082886,103.206204&ll=13.082886,103.206204&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 191, "lead_no": 189},
{"id": "nphk-20261015-0190", "customer": "ភឿន ចរិយា", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.565854,104.870867&ll=11.565854,104.870867&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 192, "lead_no": 190},
{"id": "nphk-20261015-0191", "customer": "OLE CAFE", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.509263,104.855192&ll=11.509263,104.855192&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 193, "lead_no": 191},
{"id": "nphk-20261015-0192", "customer": "LITTLE CAFÉ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.522900,104.853346&ll=11.522900,104.853346&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 194, "lead_no": 192},
{"id": "nphk-20261015-0193", "customer": "PHAI VITA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/wSo5jo2Y6LaLeuA36?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 195, "lead_no": 193, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0194", "customer": "វែង ភិរុណ", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=12.771600,102.876740&ll=12.771600,102.876740&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 196, "lead_no": 194},
{"id": "nphk-20261015-0195", "customer": "SEY SEY", "province": "កោះកុង", "url": "https://maps.app.goo.gl/eDkZ8bE6yzyk1q8bA?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 197, "lead_no": 195, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0196", "customer": "ស្រីលក្ខ័", "province": "ព្រះសីហនុ", "url": "https://maps.app.goo.gl/CcPzAFNUGe4AmbkG7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 198, "lead_no": 196, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=10.6907040,103.8113383&entry=gps&shh=CAE&lucs=,94297699,100808508,94284499,94231188,94280568,47071704,94218641,94282134,94286869&g_ep=CAISEjI2LjE2LjAuODk4OTU0MjE1MBgAINeCAypSLDk0Mjk3Njk5LDEwMDgwODUwOCw5NDI4NDQ5OSw5NDIzMTE4OCw5NDI4MDU2OCw0NzA3MTcwNCw5NDIxODY0MSw5NDI4MjEzNCw5NDI4Njg2OUICS0g%3D&skid=8e1b1a7f-5fa0-46a7-9d6d-cd6ab0ef4d31&g_st=ifm"},
{"id": "nphk-20261015-0197", "customer": "MR.DAD COFFEE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/XkKG3YiCBxB4KRqN8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 199, "lead_no": 197, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0198", "customer": "សុខ វណ្ណី", "province": "កោះកុង", "url": "https://maps.google.com/maps?q=11.567670,102.955901&ll=11.567670,102.955901&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 200, "lead_no": 198},
{"id": "nphk-20261015-0199", "customer": "H LYHACH", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/eWGPhu33W8jP7XLM8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 201, "lead_no": 199, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0200", "customer": "AH RY", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/hnbyFqekz2MCcdd39?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 202, "lead_no": 200, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0201", "customer": "TA KOY", "province": "ព្រៃវែង", "url": "https://maps.google.com/maps?q=11.432911,105.596452&ll=11.432911,105.596452&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 203, "lead_no": 201},
{"id": "nphk-20261015-0202", "customer": "THEART TY", "province": "តាកែវ", "url": "https://maps.app.goo.gl/ERV3xXTYyAiAFcRXA?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 204, "lead_no": 202, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0203", "customer": "ស្រី ខេង", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/ELZom383UKzg3Fmc9?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 205, "lead_no": 203, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.1060719,103.9186756&entry=gps&shh=CAE&lucs=,94297699,94284472,94231188,94280568,47071704,94218641,94282134,94286869&g_ep=CAISEjI1LjQ5LjkuODM4ODk5MTgzMBgAINeCAypILDk0Mjk3Njk5LDk0Mjg0NDcyLDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDk0Mjg2ODY5QgJLSA%3D%3D&skid=8c1cb931-3544-4290-8aa9-2235628aa63f&g_st=ifm"},
{"id": "nphk-20261015-0204", "customer": "BLUEBIRD INTERNATIONL EDUCATION", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Z9LBqRyofxNzY8Qr5?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 206, "lead_no": 204, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0205", "customer": "MACH DARA ព្រែកហូរ", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.441557,104.927903&ll=11.441557,104.927903&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 207, "lead_no": 205},
{"id": "nphk-20261015-0206", "customer": "VEN KIMHENG", "province": "ព្រៃវែង", "url": "https://maps.google.com/maps?q=11.573328,105.420544&ll=11.573328,105.420544&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 208, "lead_no": 206},
{"id": "nphk-20261015-0207", "customer": "The one coffee", "province": "ស្វាយរៀង", "url": "https://maps.google.com/maps?q=11.091688,105.791785&ll=11.091688,105.791785&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 209, "lead_no": 207},
{"id": "nphk-20261015-0208", "customer": "អមតៈម៉ាតនិងកាហ្វេ", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=10.919648,104.603997&ll=10.919648,104.603997&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 210, "lead_no": 208},
{"id": "nphk-20261015-0209", "customer": "ជេង ដាណៃ", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.346004,103.841554&ll=13.346004,103.841554&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 211, "lead_no": 209},
{"id": "nphk-20261015-0210", "customer": "KAN NHA សិរីសោភ័ណ បន្ទាយមានជ័យ", "province": "បន្ទាយមានជ័យ", "url": "https://maps.app.goo.gl/SRr8AEFtLo1MYCyh8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 212, "lead_no": 210, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0211", "customer": "រ័ត្ន មនោរិទ្ធ", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/iqsdUiyvoDj391qT9", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 213, "lead_no": 211, "resolved_url": "https://www.google.com/maps/place/12.395248,105.082778/data=!4m6!3m5!1s0!7e2!8m2!3d12.3952484!4d105.0827781?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESCjExLjEyOS4xMDMYACDXggMqGyw5NDIwNzUwNiw5NDIwODUwNiw5NDIxODY1M0ICS0g%3D&skid=3fe9ce11-f8c4-45f0-9f86-0399ea45993b", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0212", "customer": "ប៊ុនធេង", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.582224,104.849146&ll=11.582224,104.849146&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 214, "lead_no": 212},
{"id": "nphk-20261015-0213", "customer": "牡丹花", "province": "ព្រះសីហនុ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 215, "lead_no": 213},
{"id": "nphk-20261015-0214", "customer": "ម៉ី ក្បាលស្ពាន", "province": "ប៉ោយប៉ែត", "url": "https://maps.google.com/maps?q=13.660573,102.551352&ll=13.660573,102.551352&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 216, "lead_no": 214},
{"id": "nphk-20261015-0215", "customer": "LEANG", "province": "ត្បូងឃ្មុំ", "url": "https://maps.google.com/maps?q=11.826201,105.783795&ll=11.826201,105.783795&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 217, "lead_no": 215},
{"id": "nphk-20261015-0216", "customer": "CHOUN CHEASEYHA", "province": "កំពង់ឆ្នាំង", "url": "https://maps.google.com/maps?q=12.253794,104.670043&ll=12.253794,104.670043&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 218, "lead_no": 216},
{"id": "nphk-20261015-0217", "customer": "ទេពនិមន្ដ", "province": "កណ្តាល", "url": "https://goo.gl/maps/zDfGmNn5UzMqfPhG8?g_st=ac", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 219, "lead_no": 217, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.582924,104.970368&entry=gps&g_ep=CAESBzI2LjE2LjUYACCIJyqLASw5NDI2NzcyNyw5NDI5MjE5NSw5NDI5OTUzMiwxMDA3OTY0OTgsMTAwNzk3NzYxLDEwMDc5NjUzNSw5NDI4MDU3Niw5NDIwNzM5NCw5NDIwNzUwNiw5NDIwODUwNiw5NDIxODY1Myw5NDIyOTgzOSw5NDI3NTE2OCw5NDI3OTYxOSwxMDA4MTA0NThCAktI&skid=49a92ffc-f193-488e-9473-134b2e240b7d&shorturl=1"},
{"id": "nphk-20261015-0218", "customer": "Caltex", "province": "ព្រៃវែង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 220, "lead_no": 218},
{"id": "nphk-20261015-0219", "customer": "H LYHACH", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/cBTp18aLGUbMDFmB8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 221, "lead_no": 219, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0220", "customer": "SOMBO MANA", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.074360,104.496803&ll=11.074360,104.496803&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 222, "lead_no": 220},
{"id": "nphk-20261015-0221", "customer": "MUY SOCHENDA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/2dLY1dJ6s2tJJbPDA?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 223, "lead_no": 221, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0222", "customer": "សុគង់ ឡន កំបូល", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.487780,104.789880&ll=11.487780,104.789880&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 224, "lead_no": 222},
{"id": "nphk-20261015-0223", "customer": "SEAVMEY", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.437672,104.967744&ll=11.437672,104.967744&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 225, "lead_no": 223},
{"id": "nphk-20261015-0224", "customer": "VANNY THON", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.576389,103.565223&ll=10.576389,103.565223&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 226, "lead_no": 224},
{"id": "nphk-20261015-0225", "customer": "CHHAY BOEY តាខ្មៅ", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.465906,104.966713&ll=11.465906,104.966713&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 227, "lead_no": 225},
{"id": "nphk-20261015-0226", "customer": "SUM CHANNY", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/YqonEUYv9wnoPM5y8?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 228, "lead_no": 226, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5772464,104.8330054&entry=gps&shh=CAE&lucs=,94297699,100808508,94284454,94231188,94280568,47071704,94218641,94282134,100799872,94286869&g_ep=CAISEjI2LjEzLjYuODg4MzU5NjE4MBgAINeCAypcLDk0Mjk3Njk5LDEwMDgwODUwOCw5NDI4NDQ1NCw5NDIzMTE4OCw5NDI4MDU2OCw0NzA3MTcwNCw5NDIxODY0MSw5NDI4MjEzNCwxMDA3OTk4NzIsOTQyODY4NjlCAktI&skid=3b427362-22a7-4ce4-83a7-2c9aa3fced1c&g_st=ifm"},
{"id": "nphk-20261015-0227", "customer": "ឥន្រ្ទី បូព៌ា", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/LFmkkwGBtki4se9k9?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 229, "lead_no": 227, "resolved_url": "https://www.google.com/maps/place/GRRG%2B752+LH+Tattoo+%E1%9E%85%E1%9E%B6%E1%9E%80%E1%9F%8B%E1%9E%9F%E1%9E%B6%E1%9E%80%E1%9F%8B+24%E1%9E%98%E1%9F%89%E1%9F%84%E1%9E%84,+Phnom+Penh/data=!4m6!3m5!1s0x31094f0020c7adc1:0x97ff5caa72f80115!7e2!8m2!3d11.5406351!4d104.8253907!18m1!1e1?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI2LjE1LjEYACDXggMqlAEsOTQyNjc3MjcsOTQyOTIxOTUsOTQyOTk1MzIsMTAwNzk2NDk4LDEwMDc5Nzc2MSwxMDA3OTY1MzUsOTQyODQ0NTcsOTQyODA1NzYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksMTAwNzk5MjUxQgJLSA%3D%3D&skid=c7d85147-475d-48ca-b034-07bbb3bf0c74&g_st=atm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0228", "customer": "GALLERY COFFE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Rq9syLtSX1RKtdyf9?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 230, "lead_no": 228, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0229", "customer": "KAFE SOYA HOUSE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/BgFqJrRCSQjnbbSV9?g_st=ac", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 231, "lead_no": 229, "resolved_url": "https://www.google.com/maps/place/DSL+Apartment,+Street+2004,+Phnom+Penh/data=!4m6!3m5!1s0x310951e8c16ff2c5:0xb57a03ff150fd880!7e2!8m2!3d11.552963!4d104.86128049999999!18m1!1e1?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI2LjE1LjEYACCenQoqgQEsOTQyNjc3MjcsOTQyOTIxOTUsOTQyOTk1MzIsMTAwNzk2NDk4LDEwMDc5Nzc2MSwxMDA3OTY1MzUsOTQyODA1NzYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTlCAktI&skid=8ee825d6-cc3f-4334-9a16-a5cad5f992d8&g_st=ac", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0230", "customer": "SAK COFFEE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Xk49StYVdgK7m9cp9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 232, "lead_no": 230, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0231", "customer": "វណ្ណះ ចរិយា", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/m2HQMBsGgqoU3pSf6?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 233, "lead_no": 231, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0232", "customer": "HENG SAMNANG", "province": "ព្រៃវែង", "url": "https://maps.google.com/maps?q=11.257800,105.401289&ll=11.257800,105.401289&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 234, "lead_no": 232},
{"id": "nphk-20261015-0233", "customer": "NY TANG CALTEX", "province": "កំពង់ឆ្នាំង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 235, "lead_no": 233},
{"id": "nphk-20261015-0234", "customer": "OUNPOV", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.502077,104.809401&ll=11.502077,104.809401&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 236, "lead_no": 234},
{"id": "nphk-20261015-0235", "customer": "CHENG DANET", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.367083,103.838365&ll=13.367083,103.838365&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 237, "lead_no": 235},
{"id": "nphk-20261015-0236", "customer": "JEE DAEN", "province": "កំពង់ចាម", "url": "https://maps.google.com/maps?q=11.939365,105.167322&ll=11.939365,105.167322&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 238, "lead_no": 236},
{"id": "nphk-20261015-0237", "customer": "MI NEA", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/CfQrSEwa7ah9esWQ7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 239, "lead_no": 237, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0238", "customer": "SAR KEOKANHA", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.478527,104.894221&ll=11.478527,104.894221&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 240, "lead_no": 238},
{"id": "nphk-20261015-0239", "customer": "LEANG LEANG", "province": "ប៉ៃលិន", "url": "https://maps.google.com/maps?q=12.927933,102.497464&ll=12.927933,102.497464&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 241, "lead_no": 239},
{"id": "nphk-20261015-0240", "customer": "PHENG AN AN", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.333880,104.719774&ll=11.333880,104.719774&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 242, "lead_no": 240},
{"id": "nphk-20261015-0241", "customer": "YU MI", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.488753,104.813017&ll=11.488753,104.813017&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 243, "lead_no": 241},
{"id": "nphk-20261015-0242", "customer": "Central Beach Resort Long Set Beach", "province": "ព្រះសីហនុ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 244, "lead_no": 242},
{"id": "nphk-20261015-0243", "customer": "MOLII COFFEE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/2Q7f3eShrBa1mFsu5?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 245, "lead_no": 243, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0244", "customer": "NONG DAVY", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.514568,104.854154&ll=11.514568,104.854154&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 246, "lead_no": 244},
{"id": "nphk-20261015-0245", "customer": "SREY NICH", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 247, "lead_no": 245},
{"id": "nphk-20261015-0246", "customer": "KOEM SREYRATH", "province": "តាកែវ", "url": "https://maps.app.goo.gl/49L6KmGJf6SXJZRg6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 248, "lead_no": 246, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0247", "customer": "PHO MONICA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/iAC73XScurjxpswx7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 249, "lead_no": 247, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0248", "customer": "SOMALY", "province": "បន្ទាយមានជ័យ", "url": "https://maps.app.goo.gl/NUSnfMVEGJHArCsp6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 250, "lead_no": 248, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=13.4662464,103.0137777&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,94286869&g_ep=CAISEjI2LjEwLjIuODc3MzE3OTEwMBgAINeCAyo_LDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDk0Mjg2ODY5QgJLSA%3D%3D&skid=bef26b1e-a15c-48c5-84b1-b39a81a0b492&g_st=it"},
{"id": "nphk-20261015-0249", "customer": "ម៉ាក់ លីម៉េង", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.068154,104.287818&ll=13.068154,104.287818&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 251, "lead_no": 249},
{"id": "nphk-20261015-0250", "customer": "VIN PARY", "province": "កំពត", "url": "https://maps.app.goo.gl/NNSrDuf5DGMzpJbE9?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 252, "lead_no": 250, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0251", "customer": "DAVID", "province": "សៀមរាប", "url": "https://maps.app.goo.gl/8wT1US3ZQFRDPwEk6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 253, "lead_no": 251, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0252", "customer": "សុធា សុថាវី", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/4nmZtSWCHSqZf4hD6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 254, "lead_no": 252, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0253", "customer": "SAROEURN", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/Rf6RMuG2Wj7DHRta9?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 255, "lead_no": 253, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0254", "customer": "NANFA វត្ដអង្គពោធិ៍ញ្ញាណ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.526595,104.897529&ll=11.526595,104.897529&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 256, "lead_no": 254},
{"id": "nphk-20261015-0255", "customer": "BilLY COFFEEស្អាង", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 257, "lead_no": 255},
{"id": "nphk-20261015-0256", "customer": "THEA JULY", "province": "ពោធិ៍សាត់", "url": "https://maps.google.com/maps?q=12.552896,103.871537&ll=12.552896,103.871537&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 258, "lead_no": 256},
{"id": "nphk-20261015-0257", "customer": "KANNITHA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/9qvYiqJCaypKNhJd9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 259, "lead_no": 257, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0258", "customer": "PISEY KO", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.675991,104.561729&ll=10.675991,104.561729&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 260, "lead_no": 258},
{"id": "nphk-20261015-0259", "customer": "HAK SOPHAL", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.100332,103.207351&ll=13.100332,103.207351&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 261, "lead_no": 259},
{"id": "nphk-20261015-0260", "customer": "ស្រីល័ក្ខ ភូមិត្រពាំងពោ", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.645619,104.667977&ll=10.645619,104.667977&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 262, "lead_no": 260},
{"id": "nphk-20261015-0261", "customer": "MR.DAD CAFÉ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/tVQYqp4mFrL8Gghp6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 263, "lead_no": 261, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0262", "customer": "PANHAPICH គួរស្រូវ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.441673,104.890393&ll=11.441673,104.890393&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 264, "lead_no": 262},
{"id": "nphk-20261015-0263", "customer": "LV  Coffee", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/xurdeGGDyoCUxRAx5", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 265, "lead_no": 263, "resolved_url": "https://www.google.com/maps/place/%E1%9E%A2%E1%9E%B7%E1%9E%9B%26%E1%9E%9C%E1%9E%B8%E1%9E%80%E1%9E%B6%E1%9E%A0%E1%9F%92%E1%9E%9C%E1%9F%81/@11.5673177,104.9086733,20.75z/data=!4m6!3m5!1s0x3109510002b6629f:0x821de1bacf977552!8m2!3d11.5671125!4d104.9091186!16s%2Fg%2F11zjl6zdyq?entry=tts&g_ep=EgoyMDI2MDIyNS4wIPu8ASoASAFQAw%3D%3D&skid=a1886211-4d16-40f4-9495-c899247cd41c", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0264", "customer": "LIM NGEAN", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/YPTkvLvFy3hpJk469?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 266, "lead_no": 264, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0265", "customer": "SOK LEAPHEA", "province": "បន្ទាយមានជ័យ", "url": "https://maps.google.com/maps?q=13.535348,103.022473&ll=13.535348,103.022473&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 267, "lead_no": 265},
{"id": "nphk-20261015-0266", "customer": "AH LY MOLY", "province": "ព្រះសីហនុ", "url": "https://maps.app.goo.gl/zV9ZNqL5R8prEsYSA?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 268, "lead_no": 266, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=10.6172998,103.5363740&entry=gps&shh=CAE&lucs=,94297699,100794546,94284454,94231188,94280568,47071704,94218641,94282134,100799877,94286869,100796593&g_ep=CAISEjI2LjA4LjIuODcwOTc4MTE2MBgAIIgnKmYsOTQyOTc2OTksMTAwNzk0NTQ2LDk0Mjg0NDU0LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDc5OTg3Nyw5NDI4Njg2OSwxMDA3OTY1OTNCAktI&skid=0e5bffe0-a880-4318-90fc-b1b8dd7d668d&g_st=ifm"},
{"id": "nphk-20261015-0267", "customer": "GM PHEAK", "province": "សៀមរាប", "url": "https://maps.app.goo.gl/22SwNJTdVYbpVtMa6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 269, "lead_no": 267, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0268", "customer": "NEANG POVDARAVONTEY", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.667173,104.561084&ll=10.667173,104.561084&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 270, "lead_no": 268},
{"id": "nphk-20261015-0269", "customer": "MEAN RITHY", "province": "សៀមរាប", "url": "https://maps.apple.com/place?address=Sok%20San%20Road,%20Siem%20Reap,%20Cambodia&coordinate=13.354861,103.849467&name=The%20Night%20Mini%20Mart&place-id=I837E74F5413C7CD5&map=explore", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 271, "lead_no": 269},
{"id": "nphk-20261015-0270", "customer": "SOK LA", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.161750,104.853254&ll=11.161750,104.853254&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 272, "lead_no": 270},
{"id": "nphk-20261015-0271", "customer": "MART", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.621327,104.882739&ll=11.621327,104.882739&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 273, "lead_no": 271},
{"id": "nphk-20261015-0272", "customer": "BO KAKNIKA", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.661829,104.798724&ll=11.661829,104.798724&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 274, "lead_no": 272},
{"id": "nphk-20261015-0273", "customer": "SO NITA", "province": "កំពង់ធំ", "url": "https://maps.google.com/maps?q=12.901877,105.431184&ll=12.901877,105.431184&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 275, "lead_no": 273},
{"id": "nphk-20261015-0274", "customer": "DY DARA", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.611208,104.914855&ll=11.611208,104.914855&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 276, "lead_no": 274},
{"id": "nphk-20261015-0275", "customer": "HAY", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Uxitnj8mXxYRzsLh8?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 277, "lead_no": 275, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0276", "customer": "LA BELLA COFFEE", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.395932,104.801630&ll=11.395932,104.801630&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 278, "lead_no": 276},
{"id": "nphk-20261015-0277", "customer": "MAICHEU", "province": "សៀមរាប", "url": "https://maps.app.goo.gl/tVQYqp4mFrL8Gghp6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 279, "lead_no": 277, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0278", "customer": "CHIN HOK", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/EATNm5sagqoNsrmJ7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 280, "lead_no": 278, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5936063,104.9269022&entry=gps&lucs=,94297699,94275415,94284484,94231188,94280568,47071704,94218641,94282134,94286869,100796589&g_ep=CAISEjI1LjQ5LjkuODM4ODk5MTgzMBgAINeCAypbLDk0Mjk3Njk5LDk0Mjc1NDE1LDk0Mjg0NDg0LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDk0Mjg2ODY5LDEwMDc5NjU4OUICS0g%3D&skid=1fcf3255-c09b-4ebf-b442-2999ec5c9da0&g_st=it"},
{"id": "nphk-20261015-0279", "customer": "HUNI LIN", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.443935,104.448453&ll=11.443935,104.448453&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 281, "lead_no": 279},
{"id": "nphk-20261015-0280", "customer": "BUN LEANG កំពង់ចាម", "province": "កំពង់ធំ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 282, "lead_no": 280},
{"id": "nphk-20261015-0281", "customer": "SREY POV", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.518846,104.876302&ll=11.518846,104.876302&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 283, "lead_no": 281},
{"id": "nphk-20261015-0282", "customer": "SITHA PHONESHOP", "province": "ក្រចេះ", "url": "https://maps.google.com/maps?q=12.417801,105.924494&ll=12.417801,105.924494&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 284, "lead_no": 282},
{"id": "nphk-20261015-0283", "customer": "QM SERVICES", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/6wGQjozAM8RG5s9R9?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 285, "lead_no": 283, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5028316,104.8800410&entry=gps&shh=CAE&lucs=,94286590,94297699,94275415,94284505,94231188,94280568,47071704,94218641,94282134,94292074,94286869&g_ep=CAISEjI2LjA0LjEuODU4MjY5MDE5MBgAINeCAypjLDk0Mjg2NTkwLDk0Mjk3Njk5LDk0Mjc1NDE1LDk0Mjg0NTA1LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDk0MjkyMDc0LDk0Mjg2ODY5QgJLSA%3D%3D&skid=92a33825-9e3b-4dfd-8ba7-e2083ad5d9ce&g_st=ic"},
{"id": "nphk-20261015-0284", "customer": "KIM CHHENGHONG", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/gWBwa1XvEqGL9Mun6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 286, "lead_no": 284, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0285", "customer": "KIM BUNKORNG", "province": "កំពង់ចាម", "url": "https://maps.google.com/maps?q=12.017509,105.070127&ll=12.017509,105.070127&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 287, "lead_no": 285},
{"id": "nphk-20261015-0286", "customer": "KIM CHHENGHONG", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/GuL48LH2WkUo3m4j6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 288, "lead_no": 286, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0287", "customer": "JUER JUER", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.519083,104.836966&ll=11.519083,104.836966&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 289, "lead_no": 287},
{"id": "nphk-20261015-0288", "customer": "RY បុរីសុខសាន្ដ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.504997,104.857324&ll=11.504997,104.857324&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 290, "lead_no": 288},
{"id": "nphk-20261015-0289", "customer": "SENGHEEANG SEAN", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/qboNuqdjp1Zf9Grd7?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 291, "lead_no": 289, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5448858,104.8328784&entry=gps&shh=CAE&lucs=,94297699,94275415,94284466,94231188,94280568,47071704,94218641,94282134,94286869&g_ep=CAISEjI2LjA0LjEuODU4MjY5MDE5MBgAINeCAypRLDk0Mjk3Njk5LDk0Mjc1NDE1LDk0Mjg0NDY2LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDk0Mjg2ODY5QgJLSA%3D%3D&skid=8f83239a-9366-4fa6-b224-99527d06491d&g_st=ic"},
{"id": "nphk-20261015-0290", "customer": "RAVY SEANG", "province": "កោះកុង", "url": "https://maps.app.goo.gl/DCdZUKs93Av5gLdu7?g_st=com.google.maps.preview.copy", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 292, "lead_no": 290, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0291", "customer": "ម៉ាក់ អូនយ៉ា", "province": "ឧត្តរមានជ័យ", "url": "https://maps.app.goo.gl/tjxyr5iLP2Ud8ksn7?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 293, "lead_no": 291, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0292", "customer": "សម្បត្ដិរក្សាតេលា", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 294, "lead_no": 292},
{"id": "nphk-20261015-0293", "customer": "BUN LEANG", "province": "កំពង់ចាម", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 295, "lead_no": 293},
{"id": "nphk-20261015-0294", "customer": "KIMSOUR SENG", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.520112,104.878930&ll=11.520112,104.878930&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 296, "lead_no": 294},
{"id": "nphk-20261015-0295", "customer": "J KEOV", "province": "កោះកុង", "url": "https://maps.google.com/maps?q=11.604918,102.979726&ll=11.604918,102.979726&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 297, "lead_no": 295},
{"id": "nphk-20261015-0296", "customer": "PHANNY TEAV", "province": "ស្វាយរៀង", "url": "https://maps.app.goo.gl/8Vo6NQX7awPH3HrCA?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 298, "lead_no": 296, "resolved_url": "https://www.google.com/maps/place/11.080524,105.806425/data=!4m6!3m5!1s0!7e2!8m2!3d11.0805235!4d105.80642499999999!17m2!4m1!1e3!18m1!1e1?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBjI2LjUuNBgAIPrsDSqcASw5NDI2NzcyNyw5NDI3NTQwNyw5NDI5MjE5NSw5NDI5OTUzMiwxMDA3OTY0OTIsMTAwNzk1NjI1LDk0Mjg0NDk5LDk0MjgwNTc2LDk0MjA3Mzk0LDk0MjA3NTA2LDk0MjA4NTA2LDk0MjE4NjUzLDk0MjI5ODM5LDk0Mjc1MTY4LDk0Mjc5NjE5LDk0MjYyNzMzLDEwMDc5MTQ4M0ICS0g%3D&skid=1551ff4d-2d96-44e5-b0c2-66d67a986cf0&g_st=atm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0297", "customer": "ចែ ហៀង", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=20.659324,-11.406255&ll=20.659324,-11.406255&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 299, "lead_no": 297},
{"id": "nphk-20261015-0298", "customer": "ចេ តា", "province": "កោះកុង", "url": "https://maps.google.com/maps?q=11.105152,103.798648&ll=11.105152,103.798648&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 300, "lead_no": 298},
{"id": "nphk-20261015-0299", "customer": "SOPHEAK LAY", "province": "កំពត", "url": "https://maps.app.goo.gl/s8AXyAGnRdN3JVMNA", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 301, "lead_no": 299, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0300", "customer": "CHANNA", "province": "បាត់ដំបង", "url": "https://maps.app.goo.gl/d667LdM8FEu6wXSJ8?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 302, "lead_no": 300, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0301", "customer": "AH RAVY", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.550760,104.861911&ll=11.550760,104.861911&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 303, "lead_no": 301},
{"id": "nphk-20261015-0302", "customer": "PHON SIHOUR", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.601656,104.906035&ll=11.601656,104.906035&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 304, "lead_no": 302},
{"id": "nphk-20261015-0303", "customer": "LEAKHENA CHEANG", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.606413,104.173470&ll=10.606413,104.173470&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 305, "lead_no": 303},
{"id": "nphk-20261015-0304", "customer": "CHENDA SREYLEAK", "province": "កែប", "url": "https://maps.google.com/maps?q=10.576536,104.390701&ll=10.576536,104.390701&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 306, "lead_no": 304},
{"id": "nphk-20261015-0305", "customer": "KHIEV MINEA", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.698302,103.813333&ll=10.698302,103.813333&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 307, "lead_no": 305},
{"id": "nphk-20261015-0306", "customer": "SIV YEE", "province": "កោះកុង", "url": "https://maps.app.goo.gl/66ReFFe3BGZY7vLn7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 308, "lead_no": 306, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0307", "customer": "CHHEM SOMALY", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.637327,103.538847&ll=10.637327,103.538847&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 309, "lead_no": 307},
{"id": "nphk-20261015-0308", "customer": "BilLY COFFEE", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.363576,105.004077&ll=11.363576,105.004077&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 310, "lead_no": 308},
{"id": "nphk-20261015-0309", "customer": "LY NA ​", "province": "កោះកុង", "url": "https://maps.google.com/maps?q=10.891951,103.407189&ll=10.891951,103.407189&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 311, "lead_no": 309},
{"id": "nphk-20261015-0310", "customer": "SUGEK CAFÉ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/5vLS1813D7UVns8a8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 312, "lead_no": 310, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0311", "customer": "EM LIMHEAR", "province": "ព្រៃវែង", "url": "https://maps.app.goo.gl/4C2JmkVAHYoXbf6R9?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 313, "lead_no": 311, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0312", "customer": "SREY NUCH", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.529477,104.944569&ll=11.529477,104.944569&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 314, "lead_no": 312},
{"id": "nphk-20261015-0313", "customer": "អេតឌី", "province": "ប៉ៃលិន", "url": "https://goo.gl/maps/d35bwfyeiP95zzfP6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 315, "lead_no": 313, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=13.085273,102.452879&entry=gps&g_ep=CAESBzI1LjQ5LjYYACDXggMqbCw5NDI2NzcyNyw5NDI3NTQwNyw5NDI5MjE5NSw5NDI5OTUzMiw5NDI4MDU3Niw5NDIwNzM5NCw5NDIwNzUwNiw5NDIwODUwNiw5NDIxODY1Myw5NDIyOTgzOSw5NDI3NTE2OCw5NDI3OTYxOUICS0g%3D&skid=d16e8e94-d412-4016-a924-aba3f504b785&shorturl=1"},
{"id": "nphk-20261015-0314", "customer": "សារិកា ​កាហ្វេ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 316, "lead_no": 314},
{"id": "nphk-20261015-0315", "customer": "EANG BORA", "province": "ស្វាយរៀង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 317, "lead_no": 315},
{"id": "nphk-20261015-0316", "customer": "BERRY", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.098559,103.203813&ll=13.098559,103.203813&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 318, "lead_no": 316},
{"id": "nphk-20261015-0317", "customer": "CREAM COFFEE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/t7yLYEAgMUgC3fpb6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 319, "lead_no": 317, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0318", "customer": "KRIS", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.544433,104.916156&ll=11.544433,104.916156&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 320, "lead_no": 318},
{"id": "nphk-20261015-0319", "customer": "HIM HOY", "province": "កំពត", "url": "https://maps.app.goo.gl/n7yV6HRA2Mt8RSj49?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 321, "lead_no": 319, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0320", "customer": "វិង ប៉ោយប៉ែត", "province": "ប៉ោយប៉ែត", "url": "https://maps.google.com/maps?q=13.645170,102.590579&ll=13.645170,102.590579&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 322, "lead_no": 320},
{"id": "nphk-20261015-0321", "customer": "NA NANA", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.088059,103.186267&ll=13.088059,103.186267&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 323, "lead_no": 321},
{"id": "nphk-20261015-0322", "customer": "THE FRESH", "province": "ភ្នំពេញ", "url": "https://goo.gl/maps/h4bWFjTLrXVaxGW99?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 324, "lead_no": 322, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.595177,104.914699&entry=gps&g_ep=CAESBzI1LjQ5LjYYACDXggMqiAEsOTQyNjc3MjcsOTQyNzU0MDcsOTQyOTIxOTUsOTQyOTk1MzIsOTQyODQ0OTMsOTQyODA1NzYsOTQyNjc3ODcsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksMTAwNzkxNDc5QgJLSA%3D%3D&skid=86adb0f2-2b2d-4258-bf94-ecf85a307270&shorturl=1"},
{"id": "nphk-20261015-0323", "customer": "SOPHEAP Y", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.555639,104.933216&ll=11.555639,104.933216&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 325, "lead_no": 323},
{"id": "nphk-20261015-0324", "customer": "SOENG LINGLING", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.524543,104.879560&ll=11.524543,104.879560&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 326, "lead_no": 324},
{"id": "nphk-20261015-0325", "customer": "SITHA ស្គន់ (ម្លប់ ស្បូវផូមិខ្ញុំ)", "province": "កំពង់ចាម", "url": "https://maps.app.goo.gl/G6sMbRUdK3RqcSev5?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 327, "lead_no": 325, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0326", "customer": "MOUYGUECH KONG", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/3zth8W81n7ibLsvDA?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 328, "lead_no": 326, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0327", "customer": "ជិក រម្យនី", "province": "ក្រចេះ", "url": "https://maps.app.goo.gl/Jz5bqU4e426dXwx9A?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 329, "lead_no": 327, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0328", "customer": "ហេង​ សៀវម៉ី", "province": "កំពង់ចាម", "url": "https://maps.google.com/maps?q=12.077188,105.143820&ll=12.077188,105.143820&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 330, "lead_no": 328},
{"id": "nphk-20261015-0329", "customer": "HENG SOTHON", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/JoMxExvSUFTHJ1Ua7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 331, "lead_no": 329, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=12.7010534,104.8920751&entry=gps&lucs=,94259549,94275411,94284457,94224825,94227247,94227248,94231188,94280568,47071704,47069508,94218641,94282134,94298698,94203019,47084304,94286869&g_ep=CAISEjI1LjQ3LjAuODMzNTQyOTMwMBgAINeCAyqQASw5NDI1OTU0OSw5NDI3NTQxMSw5NDI4NDQ1Nyw5NDIyNDgyNSw5NDIyNzI0Nyw5NDIyNzI0OCw5NDIzMTE4OCw5NDI4MDU2OCw0NzA3MTcwNCw0NzA2OTUwOCw5NDIxODY0MSw5NDI4MjEzNCw5NDI5ODY5OCw5NDIwMzAxOSw0NzA4NDMwNCw5NDI4Njg2OUICS0g%3D&skid=f2c81182-ad3e-45cb-877d-d344e52b7303&g_st=ifm"},
{"id": "nphk-20261015-0330", "customer": "ធារី", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/LC5jWSeSbQemzfCx9?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 332, "lead_no": 330, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0331", "customer": "KIM SUN", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.498970,104.884979&ll=11.498970,104.884979&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 333, "lead_no": 331},
{"id": "nphk-20261015-0332", "customer": "HOUTLYCHHENG", "province": "ព្រះសីហនុ", "url": "https://maps.app.goo.gl/gtxKrmoJ23f9JKWe7?g_st=com.google.maps.preview.copy", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 334, "lead_no": 332, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=10.6163593,103.5350768&entry=gps&lucs=,94242490,94224825,94227247,94227248,47071704,47069508,94218641,94203019,47084304,94208458,94208447&g_ep=CAISEjI0LjUwLjAuNzA0NDI3ODkxMBgAINeCAypjLDk0MjQyNDkwLDk0MjI0ODI1LDk0MjI3MjQ3LDk0MjI3MjQ4LDQ3MDcxNzA0LDQ3MDY5NTA4LDk0MjE4NjQxLDk0MjAzMDE5LDQ3MDg0MzA0LDk0MjA4NDU4LDk0MjA4NDQ3QgJLSA%3D%3D&g_st=com.google.maps.preview.copy"},
{"id": "nphk-20261015-0333", "customer": "TY OUN", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.628588,104.896136&ll=11.628588,104.896136&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 335, "lead_no": 333},
{"id": "nphk-20261015-0334", "customer": "ទឹម លីហេង", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/CoES6KY1LHoGqycg7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 336, "lead_no": 334, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0335", "customer": "THY THY PICK", "province": "សៀមរាប", "url": "https://maps.app.goo.gl/3gr36YQBwJ4TjB7x5?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 337, "lead_no": 335, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0336", "customer": "ណារិន ចន្ធធារ៉ា", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.614740,104.907892&ll=11.614740,104.907892&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 338, "lead_no": 336},
{"id": "nphk-20261015-0337", "customer": "លុយ ផារី", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.545738,104.894174&ll=11.545738,104.894174&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 339, "lead_no": 337},
{"id": "nphk-20261015-0338", "customer": "35 COFFEE 371", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.525707,104.888114&ll=11.525707,104.888114&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 340, "lead_no": 338},
{"id": "nphk-20261015-0339", "customer": "HOUN BUNNY", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.584458,103.747336&ll=10.584458,103.747336&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 341, "lead_no": 339},
{"id": "nphk-20261015-0340", "customer": "PHEM THIDA", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.570520,104.134605&ll=10.570520,104.134605&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 342, "lead_no": 340},
{"id": "nphk-20261015-0341", "customer": "HEANG SREY NUOCH", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.606081,104.929618&ll=11.606081,104.929618&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 343, "lead_no": 341},
{"id": "nphk-20261015-0342", "customer": "SOVAN PANHA", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.497437,104.863061&ll=11.497437,104.863061&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 344, "lead_no": 342},
{"id": "nphk-20261015-0343", "customer": "DANETTOUCH JINGJUNG", "province": "ក្រចេះ", "url": "https://maps.app.goo.gl/8DvaHEUaEJMBykuT8?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 345, "lead_no": 343, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0344", "customer": "AH HOUY", "province": "កំពង់ឆ្នាំង", "url": "https://maps.app.goo.gl/QrBtFHaXnWSxH7HKA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 346, "lead_no": 344, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0345", "customer": "CHIN HOK", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 347, "lead_no": 345},
{"id": "nphk-20261015-0346", "customer": "LEV SOKUN", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/SbfsM3LLsa6VYZmr8?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 348, "lead_no": 346, "resolved_url": "https://www.google.com/maps/place/11.769701,104.782439/data=!4m6!3m5!1s0!7e2!8m2!3d11.7697007!4d104.78243909999999!17m2!4m1!1e3!18m1!1e1?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI1LjQ3LjgYACD67A0qqwEsOTQyNjc3MjcsOTQyNzU0MDcsOTQyOTIxOTUsOTQyODQ0OTksOTQyMjMyOTksOTQyMTY0MTMsOTQyODA1NzYsOTQyMTI0OTYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTc1MjMsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksOTQyOTU1MDQsNDcwODQzOTMsOTQyMTMyMDBCAktI&skid=a9d890ed-23b3-49e8-8a2c-74f84e23fa6c&g_st=afm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0347", "customer": "ខ្មែរម៉ាត ស្គន់ កំពង់ចាម", "province": "កំពង់ចាម", "url": "https://maps.app.goo.gl/w9tdjbatw1kstuxd6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 349, "lead_no": 347, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=12.0544820,105.0642078&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=cd9bac3e-37ad-4220-8943-e5c3c221ff76&g_st=it"},
{"id": "nphk-20261015-0348", "customer": "QM SERVICES", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/tZ9ke66oeRGnqjBW6?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 350, "lead_no": 348, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5393579,104.9251836&entry=gps&lucs=,94286590,94275415,94284505,94224825,94227247,94227248,94231188,94280568,47071704,47069508,94218641,94282134,94292074,94203019,47084304,94286869&g_ep=CAISEjI1LjQ2LjEuODMwNDc0Nzc1MBgAINeCAyqQASw5NDI4NjU5MCw5NDI3NTQxNSw5NDI4NDUwNSw5NDIyNDgyNSw5NDIyNzI0Nyw5NDIyNzI0OCw5NDIzMTE4OCw5NDI4MDU2OCw0NzA3MTcwNCw0NzA2OTUwOCw5NDIxODY0MSw5NDI4MjEzNCw5NDI5MjA3NCw5NDIwMzAxOSw0NzA4NDMwNCw5NDI4Njg2OUICS0g%3D&skid=6154530c-e97f-4076-b720-bda10f968843&g_st=ipc"},
{"id": "nphk-20261015-0349", "customer": "PHEA SREYMOM", "province": "កំពង់ឆ្នាំង", "url": "https://maps.google.com/maps?q=11.767792,104.667610&ll=11.767792,104.667610&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 351, "lead_no": 349},
{"id": "nphk-20261015-0350", "customer": "STUDY CAFÉ", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/hn1oEPzpucdmk9YM9?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 352, "lead_no": 350, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0351", "customer": "HONG HENG", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/ZnjDfoVdPbWm9ecM6?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 353, "lead_no": 351, "resolved_url": "https://www.google.com/maps/place/Koh+Teav+Market/data=!3m5!1e2!3m3!1sCIHM0ogKEICAgIDEwomVLw!2e10!6shttps:%2F%2Fgz0.googleusercontent.com%2Fgrass-cs%2FACke6TiWKsnAK4_7xB7lJbj8cqF-2lU1yDs3VBFIgITaH9X5aY0VSdCFfYfUQa47fjoauzgvil9_kUaJIQiMveXpjLsUGPu6Zq2YgiDL499V2jJtEWfcl3eiODq6KlK79se6w5AWPKj-%3Dw800-h450-k-no!4m10!3m9!1s0x310bd5beffdf71c5:0xfca601ddbcf916cb!8m2!3d11.0262842!4d105.05877059999999!10e5!13m2!1skoh+tao!2e5!16s%2Fg%2F11cnc58mlz?g_ep=CAESBzI1LjQ3LjgYACDmiAsqqwEsOTQyNjc3MjcsOTQyNzU0MDcsOTQyOTIxOTUsOTQyOTk1MzIsOTQyODQ0NjMsOTQyMjMyOTksOTQyMTY0MTMsOTQyODA1NzYsOTQyMTI0OTYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTc1MjMsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksNDcwODQzOTMsOTQyMTMyMDBCAktI&skid=99dbd6f7-709c-492b-9c0c-9af6f6ccde9d&g_st=afm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0352", "customer": "ហាប់ គឹមហ៊រ", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.362298,103.876997&ll=13.362298,103.876997&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 354, "lead_no": 352},
{"id": "nphk-20261015-0353", "customer": "HEANG CHANDA", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.499135,104.665048&ll=11.499135,104.665048&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 355, "lead_no": 353},
{"id": "nphk-20261015-0354", "customer": "SOPHORS VETH", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.587520,104.813162&ll=11.587520,104.813162&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 356, "lead_no": 354},
{"id": "nphk-20261015-0355", "customer": "SUN POVNEARY", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.576364,104.841325&ll=11.576364,104.841325&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 357, "lead_no": 355},
{"id": "nphk-20261015-0356", "customer": "PANHCHAKRITHD", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.560271,104.929453&ll=11.560271,104.929453&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 358, "lead_no": 356},
{"id": "nphk-20261015-0357", "customer": "HOR SAMBATH", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/65tyyWE8XXphQzCx9?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 359, "lead_no": 357, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0358", "customer": "CHANTHA", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.445640,104.580222&ll=11.445640,104.580222&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 360, "lead_no": 358},
{"id": "nphk-20261015-0359", "customer": "BUN LEANG", "province": "កំពង់ចាម", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 361, "lead_no": 359},
{"id": "nphk-20261015-0360", "customer": "CHANRA CHOUN", "province": "ប៉ោយប៉ែត", "url": "https://maps.app.goo.gl/FSRuZJnuePNkqrxN9?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 362, "lead_no": 360, "resolved_url": "https://www.google.com/maps/place/13.668564,102.583785/data=!4m6!3m5!1s0!7e2!8m2!3d13.668563899999999!4d102.5837851?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI1LjQ2LjUYACD67A0qogEsOTQyNjc3MjcsOTQyNzU0MDMsOTQyOTIxOTUsOTQyODQ0OTMsOTQyMjMyOTksOTQyMTY0MTMsOTQyODA1NzYsOTQyMTI0OTYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTc1MjMsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksNDcwODQzOTMsOTQyMTMyMDBCAktI&skid=a09d04b1-8306-40b5-9ecd-a8f6cf4e943c&g_st=atm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0361", "customer": "ម៉ាក់ លីស៊ីង", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.512440,104.462513&ll=10.512440,104.462513&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 363, "lead_no": 361},
{"id": "nphk-20261015-0362", "customer": "LY SAUREN", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.459375,104.936814&ll=11.459375,104.936814&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 364, "lead_no": 362},
{"id": "nphk-20261015-0363", "customer": "SENG KAVEN", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/VMsWrCoYPKG4Xway7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 365, "lead_no": 363, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0364", "customer": "BUN LEANG", "province": "កំពង់ចាម", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 366, "lead_no": 364},
{"id": "nphk-20261015-0365", "customer": "អ៊ុត សេរី", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.477924,104.951568&ll=11.477924,104.951568&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 367, "lead_no": 365},
{"id": "nphk-20261015-0366", "customer": "NA RAKSMEY", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=10.576389,103.565223&ll=10.576389,103.565223&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 368, "lead_no": 366},
{"id": "nphk-20261015-0367", "customer": "TAN MOUY HENG", "province": "តាកែវ", "url": "https://maps.app.goo.gl/cidJcbURLsUfJGza8?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 369, "lead_no": 367, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=10.9888502,104.7779068&entry=gps&lucs=,94284463,94224825,94227247,94227248,94231188,47071704,47069508,94218641,94282134,94203019,47084304&g_ep=CAISEjI1LjE5LjEuNzU0OTg3NTEyMBgAIIgnKmMsOTQyODQ0NjMsOTQyMjQ4MjUsOTQyMjcyNDcsOTQyMjcyNDgsOTQyMzExODgsNDcwNzE3MDQsNDcwNjk1MDgsOTQyMTg2NDEsOTQyODIxMzQsOTQyMDMwMTksNDcwODQzMDRCAktI&skid=14cb7e8d-3bd1-4492-9b7b-0d1ba27ad4a3&g_st=ifm"},
{"id": "nphk-20261015-0368", "customer": "RAK", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.650500,104.914458&ll=11.650500,104.914458&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 370, "lead_no": 368},
{"id": "nphk-20261015-0369", "customer": "LEAKHENA", "province": "បន្ទាយមានជ័យ", "url": "https://maps.app.goo.gl/N8wYcBP2RZJ6eBXV7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 371, "lead_no": 369, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0370", "customer": "មរតក", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=10.923831,104.612717&ll=10.923831,104.612717&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 372, "lead_no": 370},
{"id": "nphk-20261015-0371", "customer": "CHANRA CHOUN", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.695593,102.652428&ll=13.695593,102.652428&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 373, "lead_no": 371},
{"id": "nphk-20261015-0372", "customer": "CHANRA CHOUN", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.695593,102.652428&ll=13.695593,102.652428&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 374, "lead_no": 372},
{"id": "nphk-20261015-0373", "customer": "CHANRA CHOUN", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.695593,102.652428&ll=13.695593,102.652428&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 375, "lead_no": 373},
{"id": "nphk-20261015-0374", "customer": "OUN VY", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/fUo56rTG1ejgjYPv7?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 376, "lead_no": 374, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0375", "customer": "NA RY", "province": "ព្រះសីហនុ", "url": "https://maps.app.goo.gl/Br5PJpNPS9zyHESs6?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 377, "lead_no": 375, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0376", "customer": "ខ្មែរ ម៉ាត", "province": "រតនគិរី", "url": "https://maps.google.com/maps?q=13.739884,106.982289&ll=13.739884,106.982289&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 378, "lead_no": 376},
{"id": "nphk-20261015-0377", "customer": "YOY COFFEE", "province": "ឧត្តរមានជ័យ", "url": "https://maps.app.goo.gl/AKTGmd1rft2Skg6s5?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 379, "lead_no": 377, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0378", "customer": "ម៉ៃ", "province": "ប៉ោយប៉ែត", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 380, "lead_no": 378},
{"id": "nphk-20261015-0379", "customer": "VICHARA", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.458049,104.923536&ll=11.458049,104.923536&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 381, "lead_no": 379},
{"id": "nphk-20261015-0380", "customer": "ចន្នី", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 382, "lead_no": 380},
{"id": "nphk-20261015-0381", "customer": "LY THAIING", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.576684,104.925812&ll=11.576684,104.925812&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 383, "lead_no": 381},
{"id": "nphk-20261015-0382", "customer": "JOHN MENGHAK", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.587049,104.938251&ll=11.587049,104.938251&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 384, "lead_no": 382},
{"id": "nphk-20261015-0383", "customer": "NOK NOI CAFÉ", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/yQoqyywPPjpTckzU7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 385, "lead_no": 383, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.4640374,104.9582579&entry=gps&lucs=,94284508,94224825,94227247,94227248,94231188,94280568,47071704,47069508,94218641,94282134,94203019,47084304,94286869&g_ep=CAISEjI1LjM4LjAuODA3MzYwMDM5MBgAINeCAyp1LDk0Mjg0NTA4LDk0MjI0ODI1LDk0MjI3MjQ3LDk0MjI3MjQ4LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDQ3MDY5NTA4LDk0MjE4NjQxLDk0MjgyMTM0LDk0MjAzMDE5LDQ3MDg0MzA0LDk0Mjg2ODY5QgJLSA%3D%3D&skid=783090d8-0306-4150-bb67-a9e954e968ea&g_st=it"},
{"id": "nphk-20261015-0384", "customer": "MANETH", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/7uELtHj4sKsZ3TKfA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 386, "lead_no": 384, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0385", "customer": "សុវី", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.359494,105.014323&ll=11.359494,105.014323&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 387, "lead_no": 385},
{"id": "nphk-20261015-0386", "customer": "LEAK SEY", "province": "ត្បូងឃ្មុំ", "url": "https://maps.google.com/maps?q=12.096334,105.549159&ll=12.096334,105.549159&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 388, "lead_no": 386},
{"id": "nphk-20261015-0387", "customer": "DOWNTOWN", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.484951,104.715381&ll=11.484951,104.715381&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 389, "lead_no": 387},
{"id": "nphk-20261015-0388", "customer": "DOWNTOWN", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.484951,104.715381&ll=11.484951,104.715381&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 390, "lead_no": 388},
{"id": "nphk-20261015-0389", "customer": "SREY POV", "province": "ស្វាយរៀង", "url": "https://maps.google.com/maps?q=11.426621,105.803057&ll=11.426621,105.803057&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 391, "lead_no": 389},
{"id": "nphk-20261015-0390", "customer": "VANNIN OAK", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.564837,104.828407&ll=11.564837,104.828407&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 392, "lead_no": 390},
{"id": "nphk-20261015-0391", "customer": "RAKSMEY NANO", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.525483,104.936747&ll=11.525483,104.936747&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 393, "lead_no": 391},
{"id": "nphk-20261015-0392", "customer": "ស្រៀន ស្រីកា", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/a8qDD7C2sZvMW12a6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 394, "lead_no": 392, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5076677,104.9132089&entry=gps&lucs=,94284460,94224825,94227247,94227248,94231188,94280568,47071704,47069508,94218641,94282134,94203019,47084304&g_ep=CAISEjI1LjM5LjMuODEwMTI3MDQ4MBgAINeCAypsLDk0Mjg0NDYwLDk0MjI0ODI1LDk0MjI3MjQ3LDk0MjI3MjQ4LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDQ3MDY5NTA4LDk0MjE4NjQxLDk0MjgyMTM0LDk0MjAzMDE5LDQ3MDg0MzA0QgJLSA%3D%3D&skid=b4a8b714-cc7a-44a4-a270-b99ab8ed2dfc&g_st=ic"},
{"id": "nphk-20261015-0393", "customer": "KHAM CHISOPHEAK", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/hDLiqZzgUCS8wK9g6?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 395, "lead_no": 393, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5634999,104.9007497&entry=gps&lucs=,94284454,94224825,94227247,94227248,94231188,94280564,47071704,47069508,94273883,94218641,94282134,94203019,47084304&g_ep=CAISEjI1LjQwLjIuODEyNjUyMzQwMBgAINeCAyp1LDk0Mjg0NDU0LDk0MjI0ODI1LDk0MjI3MjQ3LDk0MjI3MjQ4LDk0MjMxMTg4LDk0MjgwNTY0LDQ3MDcxNzA0LDQ3MDY5NTA4LDk0MjczODgzLDk0MjE4NjQxLDk0MjgyMTM0LDk0MjAzMDE5LDQ3MDg0MzA0QgJLSA%3D%3D&skid=b8f87cb8-80e3-493b-a2e8-a48c12b9b88e&g_st=ipc"},
{"id": "nphk-20261015-0394", "customer": "សារី មង្គល", "province": "តាកែវ", "url": "https://maps.app.goo.gl/1Eu5TP3sqB9bsVWc9?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 396, "lead_no": 394, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0395", "customer": "CHANKHOEUN", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.552884,104.861309&ll=11.552884,104.861309&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 397, "lead_no": 395},
{"id": "nphk-20261015-0396", "customer": "PISETH POV", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.536635,104.909500&ll=11.536635,104.909500&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 398, "lead_no": 396},
{"id": "nphk-20261015-0397", "customer": "LIN MET", "province": "ប៉ោយប៉ែត", "url": "https://maps.google.com/maps?q=13.677613,102.565034&ll=13.677613,102.565034&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 399, "lead_no": 397},
{"id": "nphk-20261015-0398", "customer": "AUREA STELLA COFFEE", "province": "ប៉ោយប៉ែត", "url": "https://maps.google.com/maps?q=13.680484,102.563680&ll=13.680484,102.563680&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 400, "lead_no": 398},
{"id": "nphk-20261015-0399", "customer": "SORA VY", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/ZKX8ohRDVx4YutHs6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 401, "lead_no": 399, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0400", "customer": "AH POV HD", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/H63XSCBJDswwVSWk8?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 402, "lead_no": 400, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0401", "customer": "ស្រីឡៃ សម្រស់ធម្មជាតិ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/q5wNQTnsiFKr1xL57?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 403, "lead_no": 401, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0402", "customer": "ស្រី នាត", "province": "ត្បូងឃ្មុំ", "url": "https://maps.google.com/maps?q=12.264966,105.561502&ll=12.264966,105.561502&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 404, "lead_no": 402},
{"id": "nphk-20261015-0403", "customer": "LAY BUNNAWATH", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.355995,103.875112&ll=13.355995,103.875112&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 405, "lead_no": 403},
{"id": "nphk-20261015-0404", "customer": "MEN CHAMNAN", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.582287,104.890793&ll=11.582287,104.890793&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 406, "lead_no": 404},
{"id": "nphk-20261015-0405", "customer": "CHANKHOEUN", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.550462,104.883266&ll=11.550462,104.883266&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 407, "lead_no": 405},
{"id": "nphk-20261015-0406", "customer": "HOUR KUNTHEA", "province": "ស្វាយរៀង", "url": "https://maps.app.goo.gl/V8dhKE5UpPYHzN3b6?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 408, "lead_no": 406, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0407", "customer": "BUN LEANG", "province": "កំពង់ចាម", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 409, "lead_no": 407},
{"id": "nphk-20261015-0408", "customer": "KHUN BELLA", "province": "បន្ទាយមានជ័យ", "url": "https://maps.app.goo.gl/MroQLB66pkYAyviJ6?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 410, "lead_no": 408, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=14.4165058,103.6951504&entry=gps&lucs=,94284499,94224825,94227247,94227248,94231188,47071704,47069508,94218641,94282134,94203019,47084304&g_ep=CAISEjI1LjIyLjAuNzYzNTE5NzAyMBgAINeCAypjLDk0Mjg0NDk5LDk0MjI0ODI1LDk0MjI3MjQ3LDk0MjI3MjQ4LDk0MjMxMTg4LDQ3MDcxNzA0LDQ3MDY5NTA4LDk0MjE4NjQxLDk0MjgyMTM0LDk0MjAzMDE5LDQ3MDg0MzA0QgJLSA%3D%3D&skid=36a61137-5d5c-4aa4-b98b-19d86423b168&g_st=ifm"},
{"id": "nphk-20261015-0409", "customer": "មករា​", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.407472,104.865920&ll=11.407472,104.865920&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 411, "lead_no": 409},
{"id": "nphk-20261015-0410", "customer": "FLOWER", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.580222,104.900801&ll=11.580222,104.900801&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 412, "lead_no": 410},
{"id": "nphk-20261015-0411", "customer": "សោ ភា", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/74oa632xYXMNaPCJ9?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 413, "lead_no": 411, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5748733,104.8897452&entry=gps&lucs=,94284463,94224825,94227247,94227248,94231188,94280568,47071704,47069508,94218641,94282134,94203019,47084304&g_ep=CAISEjI1LjM5LjIuODEwMTI3MDQ4MBgAINeCAypsLDk0Mjg0NDYzLDk0MjI0ODI1LDk0MjI3MjQ3LDk0MjI3MjQ4LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDQ3MDY5NTA4LDk0MjE4NjQxLDk0MjgyMTM0LDk0MjAzMDE5LDQ3MDg0MzA0QgJLSA%3D%3D&skid=1446eda7-1879-4560-84a5-c970123e8eaa&g_st=ifm"},
{"id": "nphk-20261015-0412", "customer": "ឡឹង បញ្ញា", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.510606,104.746121&ll=11.510606,104.746121&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 414, "lead_no": 412},
{"id": "nphk-20261015-0413", "customer": "ឈាង លីដា", "province": "សៀមរាប", "url": "https://maps.app.goo.gl/JjSCJwtD5Q7CVVSS8?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 415, "lead_no": 413, "resolved_url": "https://www.google.com/maps/place/13.287168,103.820569/data=!4m6!3m5!1s0!7e2!8m2!3d13.287168399999999!4d103.82056879999999?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI1LjE5LjYYACD4wA0qhwEsOTQyNjc3MjcsOTQyODQ0OTAsOTQyMjMyOTksOTQyMTY0MTMsOTQyODA1NzYsOTQyMTI0OTYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTc1MjMsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsNDcwODQzOTMsOTQyMTMyMDBCAktI&skid=83d207e7-267d-4564-8f1e-3a060c83d526&g_st=afm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0414", "customer": "បាយស្រូប", "province": "កោះពេជ្រ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 416, "lead_no": 414},
{"id": "nphk-20261015-0415", "customer": "SAM MST", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.608234,103.537815&ll=10.608234,103.537815&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 417, "lead_no": 415},
{"id": "nphk-20261015-0416", "customer": "PANHCHAKRITHD", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.564029,104.923772&ll=11.564029,104.923772&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 418, "lead_no": 416},
{"id": "nphk-20261015-0417", "customer": "VOLEAK TAING", "province": "សៀមរាប", "url": "https://maps.app.goo.gl/NsG7MaRtvwoNKSUM9?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 419, "lead_no": 417, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0418", "customer": "AH NA", "province": "ត្បូងឃ្មុំ", "url": "https://maps.google.com/maps?q=11.936937,105.570604&ll=11.936937,105.570604&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 420, "lead_no": 418},
{"id": "nphk-20261015-0419", "customer": "CHUU MI", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.629696,104.877727&ll=11.629696,104.877727&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 421, "lead_no": 419},
{"id": "nphk-20261015-0420", "customer": "KIM CHHORN CAFÉ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/NfPfxcR3yFgu6pcW6?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 422, "lead_no": 420, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0421", "customer": "មុំ ចន្ទ័រតនា", "province": "តាកែវ", "url": "https://maps.app.goo.gl/8162EMUAySg6SKnH7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 423, "lead_no": 421, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=10.9794480,104.7747130&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=3e61c282-c5af-4c39-8fba-f8e76d626bf3&g_st=it"},
{"id": "nphk-20261015-0422", "customer": "VIE VIE", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/32Cutrb1Mpsrgaba9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 424, "lead_no": 422, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.4795560,104.9482220&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=428b0758-077b-41a5-871f-86e9ed46849b&g_st=it"},
{"id": "nphk-20261015-0423", "customer": "ឈាន រស្មី", "province": "មណ្ឌលគិរី", "url": "https://maps.google.com/maps?q=12.441636,107.198472&ll=12.441636,107.198472&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 425, "lead_no": 423},
{"id": "nphk-20261015-0424", "customer": "HENG THIDA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/YfAcFVppjHudWCqW8?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 426, "lead_no": 424, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0425", "customer": "SOPHAL FREEMAN", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/ii7EG7PooU7u7h3YA?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 427, "lead_no": 425, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0426", "customer": "RA CHANBORMEY", "province": "សៀមរាប", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 428, "lead_no": 426},
{"id": "nphk-20261015-0427", "customer": "CHENG HOUR", "province": "កំពង់ធំ", "url": "https://maps.google.com/maps?q=12.733231,104.896563&ll=12.733231,104.896563&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 429, "lead_no": 427},
{"id": "nphk-20261015-0428", "customer": "LIDA JOLIE MART", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.462188,104.949840&ll=11.462188,104.949840&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 430, "lead_no": 428},
{"id": "nphk-20261015-0429", "customer": "SROS SAING", "province": "កំពត", "url": "https://maps.app.goo.gl/n9crDHY5d9VG5CdR6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 431, "lead_no": 429, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0430", "customer": "LIM LONG", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Bva2ppmK7HjW1k7C7?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 432, "lead_no": 430, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0431", "customer": "ម៉ាក់ណា", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 433, "lead_no": 431},
{"id": "nphk-20261015-0432", "customer": "HOUY NITA", "province": "តាកែវ", "url": "https://maps.app.goo.gl/Vo7WPXKe8BoBUJcg6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 434, "lead_no": 432, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0433", "customer": "HENG SO PHEAP", "province": "កំពត", "url": "https://maps.app.goo.gl/N7jDeTmWvZmVWBcg6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 435, "lead_no": 433, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0434", "customer": "TELA RITHY", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.591583,104.894529&ll=11.591583,104.894529&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 436, "lead_no": 434},
{"id": "nphk-20261015-0435", "customer": "SUGEK CHIN", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/y6AXgKdAR3b7xWyq7?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 437, "lead_no": 435, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5982007,104.8857243&entry=gps&lucs=,94284481,94224825,94227247,94227248,94231188,47071704,47069508,94218641,94282134,94203019,47084304,94286863&g_ep=CAISEjI1LjM1LjAuNzk5MDg4MzU1MBgAIIgnKmwsOTQyODQ0ODEsOTQyMjQ4MjUsOTQyMjcyNDcsOTQyMjcyNDgsOTQyMzExODgsNDcwNzE3MDQsNDcwNjk1MDgsOTQyMTg2NDEsOTQyODIxMzQsOTQyMDMwMTksNDcwODQzMDQsOTQyODY4NjNCAktI&skid=a6810765-363b-48c9-a215-354a5241935b&g_st=ipc"},
{"id": "nphk-20261015-0436", "customer": "SANG SOPHARA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Kszr2R1CH15SpFAH7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 438, "lead_no": 436, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5386165,104.8202566&entry=gps&lucs=,94284484,94224825,94227247,94227248,94231188,47071704,47069508,94218641,94282134,94203019,47084304&g_ep=CAISEjI1LjMxLjAuNzg4MTIyNzc1MBgAINeCAypjLDk0Mjg0NDg0LDk0MjI0ODI1LDk0MjI3MjQ3LDk0MjI3MjQ4LDk0MjMxMTg4LDQ3MDcxNzA0LDQ3MDY5NTA4LDk0MjE4NjQxLDk0MjgyMTM0LDk0MjAzMDE5LDQ3MDg0MzA0QgJLSA%3D%3D&skid=43d64e84-4808-4999-a575-04cda3756276&g_st=ifm"},
{"id": "nphk-20261015-0437", "customer": "SVAY LY CHANTHA", "province": "សៀមរាប", "url": "https://maps.app.goo.gl/8GXmhCq4FS6eUVbW8", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 439, "lead_no": 437, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0438", "customer": "THEA RA", "province": "សៀមរាប", "url": "https://www.google.com/maps/place//@11.5913471,104.8943921,18.5z/data=!4m6!1m5!3m4!2zMTHCsDM1JzI5LjciTiAxMDTCsDUzJzQwLjMiRQ!8m2!3d11.591583!4d104.894529!5m1!1e1?entry=ttu&g_ep=EgoyMDI1MDkwMy4wIKXMDSoASAFQAw%3D%3D", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 440, "lead_no": 438},
{"id": "nphk-20261015-0439", "customer": "LEANG HUN", "province": "ស្វាយរៀង", "url": "https://maps.google.com/maps?q=11.081084,105.847270&ll=11.081084,105.847270&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 441, "lead_no": 439},
{"id": "nphk-20261015-0440", "customer": "ចែ ណែត", "province": "ប៉ោយប៉ែត", "url": "https://maps.app.goo.gl/sW6et5CiYK854gqT6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 442, "lead_no": 440, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=13.6717180,102.5675520&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=2f9c0926-4030-4131-9505-b1a573f3d2d7&g_st=it"},
{"id": "nphk-20261015-0441", "customer": "TIK TOK CAFÉ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/JPhYwtCPFv6zQfpN6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 443, "lead_no": 441, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0442", "customer": "ចន្ថា ប៉ុណ្ណាការ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 444, "lead_no": 442},
{"id": "nphk-20261015-0443", "customer": "SREY KHOUCH", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 445, "lead_no": 443},
{"id": "nphk-20261015-0444", "customer": "MORNIKA VAYOUK", "province": "ពោធិ៍សាត់", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 446, "lead_no": 444},
{"id": "nphk-20261015-0445", "customer": "OUNKHIM LOVE", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/Yg69EwJQAeJnNsqU7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 447, "lead_no": 445, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0446", "customer": "ម៉ុង បរមី", "province": "", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 448, "lead_no": 446},
{"id": "nphk-20261015-0447", "customer": "TON CHANNY", "province": "កោះកុង", "url": "https://maps.app.goo.gl/3pyXDbYCkTiyZCyGA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 449, "lead_no": 447, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0448", "customer": "ROTH NARAK", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 450, "lead_no": 448},
{"id": "nphk-20261015-0449", "customer": "NA NA", "province": "ស្វាយរៀង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 451, "lead_no": 449},
{"id": "nphk-20261015-0450", "customer": "CHHEA PISEY", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 452, "lead_no": 450},
{"id": "nphk-20261015-0451", "customer": "CHANRA CHOUN", "province": "បាត់ដំបង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 453, "lead_no": 451},
{"id": "nphk-20261015-0452", "customer": "ម៉ុង បរមី", "province": "", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 454, "lead_no": 452},
{"id": "nphk-20261015-0453", "customer": "សួរ ឧស្សាហ៍", "province": "បន្ទាយមានជ័យ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 455, "lead_no": 453},
{"id": "nphk-20261015-0454", "customer": "BARANG KTH", "province": "កំពត", "url": "https://maps.app.goo.gl/jZfSv5DgZDP97hTm9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 456, "lead_no": 454, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0455", "customer": "THIDA CHHOUN", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 457, "lead_no": 455},
{"id": "nphk-20261015-0456", "customer": "LEONG KUNTHEA", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.183393,104.780581&ll=11.183393,104.780581&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 458, "lead_no": 456},
{"id": "nphk-20261015-0457", "customer": "RASY HR", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/16niAUFaiU2GdJYN7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 459, "lead_no": 457, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.4439860,104.8838930&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b9120834-9311-4f8c-8026-86d7a99b7e79&g_st=it"},
{"id": "nphk-20261015-0458", "customer": "ROS SARADANY", "province": "ឧត្តរមានជ័យ", "url": "https://maps.app.goo.gl/3LeWNWXj2c6pMKmS7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 460, "lead_no": 458, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0459", "customer": "CALTEX", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 461, "lead_no": 459},
{"id": "nphk-20261015-0460", "customer": "អ៊ុក កញ្ញា", "province": "កោះកុង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 462, "lead_no": 460},
{"id": "nphk-20261015-0461", "customer": "MS NA", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 463, "lead_no": 461},
{"id": "nphk-20261015-0462", "customer": "សៀក នី", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/u6qQkKy9wUf2FS1L9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 464, "lead_no": 462, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.2110680,104.5835330&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b8c863db-6d37-4ffb-a264-a75298a4b2ec&g_st=it"},
{"id": "nphk-20261015-0463", "customer": "ROTHA សំបុកត្រចៀកកាំ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 465, "lead_no": 463},
{"id": "nphk-20261015-0464", "customer": "DARA PICH", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=13.645170,102.590579&ll=13.645170,102.590579&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 466, "lead_no": 464},
{"id": "nphk-20261015-0465", "customer": "អ៊ុក មឿន", "province": "ព្រះសីហនុ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 467, "lead_no": 465},
{"id": "nphk-20261015-0466", "customer": "BE STRONG", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 468, "lead_no": 466},
{"id": "nphk-20261015-0467", "customer": "BELLA SMITT", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/SgaLfpMkbU5goa3KA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 469, "lead_no": 467, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0468", "customer": "អ៊ីង អ៊ីង", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 470, "lead_no": 468},
{"id": "nphk-20261015-0469", "customer": "VOREAKTEY", "province": "ប៉ោយប៉ែត", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 471, "lead_no": 469},
{"id": "nphk-20261015-0470", "customer": "ចាន់ ថន", "province": "ព្រៃវែង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 472, "lead_no": 470},
{"id": "nphk-20261015-0471", "customer": "ម៉ាក់អូន ឈីញ", "province": "ព្រះវិហារ", "url": "https://maps.app.goo.gl/LGwFe8YMrQisKQLC9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 473, "lead_no": 471, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0472", "customer": "PISEY CHHEA", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 474, "lead_no": 472},
{"id": "nphk-20261015-0473", "customer": "អា នី", "province": "ត្បូងឃ្មុំ", "url": "https://maps.app.goo.gl/WVmaXBosd8HPrjut8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 475, "lead_no": 473, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.7610000,106.3343890&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=d4ebf53f-e308-4cd3-9169-e6b6fcddf316&g_st=it"},
{"id": "nphk-20261015-0474", "customer": "SN79 MART & TOYS", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 476, "lead_no": 474},
{"id": "nphk-20261015-0475", "customer": "SREYPICH THAI", "province": "ត្បូងឃ្មុំ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 477, "lead_no": 475},
{"id": "nphk-20261015-0476", "customer": "ចិ ភា លក់គ្រឿងក្រអូប ក្នុងផ្សារកំពង់ត្រាច", "province": "កំពត", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 478, "lead_no": 476},
{"id": "nphk-20261015-0477", "customer": "CHEA MOLIVANN", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/9xqAkdZRKyogKbQ57?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 479, "lead_no": 477, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0478", "customer": "កង់ទីនសាលា BRIGHT LINE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Hq9d89aF7kn1356CA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 480, "lead_no": 478, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0479", "customer": "JEE DA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/VRHK5ono4srsGgaC9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 481, "lead_no": 479, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5121940,104.9300002&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b2d141e1-bb9b-46eb-8b85-5e66cd816145&g_st=it"},
{"id": "nphk-20261015-0480", "customer": "MALAY MALAY", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/AEgveS7ThaQzveEY9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 482, "lead_no": 480, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=12.8717070,105.0431690&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=78cf2575-4095-49d0-8d80-61fadb58adb0&g_st=it"},
{"id": "nphk-20261015-0481", "customer": "PHAL LA", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 483, "lead_no": 481},
{"id": "nphk-20261015-0482", "customer": "OUK CHENDA", "province": "ព្រះសីហនុ", "url": "https://maps.app.goo.gl/FYnAD4G6vc94jEAA8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 484, "lead_no": 482, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0483", "customer": "AM SANG HOUY", "province": "ពោធិ៍សាត់", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 485, "lead_no": 483},
{"id": "nphk-20261015-0484", "customer": "RAINBO", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/HizthsHTMDdR15N8A?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 486, "lead_no": 484, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0485", "customer": "MASY MASY", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 487, "lead_no": 485},
{"id": "nphk-20261015-0486", "customer": "MITHONA PEN", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 488, "lead_no": 486},
{"id": "nphk-20261015-0487", "customer": "AH TOCH KH", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 489, "lead_no": 487},
{"id": "nphk-20261015-0488", "customer": "MAK VISAL", "province": "ពោធិ៍សាត់", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 490, "lead_no": 488},
{"id": "nphk-20261015-0489", "customer": "MO LIKA", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 491, "lead_no": 489},
{"id": "nphk-20261015-0490", "customer": "PHAI VITA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/pHMXdVTRx5neeMkNA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 492, "lead_no": 490, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0491", "customer": "CHANRA CHOUN", "province": "បាត់ដំបង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 493, "lead_no": 491},
{"id": "nphk-20261015-0492", "customer": "CHANRA CHOUN", "province": "បាត់ដំបង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 494, "lead_no": 492},
{"id": "nphk-20261015-0493", "customer": "CHANRA CHOUN", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 495, "lead_no": 493},
{"id": "nphk-20261015-0494", "customer": "LY HONG", "province": "បាត់ដំបង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 496, "lead_no": 494},
{"id": "nphk-20261015-0495", "customer": "FAML NU", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 497, "lead_no": 495},
{"id": "nphk-20261015-0496", "customer": "SREYDET KHOUN", "province": "សៀមរាប", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 498, "lead_no": 496},
{"id": "nphk-20261015-0497", "customer": "SOULINH HEANG", "province": "ព្រះវិហារ", "url": "https://maps.app.goo.gl/Jks3wPbS1y16y6pw6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 499, "lead_no": 497, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=13.3046450,105.0021700&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=5860543d-97b8-4eb4-9798-b5c31595bc40&g_st=it"},
{"id": "nphk-20261015-0498", "customer": "ING MUOYSIM", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/wY6HYxzDmgRSDMb96?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 500, "lead_no": 498, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0499", "customer": "X CAFÉ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/e5YhmG8cefwxksZK9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 501, "lead_no": 499, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0500", "customer": "PHOK SOMALY", "province": "តាកែវ", "url": "https://maps.app.goo.gl/4ojBjtjKafwmkGVLA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 502, "lead_no": 500, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.3848580,104.8635680&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=77683e8e-d5b1-453f-b28e-32378c4496ec&g_st=it"},
{"id": "nphk-20261015-0501", "customer": "NOREAK 168 SHOP", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/89ph66quWaDvfXUb7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 503, "lead_no": 501, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5616650,104.8413820&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=7d6bded9-a600-44d4-b80d-2948ad7bedd1&g_st=it"},
{"id": "nphk-20261015-0502", "customer": "MOUYCHHENG GOV", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.684197,104.700838&ll=11.684197,104.700838&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 504, "lead_no": 502},
{"id": "nphk-20261015-0503", "customer": "ស៊ុន រតនៈ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/J7AeM9SRk25FKwiQA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 505, "lead_no": 503, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0504", "customer": "LY SOK IM", "province": "ព្រះវិហារ", "url": "https://maps.google.com/maps?q=13.304640,105.002195&ll=13.304640,105.002195&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 506, "lead_no": 504},
{"id": "nphk-20261015-0505", "customer": "TANGIM COSMETIC", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/KATyHNN34rXurtzA6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 507, "lead_no": 505, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.2116670,104.5766390&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=49e6635d-f657-4dc2-9ed9-edc792adf148&g_st=it"},
{"id": "nphk-20261015-0506", "customer": "SOKHEA NEANG", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/F52hXU154g9nnRMb7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 508, "lead_no": 506, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5970670,104.8025270&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=c7e016c3-689b-4b2f-b81d-50cad96662f9&g_st=it"},
{"id": "nphk-20261015-0507", "customer": "តេលា", "province": "កំពង់ឆ្នាំង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 509, "lead_no": 507},
{"id": "nphk-20261015-0508", "customer": "ដើមកាហ្វេ អ៊ិចស្រ្ពេស", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 510, "lead_no": 508},
{"id": "nphk-20261015-0509", "customer": "PICH COFFEE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/NS6rxYzRAHRPnS5D6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 511, "lead_no": 509, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5318309,104.9296739&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=9cca0c1c-bb8e-4c08-b09b-30d4daf2be8c&g_st=it"},
{"id": "nphk-20261015-0510", "customer": "ស្រី ពៅ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 512, "lead_no": 510},
{"id": "nphk-20261015-0511", "customer": "SREY PHEAK", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 513, "lead_no": 511},
{"id": "nphk-20261015-0512", "customer": "ពៅ លីហុង", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 514, "lead_no": 512},
{"id": "nphk-20261015-0513", "customer": "THEARY", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/fCyvZSzrEx2Mc8u56?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 515, "lead_no": 513, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5141191,104.9024659&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=4d59d915-2af7-462b-9fc2-9a16214896ca&g_st=it"},
{"id": "nphk-20261015-0514", "customer": "មុំ ចន្ទ័រតនា", "province": "តាកែវ", "url": "https://maps.app.goo.gl/m2wRWPwMwYbHedGB7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 516, "lead_no": 514, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=10.9794480,104.7747130&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=f4e2a8d6-a20f-4d99-a704-4187c4b5bedc&g_st=it"},
{"id": "nphk-20261015-0515", "customer": "និនិកាហ្វេ- NINI CAFÉ", "province": "កំពង់ធំ", "url": "https://maps.google.com/maps?q=13.036699,104.513791&ll=13.036699,104.513791&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 517, "lead_no": 515},
{"id": "nphk-20261015-0516", "customer": "SOEURNG SREY NEANG", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/oaWKqDxFCaxQnCyJ7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 518, "lead_no": 516, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=12.6128550,105.0031460&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=8929b6f1-adde-4fdc-a46f-afa4d2004a74&g_st=it"},
{"id": "nphk-20261015-0517", "customer": "SON CHANDY", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/38LexCPMCQExx1TM9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 519, "lead_no": 517, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0518", "customer": "TEB CHOMNO", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 520, "lead_no": 518},
{"id": "nphk-20261015-0519", "customer": "ROTH", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 521, "lead_no": 519},
{"id": "nphk-20261015-0520", "customer": "MALIKA YURI", "province": "កំពង់ចាម", "url": "https://maps.app.goo.gl/fkka935UGb9iAkLF7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 522, "lead_no": 520, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0521", "customer": "SAMNEANG LUN", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.583637,104.841023&ll=11.583637,104.841023&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 523, "lead_no": 521},
{"id": "nphk-20261015-0522", "customer": "DIAMOND BICYCLE", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 524, "lead_no": 522},
{"id": "nphk-20261015-0523", "customer": "ដេប៉ូតេលាគីឡូម៉ែត្រ65", "province": "កំពង់ឆ្នាំង", "url": "https://maps.app.goo.gl/MUMtHk5JzN65nqg88?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 525, "lead_no": 523, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0524", "customer": "SREYPICH THAI", "province": "ត្បូងឃ្មុំ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 526, "lead_no": 524},
{"id": "nphk-20261015-0525", "customer": "MONI VANN", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 527, "lead_no": 525},
{"id": "nphk-20261015-0526", "customer": "SOPHEAROM MEN", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 528, "lead_no": 526},
{"id": "nphk-20261015-0527", "customer": "MOUY YIM", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 529, "lead_no": 527},
{"id": "nphk-20261015-0528", "customer": "LIKA MECH", "province": "កំពត", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 530, "lead_no": 528},
{"id": "nphk-20261015-0529", "customer": "BELLA SMITT", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.395932,104.801630&ll=11.395932,104.801630&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 531, "lead_no": 529},
{"id": "nphk-20261015-0530", "customer": "HORN SIVNAI", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 532, "lead_no": 530},
{"id": "nphk-20261015-0531", "customer": "POP CAFÉ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/YVHnyEySsoBitf4f7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 533, "lead_no": 531, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0532", "customer": "ទួនហ្វា", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 534, "lead_no": 532},
{"id": "nphk-20261015-0533", "customer": "PTT", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 535, "lead_no": 533},
{"id": "nphk-20261015-0534", "customer": "ចណ្ណា កាហ្វេ", "province": "តាកែវ", "url": "https://maps.app.goo.gl/wURSFi2aqQRxotLKA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 536, "lead_no": 534, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0535", "customer": "PTT", "province": "កំពង់ចាម", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 537, "lead_no": 535},
{"id": "nphk-20261015-0536", "customer": "PTT", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 538, "lead_no": 536},
{"id": "nphk-20261015-0537", "customer": "PTT", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 539, "lead_no": 537},
{"id": "nphk-20261015-0538", "customer": "ហួត លៀងទុយ", "province": "កោះកុង", "url": "https://maps.google.com/maps?q=11.139767,103.768197&ll=11.139767,103.768197&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 540, "lead_no": 538},
{"id": "nphk-20261015-0539", "customer": "KATI YA", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 541, "lead_no": 539},
{"id": "nphk-20261015-0540", "customer": "LEEYA SUON", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 542, "lead_no": 540},
{"id": "nphk-20261015-0541", "customer": "លាស់ គីមលាង", "province": "ប៉ោយប៉ែត", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 543, "lead_no": 541},
{"id": "nphk-20261015-0542", "customer": "NIMOL VOEUN", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 544, "lead_no": 542},
{"id": "nphk-20261015-0543", "customer": "LAY KONG RETAIL", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/8tzE4c8pDT5kFAm7A?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 545, "lead_no": 543, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0544", "customer": "លីមដា កាហ្វេ", "province": "កោះកុង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 546, "lead_no": 544},
{"id": "nphk-20261015-0545", "customer": "HENG CHHUNIM", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.530185,104.864197&ll=11.530185,104.864197&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 547, "lead_no": 545},
{"id": "nphk-20261015-0546", "customer": "តុប ណៃអេង", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 548, "lead_no": 546},
{"id": "nphk-20261015-0547", "customer": "ប៉ុក វ៉ាត", "province": "រតនគិរី", "url": "https://maps.app.goo.gl/jr1FMhFTVrpzXqfdA?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 549, "lead_no": 547, "resolved_url": "https://www.google.com/maps/place/13.685918,107.216926/data=!4m6!3m5!1s0!7e2!8m2!3d13.6859176!4d107.2169263?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI1LjEzLjYYACDj7Q0qYyw5NDIyMzI5OSw5NDIxNjQxMyw5NDIxMjQ5Niw5NDIwNzM5NCw5NDIwNzUwNiw5NDIwODUwNiw5NDIxNzUyMyw5NDIxODY1Myw5NDIyOTgzOSw0NzA4NDM5Myw5NDIxMzIwMEICS0g%3D&skid=648cd766-2ce9-4479-823b-f383d4f044c7&g_st=atm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0548", "customer": "KONG SIMALA", "province": "ប៉ៃលិន", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 550, "lead_no": 548},
{"id": "nphk-20261015-0549", "customer": "សឿន ប៊ុនឆៃ បុរីសូនី", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/k3penyvvMnXeUpSn6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 551, "lead_no": 549, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5275120,104.8807430&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b525be45-d9cb-4ce9-9240-272f9257a9a0&g_st=it"},
{"id": "nphk-20261015-0550", "customer": "MA DY", "province": "ព្រៃវែង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 552, "lead_no": 550},
{"id": "nphk-20261015-0551", "customer": "ចាន​ ថន", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 553, "lead_no": 551},
{"id": "nphk-20261015-0552", "customer": "ដើមកាហ្វេ អ៊ិចស្រ្ពេស", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 554, "lead_no": 552},
{"id": "nphk-20261015-0553", "customer": "SOMA LY", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.620510,103.542128&ll=10.620510,103.542128&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 555, "lead_no": 553},
{"id": "nphk-20261015-0554", "customer": "BTA WATCH", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/SPjvFBGQkcD5o2nT7", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 556, "lead_no": 554, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0555", "customer": "DY KIMSA", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 557, "lead_no": 555},
{"id": "nphk-20261015-0556", "customer": "នំបុ័ងភ្នំពេញ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 558, "lead_no": 556},
{"id": "nphk-20261015-0557", "customer": "AH HEAK", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 559, "lead_no": 557},
{"id": "nphk-20261015-0558", "customer": "ជាងពុម្ភ ជាងដែក", "province": "កោះកុង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 560, "lead_no": 558},
{"id": "nphk-20261015-0559", "customer": "KIM SEU LY", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/1aNgLMuepZNhrQXk7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 561, "lead_no": 559, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5237610,104.9075820&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b35e3b10-1f9c-4374-b435-68abc3a3b458&g_st=it"},
{"id": "nphk-20261015-0560", "customer": "ចេ ស្រស់", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.278135,104.210464&ll=11.278135,104.210464&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 562, "lead_no": 560},
{"id": "nphk-20261015-0561", "customer": "EI SOK MENG", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.389148,104.378740&ll=11.389148,104.378740&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 563, "lead_no": 561},
{"id": "nphk-20261015-0562", "customer": "SOU SARITH", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 564, "lead_no": 562},
{"id": "nphk-20261015-0563", "customer": "THEARYNA SENG", "province": "មណ្ឌលគិរី", "url": "https://maps.google.com/maps?q=12.460194,107.185893&ll=12.460194,107.185893&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 565, "lead_no": 563},
{"id": "nphk-20261015-0564", "customer": "ម៉ាក់ កូនវិ", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/dwtmMviNLSTYdSNW7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 566, "lead_no": 564, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5008200,104.7504870&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=31fa9195-cfcd-4d90-b258-6ee98f2267b6&g_st=it"},
{"id": "nphk-20261015-0565", "customer": "NIN NOCH", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 567, "lead_no": 565},
{"id": "nphk-20261015-0566", "customer": "THY CHOURY", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/yYPf4eriKD3qvbF6A?g_st=com.google.maps.preview.copy", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 568, "lead_no": 566, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.7587270,104.9232300&entry=gps&lucs=,94259550,94242520,94224825,94227247,94227248,94231188,47071704,94259573,47069508,94218641,94203019,47084304,94208458,94208447&g_ep=CAISEjI1LjA4LjAuNzI3OTM5NzI3MBgAIIgnKn4sOTQyNTk1NTAsOTQyNDI1MjAsOTQyMjQ4MjUsOTQyMjcyNDcsOTQyMjcyNDgsOTQyMzExODgsNDcwNzE3MDQsOTQyNTk1NzMsNDcwNjk1MDgsOTQyMTg2NDEsOTQyMDMwMTksNDcwODQzMDQsOTQyMDg0NTgsOTQyMDg0NDdCAktI&g_st=com.google.maps.preview.copy"},
{"id": "nphk-20261015-0567", "customer": "SREY LIN", "province": "កំពត", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 569, "lead_no": 567},
{"id": "nphk-20261015-0568", "customer": "MORIKO KREE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/oVxQR1sv3GSBVCi78?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 570, "lead_no": 568, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.7293560,104.5577810&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjQuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=af70c0b9-cab8-4b4c-aaa1-9d7b32839142&g_st=ic"},
{"id": "nphk-20261015-0569", "customer": "ស្រី នាត", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 571, "lead_no": 569},
{"id": "nphk-20261015-0570", "customer": "កោះកាហ្វេ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/18SoQZcfJb72jGqV8", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 572, "lead_no": 570, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0571", "customer": "RADET JASPER", "province": "ភ្នំពេញ", "url": "https://nphk-pos.balancikaapps.com/login", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 573, "lead_no": 571},
{"id": "nphk-20261015-0572", "customer": "DYSON KLEN COFFEE", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 574, "lead_no": 572},
{"id": "nphk-20261015-0573", "customer": "VOUCH CHHENG", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.126683,104.336279&ll=13.126683,104.336279&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 575, "lead_no": 573},
{"id": "nphk-20261015-0574", "customer": "SOK HENG", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 576, "lead_no": 574},
{"id": "nphk-20261015-0575", "customer": "THIDA RITH", "province": "កំពង់ចាម", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 577, "lead_no": 575},
{"id": "nphk-20261015-0576", "customer": "ជឹមជ័យសិរីមុន្និន", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/VTeN9fhx6P3hCadZ8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 578, "lead_no": 576, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5513240,104.9396820&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjQuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=aede89dd-bf1b-4c7e-8fff-fc5f7f543902&g_st=ic"},
{"id": "nphk-20261015-0577", "customer": "ជា សុភ័ក្រ្ត", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/BPoYiJgLGyzeANsw8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 579, "lead_no": 577, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5389860,104.9028930&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjQuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=1baf7668-37c7-4c70-ad93-9e562cbd05c7&g_st=ic"},
{"id": "nphk-20261015-0578", "customer": "PK CAFÉ & MINI MART", "province": "សៀមរាប", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 580, "lead_no": 578},
{"id": "nphk-20261015-0579", "customer": "RA SREYNA", "province": "ព្រៃវែង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 581, "lead_no": 579},
{"id": "nphk-20261015-0580", "customer": "LITA OUDOM", "province": "កំពង់ចាម", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 582, "lead_no": 580},
{"id": "nphk-20261015-0581", "customer": "SEAV AY", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 583, "lead_no": 581},
{"id": "nphk-20261015-0582", "customer": "FA NG", "province": "ស្វាយរៀង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 584, "lead_no": 582},
{"id": "nphk-20261015-0583", "customer": "AH LEAK", "province": "ព្រះសីហនុ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 585, "lead_no": 583},
{"id": "nphk-20261015-0584", "customer": "NITA KNP", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 586, "lead_no": 584},
{"id": "nphk-20261015-0585", "customer": "ចែ ទៀង", "province": "ព្រះសីហនុ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 587, "lead_no": 585},
{"id": "nphk-20261015-0586", "customer": "JEE NEATH", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 588, "lead_no": 586},
{"id": "nphk-20261015-0587", "customer": "SPATA CAFÉ KOH NOREA", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 589, "lead_no": 587},
{"id": "nphk-20261015-0588", "customer": "PREMIUM LAND COFFEE", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 590, "lead_no": 588},
{"id": "nphk-20261015-0589", "customer": "KON LYHOR", "province": "កំពង់ធំ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 591, "lead_no": 589},
{"id": "nphk-20261015-0590", "customer": "LAY LYCHING SOK SOTHEAVORN", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/oVxQR1sv3GSBVCi78?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 592, "lead_no": 590, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.7293560,104.5577810&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjQuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=af70c0b9-cab8-4b4c-aaa1-9d7b32839142&g_st=ic"},
{"id": "nphk-20261015-0591", "customer": "ROTH KIMHONG", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 593, "lead_no": 591},
{"id": "nphk-20261015-0592", "customer": "PIN SAVAT", "province": "ត្បូងឃ្មុំ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 594, "lead_no": 592},
{"id": "nphk-20261015-0593", "customer": "SOK ENG PUY", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 595, "lead_no": 593},
{"id": "nphk-20261015-0594", "customer": "AH GECH CORNER", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 596, "lead_no": 594},
{"id": "nphk-20261015-0595", "customer": "LAK KHA", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 597, "lead_no": 595}
]"""

# ==========================================
# CUSTOMER MAP REGISTRY — independent of delivery quantities and journal rows
# ==========================================
MAP_ALLOWED_HOSTS = frozenset({"maps.google.com", "www.google.com", "google.com",
    "maps.app.goo.gl", "goo.gl", "g.co", "share.google", "maps.apple", "maps.apple.com"})
MAP_SHORT_HOSTS = frozenset({"maps.app.goo.gl", "goo.gl", "g.co", "share.google", "maps.apple"})


def trusted_map_url(value):
    """Allow only HTTPS map providers, including at every redirect hop."""
    value = str(value or "").strip()
    if not value or len(value) > 6000 or any(ord(c) < 32 for c in value):
        return ""
    try:
        parsed = urllib.parse.urlsplit(value)
        if (parsed.scheme != "https" or parsed.hostname not in MAP_ALLOWED_HOSTS
                or parsed.username is not None or parsed.password is not None
                or parsed.port not in (None, 443)):
            return ""
        if parsed.hostname in {"google.com", "www.google.com", "maps.google.com"}:
            allowed_root = parsed.hostname == "maps.google.com" and parsed.path in ("", "/")
            if not allowed_root and parsed.path != "/maps" and not parsed.path.startswith("/maps/"):
                return ""
        return value
    except (ValueError, TypeError):
        return ""


def analyse_map_link(value):
    """Only destination coordinates become pins; viewport centers are never pins."""
    result = {"Map status": "Missing link", "Latitude": None, "Longitude": None,
              "Map link": "", "Directions": ""}
    if not str(value or "").strip():
        return result
    url = trusted_map_url(value)
    if not url:
        result["Map status"] = "Invalid map link"
        return result
    result["Map link"] = url
    parsed = urllib.parse.urlsplit(url)
    decoded = urllib.parse.unquote(url)
    pairs = [(float(a), float(b)) for a, b in re.findall(
        r"!3d([-+]?\d+(?:\.\d+)?)!4d([-+]?\d+(?:\.\d+)?)", decoded)]
    query = urllib.parse.parse_qs(parsed.query)
    for key in ("q", "query", "destination", "coordinate"):
        for item in query.get(key, []):
            match = re.fullmatch(r"\s*(?:loc:)?\s*([-+]?\d+(?:\.\d+)?)\s*,\s*([-+]?\d+(?:\.\d+)?)\s*", item)
            if match:
                pairs.append(tuple(map(float, match.groups())))
    unique = {(round(a, 6), round(b, 6)) for a, b in pairs}
    if len(unique) > 1:
        result["Map status"] = "Multiple pins — review"
    elif unique:
        lat, lon = next(iter(unique))
        if not (math.isfinite(lat) and math.isfinite(lon) and 10 <= lat <= 15 and 102 <= lon <= 108):
            result["Map status"] = "Outside Cambodia area — review"
        else:
            result.update({"Map status": "Ready pin", "Latitude": lat, "Longitude": lon,
                           "Directions": f"https://www.google.com/maps/dir/?api=1&destination={lat},{lon}&travelmode=driving"})
    elif parsed.hostname in MAP_SHORT_HOSTS:
        result["Map status"] = "Needs link expansion"
    else:
        result["Map status"] = "Link has no destination coordinates"
    return result


def _read_map_overlay():
    if not os.path.exists(MAP_REGISTRY_FILE):
        return {"version": 1, "records": {}, "bindings": {}}
    try:
        with open(MAP_REGISTRY_FILE, "r", encoding="utf-8-sig") as f:
            data = json.load(f)
        if (not isinstance(data, dict) or data.get("version") != 1
                or not isinstance(data.get("records"), dict) or not isinstance(data.get("bindings"), dict)):
            raise ValueError("unsupported registry structure")
        for key, rec in data["records"].items():
            if (not isinstance(rec, dict) or rec.get("id") != key
                    or not isinstance(rec.get("customer"), str) or not rec["customer"].strip()
                    or not isinstance(rec.get("url", ""), str)):
                raise ValueError("invalid customer location record")
        if any(not isinstance(k, str) or not isinstance(v, str) for k, v in data["bindings"].items()):
            raise ValueError("invalid customer binding")
        return data
    except (OSError, ValueError, TypeError) as e:
        raise RuntimeError("Customer map registry cannot be read safely. Original records were preserved; restore a verified backup.") from e


def load_map_registry(force=False):
    with _sync_state()["lock"]:
        if USE_DROPBOX:
            pull(MAP_REGISTRY_FILE, force=force)
        overlay = _read_map_overlay()
        records = {r["id"]: dict(r) for r in json.loads(_MAP_SEED_JSON)}
        records.update({key: dict(rec) for key, rec in overlay["records"].items()})
        return {"records": records, "bindings": dict(overlay["bindings"])}


def modify_map_registry(fn):
    """Admin-only, atomic read/change/save with revision conflict retries."""
    if current_role() != "admin" or not has_permission("edit"):
        raise PermissionError("Only Admin can change customer map locations.")
    for attempt in range(6):
        try:
            with _sync_state()["lock"], file_lock(MAP_REGISTRY_FILE):
                if USE_DROPBOX:
                    pull(MAP_REGISTRY_FILE, force=True)
                overlay = _read_map_overlay()
                fn(overlay)
                if os.path.exists(MAP_REGISTRY_FILE) and not backup_file(MAP_REGISTRY_FILE, "before-map-edit"):
                    raise RuntimeError("Cannot save customer maps because a backup could not be made.")
                _write_atomic(MAP_REGISTRY_FILE, json.dumps(overlay, ensure_ascii=False, indent=2).encode("utf-8"))
                if USE_DROPBOX:
                    push(MAP_REGISTRY_FILE)
            auto_bot.clear()
            return
        except ConflictError:
            if attempt == 5:
                raise RuntimeError("Customer maps changed in another session. Reload and try again.")
            time.sleep(0.2 * (attempt + 1))


def map_record_analysis(record):
    analysis = analyse_map_link(record.get("resolved_url") or record.get("url", ""))
    if (analysis["Map status"] == "Needs link expansion"
            and "no usable destination coordinates" in record.get("resolution_note", "")):
        analysis["Map status"] = "Needs full pin link"
    return analysis


def map_registry_frame(registry=None):
    registry = registry if registry is not None else load_map_registry()
    rows = []
    for rec in registry["records"].values():
        analysis = map_record_analysis(rec)
        rows.append({"Location ID": rec["id"], "Customer": rec["customer"],
                     "Province (source)": rec.get("province", ""), "Source row": rec.get("source_row", ""),
                     "Original link": rec.get("url", ""), "Resolution note": rec.get("resolution_note", ""), **analysis})
    frame = pd.DataFrame(rows, columns=["Location ID", "Customer", "Province (source)", "Source row", "Map status",
        "Latitude", "Longitude", "Map link", "Directions", "Original link", "Resolution note"])
    frame["Source row"] = pd.to_numeric(frame["Source row"], errors="coerce").astype("Int64")
    return frame


def customer_map_match(customer, registry):
    """No fuzzy identity matching and no merging separate leads with the same name."""
    key = norm_name(customer)
    bound = registry["bindings"].get(key)
    if bound:
        rec = registry["records"].get(bound)
        if not rec:
            return {"Map status": "Saved match needs review", "Map link": "", "Directions": "", "Location ID": ""}
        candidates = [rec]
    else:
        candidates = [rec for rec in registry["records"].values() if norm_name(rec["customer"]) == key]
    if not candidates:
        return {"Map status": "No location match", "Map link": "", "Directions": "", "Location ID": ""}
    # Any duplicate identity requires Admin's explicit choice, even when a pin is shared.
    if len(candidates) != 1:
        return {"Map status": "Repeated name — choose location", "Map link": "", "Directions": "", "Location ID": ""}
    rec = candidates[0]
    return {**map_record_analysis(rec), "Location ID": rec["id"]}


def mapped_customer_province(customer, registry):
    matched = customer_map_match(customer, registry)
    rec = registry["records"].get(matched.get("Location ID", ""), {})
    province_text = rec.get("province", "")
    if not province_text:
        return None
    english = {norm_name(name): name for name in PROVINCES}.get(norm_name(province_text))
    return english or detect_province(province_text)[0]


def attach_customer_maps(frame, registry=None):
    result = frame.copy()
    registry = registry if registry is not None else load_map_registry()
    matches = [customer_map_match(str(name), registry) for name in result["Customer"]]
    for col in ("Map status", "Map link", "Directions", "Location ID", "Latitude", "Longitude"):
        result[col] = [match.get(col) for match in matches]
    return result


class _ResolvedMapPin(Exception):
    def __init__(self, url):
        super().__init__("Destination coordinates found")
        self.url = url


class _MapRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if not trusted_map_url(newurl):
            if fp is not None:
                fp.close()
            raise ValueError("Map link redirected outside the supported map providers.")
        if analyse_map_link(newurl)["Map status"] == "Ready pin":
            if fp is not None:
                fp.close()
            raise _ResolvedMapPin(newurl)
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def resolve_map_link(url):
    """Network-only worker: no Streamlit/session access and no coordinates guessed from HTML."""
    if not trusted_map_url(url):
        raise ValueError("Unsupported map link")
    if analyse_map_link(url)["Map status"] == "Ready pin":
        return url
    opener = urllib.request.build_opener(_MapRedirectHandler())
    request = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (compatible; CustomerMap/1.0)"})
    try:
        with opener.open(request, timeout=10) as response:
            final_url = response.geturl()
            if not trusted_map_url(final_url):
                raise ValueError("Unsupported map destination")
            if analyse_map_link(final_url)["Map status"] != "Ready pin":
                raise ValueError("Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead.")
            return final_url
    except _ResolvedMapPin as found:
        return found.url


def _draw_customer_pins(frame):
    pins = frame[frame["Map status"] == "Ready pin"].copy()
    if pins.empty:
        st.info("No usable customer pins in this selection. Open a saved map link or ask Admin to add one.")
        return
    st.caption(f"{len(pins)} location records have usable coordinates. Pins come from supplied links; confirm the destination before delivery.")
    try:
        import pydeck as pdk
        pins["Label"] = pins["Customer"].astype(str)
        pins["Pin_ID"] = pins["Location ID"]
        layer = pdk.Layer("ScatterplotLayer", data=pins, get_position="[Longitude, Latitude]",
                          get_radius=60, radius_min_pixels=5, radius_max_pixels=12,
                          get_fill_color=[225, 70, 65, 220], get_line_color=[255, 255, 255],
                          stroked=True, line_width_min_pixels=1, pickable=True)
        center = pdk.ViewState(latitude=float(pins["Latitude"].median()), longitude=float(pins["Longitude"].median()),
                               zoom=11 if len(pins) == 1 else 6, pitch=0)
        deck = pdk.Deck(layers=[layer], map_provider="carto", map_style="light", initial_view_state=center,
                       tooltip={"text": "{Label}\nLocation ID: {Pin_ID}"})
        try:
            st.pydeck_chart(deck, width="stretch")
        except TypeError:
            st.pydeck_chart(deck, use_container_width=True)
    except Exception as e:
        bot_log("warn", "Customer map", str(e)[:160], "showing location list; pins may need internet access")
        st.info("The map could not load. Saved Google Maps links and directions are available in the list below.")


def _map_admin_panel(registry, locations):
    if current_role() != "admin" or not has_permission("edit"):
        return
    st.markdown("#### Manage customer locations")
    with st.expander("Add a new customer location"):
        with st.form("map_add_customer"):
            new_name = st.text_input("New customer name", max_chars=MAX_TEXT, key="map_new_name")
            new_province = st.text_input("New customer's province / area", max_chars=MAX_TEXT, key="map_new_province")
            new_url = st.text_input("New customer's map pin link", max_chars=6000, key="map_new_url")
            if st.form_submit_button("Add customer location"):
                if not new_name.strip():
                    st.error("Enter a customer name.")
                elif new_url.strip() and not trusted_map_url(new_url):
                    st.error("Use a valid HTTPS Google Maps or Apple Maps link.")
                else:
                    rid = "manual-" + pysecrets.token_hex(8)
                    added = {"id": rid, "customer": new_name.strip(), "province": new_province.strip(),
                             "url": new_url.strip(), "source": "Admin", "source_row": "", "lead_no": ""}
                    try:
                        modify_map_registry(lambda overlay: overlay["records"].update({rid: added}))
                        audit("customer_map_add", rid)
                        flash_and_refresh("Customer location added")
                    except Exception as e:
                        st.error(f"Could not add this customer: {e}")
    all_ids = list(registry["records"])
    labels = {rid: f"{r['customer']} | {r.get('province', '')} | {rid}" for rid, r in registry["records"].items()}
    selected_id = st.selectbox("Select a location to correct", all_ids, format_func=labels.get, key="map_admin_record")
    if not selected_id:
        return
    rec = registry["records"][selected_id]
    edit_signature = hashlib.sha256(json.dumps(rec, sort_keys=True, ensure_ascii=False).encode()).hexdigest()[:12]
    with st.form("map_location_edit"):
        customer = st.text_input("Customer name", value=rec["customer"], max_chars=MAX_TEXT, key=f"map_name_{selected_id}_{edit_signature}")
        province = st.text_input("Province / area", value=rec.get("province", ""), max_chars=MAX_TEXT, key=f"map_prov_{selected_id}_{edit_signature}")
        url = st.text_input("Google Maps or Apple Maps pin link", value=rec.get("resolved_url") or rec.get("url", ""),
                            max_chars=6000, key=f"map_url_{selected_id}_{edit_signature}")
        if st.form_submit_button("Save this customer location"):
            if not customer.strip():
                st.error("Enter a customer name.")
            elif url.strip() and not trusted_map_url(url):
                st.error("Use a valid HTTPS Google Maps or Apple Maps link.")
            else:
                changed = {**rec, "customer": customer.strip(), "province": province.strip(),
                           "url": url.strip(), "resolved_url": "", "resolution_note": "Updated by Admin " + now_str()}
                try:
                    def save_location(overlay):
                        latest = overlay["records"].get(selected_id, rec)
                        if latest != rec:
                            raise RuntimeError("This location changed in another session. Reload before saving.")
                        overlay["records"][selected_id] = changed
                    modify_map_registry(save_location)
                    audit("customer_map_edit", selected_id)
                    flash_and_refresh("Customer location saved")
                except Exception as e:
                    st.error(f"Could not save this location: {e}")
    with st.expander("Match a delivery customer to a saved location"):
        st.caption("Use this for different spellings or repeated names. This match does not rename customers or change order quantities.")
        with st.form("customer_map_binding", clear_on_submit=False):
            snap, _, _, _ = current_snapshot()
            system_names = sorted(set(snap["customers"]) | set(snap["journal"]["Customer"])) if snap else []
            if system_names:
                system_customer = st.selectbox("Customer in your delivery system", system_names, key="map_bind_customer")
            else:
                system_customer = st.text_input("Exact customer name in your delivery system", key="map_bind_customer_text")
            target = st.selectbox("Correct saved location", all_ids, format_func=labels.get, key="map_bind_location")
            save_binding = st.form_submit_button("Save customer match")
            remove_binding = st.form_submit_button("Remove this saved match")
        if save_binding:
            if system_customer.strip():
                try:
                    modify_map_registry(lambda overlay: overlay["bindings"].update({norm_name(system_customer): target}))
                    audit("customer_map_match", f"{system_customer} -> {target}")
                    flash_and_refresh("Customer map match saved")
                except Exception as e:
                    st.error(f"Could not save this match: {e}")
        current_binding = registry["bindings"].get(norm_name(system_customer))
        if current_binding:
            st.caption("Current location: " + labels.get(current_binding, current_binding))
            if remove_binding:
                try:
                    modify_map_registry(lambda overlay: overlay["bindings"].pop(norm_name(system_customer), None))
                    flash_and_refresh("Customer map match removed")
                except Exception as e:
                    st.error(f"Could not remove this match: {e}")
    with st.expander("Expand shortened map links"):
        pending = locations[locations["Map status"] == "Needs link expansion"]
        st.caption(f"{len(pending)} links need expansion. The app opens up to 20 links at a time. Your server needs access to Google / Apple Maps.")
        if st.button("Resolve next 20 map links", key="map_resolve", disabled=pending.empty):
            selected = pending.sort_values("Resolution note", kind="stable").head(20)
            updates, failed = {}, []
            from concurrent.futures import ThreadPoolExecutor, as_completed
            with st.spinner("Checking saved map links…"):
                with ThreadPoolExecutor(max_workers=4) as pool:
                    jobs = {pool.submit(resolve_map_link, r["Original link"]): r["Location ID"] for r in selected.to_dict("records")}
                    for future in as_completed(jobs):
                        rid = jobs[future]
                        updated = dict(registry["records"][rid])
                        try:
                            updated["resolved_url"] = future.result()
                            updated["resolution_note"] = "Expanded " + now_str()
                        except Exception as e:
                            updated["resolution_note"] = str(e)[:220]
                            failed.append(rid)
                        updates[rid] = updated
            # Prevent an expansion result overwriting an Admin's newer location correction.
            def apply_expansions(overlay):
                for rid, updated in updates.items():
                    latest = overlay["records"].get(rid, registry["records"][rid])
                    original = registry["records"][rid]
                    if latest.get("url") == original.get("url") and latest.get("resolved_url", "") == original.get("resolved_url", ""):
                        overlay["records"][rid] = {**latest, "resolved_url": updated.get("resolved_url", ""),
                                                   "resolution_note": updated["resolution_note"]}
            try:
                modify_map_registry(apply_expansions)
                audit("customer_map_expand", f"{len(updates) - len(failed)} resolved; {len(failed)} need review")
                flash_and_refresh(f"Resolved {len(updates) - len(failed)} links. {len(failed)} need review; see Resolution note.")
            except Exception as e:
                st.error(f"Could not save expansion results: {e}")


def _customer_map_body():
    if not has_permission("view"):
        st.error("Customer map viewing is disabled for your account.")
        return
    st.subheader("Customer locations")
    st.caption("Imported sales records stay separate from daily delivery orders. Repeated names keep separate location IDs.")
    registry = load_map_registry()
    locations = map_registry_frame(registry)
    cols = st.columns(4)
    for col, title, value in zip(cols, ("Location records", "Ready for pins", "Need link expansion", "Need review / missing"),
            (len(locations), int((locations["Map status"] == "Ready pin").sum()),
             int((locations["Map status"] == "Needs link expansion").sum()),
             int((~locations["Map status"].isin(["Ready pin", "Needs link expansion"])).sum()))):
        col.metric(title, value)
    with st.form("customer_map_filters"):
        search = st.text_input("Search customer, province or location ID", key="customer_map_search", max_chars=MAX_TEXT)
        statuses = ["All"] + sorted(locations["Map status"].unique())
        status = st.selectbox("Location status", statuses, key="customer_map_filter")
        scope = st.radio("Map selection", ["All imported locations", "Today's delivery customers"], horizontal=True, key="customer_map_scope")
        st.form_submit_button("Apply map filters")
    view = locations
    if scope == "Today's delivery customers":
        report, _, error = build_report(today_kh())
        if error:
            st.warning("Journal unavailable. Delivery-only map may be incomplete.")
        if report.empty:
            view = locations.iloc[0:0]
        else:
            matched = attach_customer_maps(report, registry)
            st.caption(f"{int(matched['Location ID'].fillna('').ne('').sum())} of {len(matched)} delivery customers matched; Admin can confirm missing or repeated names.")
            view = locations[locations["Location ID"].isin(matched["Location ID"].dropna())]
    if search.strip():
        hay = view[["Customer", "Province (source)", "Location ID"]].astype(str).agg(" ".join, axis=1)
        view = view[hay.str.contains(search.strip(), case=False, regex=False)]
    if status != "All":
        view = view[view["Map status"] == status]
    _draw_customer_pins(view)
    st.caption(f"Showing {len(view)} records. Missing or suspicious coordinates are excluded from the pin map.")
    table_config = {"Map link": st.column_config.LinkColumn("Open map", display_text="Open map"),
                       "Directions": st.column_config.LinkColumn("Directions", display_text="Directions"),
                       "Latitude": st.column_config.NumberColumn(format="%.6f"),
                       "Longitude": st.column_config.NumberColumn(format="%.6f")}
    try:
        st.dataframe(view.drop(columns=["Original link"]), hide_index=True, width="stretch", column_config=table_config)
    except TypeError:
        st.dataframe(view.drop(columns=["Original link"]), hide_index=True, use_container_width=True, column_config=table_config)
    visible_ids = view["Location ID"].tolist()
    if visible_ids:
        labels = {r["Location ID"]: f"{r['Customer']} — {r['Location ID']}" for r in view.to_dict("records")}
        chosen = st.selectbox("Open a customer's location", visible_ids, format_func=labels.get, key="customer_map_open")
        row = view.set_index("Location ID").loc[chosen]
        if row["Map link"]:
            st.link_button("Open in Maps", row["Map link"])
        if row["Directions"]:
            st.link_button("Google Maps directions", row["Directions"])
    if has_permission("reports"):
        st.download_button("Download location list", data=view.apply(lambda col: col.map(lambda v: safe_text(v, 6000) if isinstance(v, str) else v)).to_csv(index=False).encode("utf-8-sig"),
                           file_name="customer_map_locations.csv", mime="text/csv", key="map_export")
    if current_role() == "admin":
        with st.expander("Admin: add locations, correct links and match customers"):
            _map_admin_panel(registry, locations)


@st.fragment
def tab_customer_map():
    safe_render(_customer_map_body, "Customer map")


# ==========================================
# APP LAYOUT
# ==========================================
@st.fragment(run_every=60)
def health_status():
    findings, _ = auto_bot()
    errors = sum(f["Level"] == LEVEL_ICON["error"] for f in findings)
    warnings_count = sum(f["Level"] == LEVEL_ICON["warn"] for f in findings)
    if errors:
        st.warning(f"Health Bot: {errors} errors and {warnings_count} warnings. Ask Admin to review Health Bot.")
    elif warnings_count:
        st.caption(f"Health Bot: {warnings_count} warnings for Admin to review.")


st.set_page_config(page_title="Delivery Operations", page_icon="🚚", layout="wide",
                   initial_sidebar_state="collapsed")
st.markdown(CSS, unsafe_allow_html=True)
_reset_prefix = st.session_state.pop("reset_form_prefix", None)
if _reset_prefix:
    for _key in list(st.session_state):
        if str(_key).startswith(_reset_prefix):
            st.session_state.pop(_key, None)

ROLE = require_login()                     # nothing below runs until the person is logged in

_flash = st.session_state.pop("flash", None)
if _flash:
    st.toast(_flash, icon="✅")
_assignment_warning = st.session_state.pop("assignment_warning", None)
if _assignment_warning:
    st.warning(_assignment_warning)

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
                    try:                                          # this phone stays logged in after the change
                        _t = issue_remember_token(USER, load_users().get(USER, {}).get("pw_changed", ""))
                        if _t:
                            st.session_state["cookie_cmd"] = ("set", _t, USER)
                    except Exception:
                        pass
                    st.session_state["flash"] = "Password changed"
                    st.rerun()
        st.caption("At least 8 characters, letters and numbers.")
    if st.button("🚪 Log out", key="logout_btn"):
        logout("manual")
        st.rerun()

st.title("🚚 នំប៉ាវហុងកុង Supply Chain Hub")
with st.expander("Quick guide — start here"):
    st.markdown("1. **Packing:** choose your name, customer and cases, then save.\n"
                "2. **Delivery:** claim your customers, record sent cases, and add expenses now or later.\n"
                "3. **Dashboard:** search customers and check what is packed, sent or still pending.\n"
                "4. **Customer Map:** search imported customer locations and open directions. Admin can correct links and match names.\n"
                "5. If a save fails, keep your entries and read the message before trying again. "
                "Ask Admin to review Health Bot warnings.")

_backup_errors = daily_backup_once(today_kh().strftime("%Y-%m-%d"))
if _backup_errors and ROLE == "admin":
    st.warning("Backup needs attention: " + "; ".join(_backup_errors))
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
if ROLE in ("staff", "admin"):
    health_status()

_perms = effective_permissions(current_user())
labels = []
if _perms.get("tasks"):
    labels.extend(["📦 1. Packing Progress (Prep)", "🚚 2. Log Delivery (Ops)"])
if _perms.get("view"):
    labels.append("📊 Live Dashboard (Sales)")
    labels.append("📍 Customer Map")
elif _perms.get("reports"):
    labels.append("📑 Reports")
if ROLE == "admin":
    labels.append("🤖 4. Admin: Bot, Users & Security")
if not labels:
    st.warning("No app sections are enabled for your account. Ask Admin to turn on Tasks, View, or Reports.")
    st.stop()
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
        elif _label.startswith("📑"):
            tab_dashboard(False)
        elif _label.startswith("📍"):
            tab_customer_map()
        else:
            tab_bot()
