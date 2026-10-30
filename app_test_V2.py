# ============================================================
#  នំប៉ាវហុងកុង Supply Chain Hub  -  v3: fast, secure, self-healing
#  Run: python -m streamlit run app_reviewed_custom_permissions.py
#  Reviewed: batched selections, independent drafts, strict data checks and atomic saves.
# ============================================================
"""Delivery Operations — reviewed reliability update.

Run: python -m streamlit run app_reviewed_custom_permissions.py
Dependencies: streamlit>=1.37, pandas, openpyxl; dropbox for online mode.
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
import functools
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
ORDERS_FILE = os.path.join(DATA_DIR, "sale_orders.csv")              # orders typed on the site (synced to Dropbox)
HOLD_FILE = os.path.join(DATA_DIR, "customer_holds.csv")           # customers moved to tomorrow / cancelled
MAP_REGISTRY_FILE = os.path.join(DATA_DIR, "customer_map_registry.json")
CALLS_FILE = os.path.join(DATA_DIR, "customer_call_history.csv")
SI_ALIAS_FILE = os.path.join(DATA_DIR, "customer_same_names.csv")   # Admin: two spellings = same customer (or not)
VISITS_FILE = os.path.join(DATA_DIR, "shop_visits.csv")             # staff visits to customer shops
VISITS_TEST_FILE = os.path.join(DATA_DIR, "shop_visits_TEST.csv")   # admin practice visits (never in real reports)
VISIT_ZONE_FILE = os.path.join(DATA_DIR, "visit_zones.csv")         # Phnom Penh zone per shop, set by Admin
VISIT_PIN_FILE = os.path.join(DATA_DIR, "shop_pins.csv")            # shop locations saved at the shop by staff
LEADS_FILE = os.path.join(DATA_DIR, "new_customers_leads.csv")      # NPHK Leads Report rows imported in Shop Visits
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
JOURNAL_PAY_HEADER = "ការទូទាត់"        # journal column: payment (AR / FOC ...). FOC rows = free buns
BUN_CODE_RE = re.compile(r"^N\d+$")
CUSTOMER_CODE_RE = re.compile(r"^NPHK-\d+$", re.I)   # customer code column, never an invoice number
PROMO_REMARK_RE = re.compile(r"^\s*\d+\s*\+\s*\d+\s*$")  # "5+1", "10+2": bonus buns written on their own line


def free_reason(pay, remark, pcs, sales):
    """Why a journal row is free (not a paid sale), or "" when it is paid.
    - payment FOC (also the common typo F0C with a zero)
    - remark starting with FOC ("FOC ទូស្អាត", "FOC នំខូច")
    - a promotion bonus line ("5+1", "15+3") that has buns but 0 riel"""
    p = str(pay or "").strip().upper().replace("0", "O")
    r = str(remark or "").strip().upper()
    if p == "FOC":
        return "Payment FOC" if str(pay).strip().upper() == "FOC" else "Payment F0C (typo)"
    if r.startswith("FOC"):
        return "Remark FOC"
    try:
        no_riel = sales is not None and not pd.isna(sales) and float(sales) == 0
    except Exception:
        no_riel = False
    if PROMO_REMARK_RE.match(r) and no_riel and (pcs or 0) > 0:
        return "Promo bonus " + r.replace(" ", "")
    return ""  # journal columns N1, N2, N21 ... N43
SNAPSHOT_VERSION = 7                   # change this number to force the journal to be re-read

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
ORDER_BUNS = ["N1", "N2", "N21", "N22", "N23", "N3", "N31", "N32", "N33", "N4", "N41", "N42", "N43"]
ORDER_COLS = ["Date", "Customer", "OrderID", "Invoice", "Remark", "Payment", "Cases"] + ORDER_BUNS + ["Entered_By", "Entered_At", "Status"]
ORDER_NUM_COLS = ["Cases"] + ORDER_BUNS             # Status: Active | Deleted | InJournal (already copied into the journal)
NUM_COLS_ALL = set(DISPATCH_NUM_COLS + PACKING_NUM_COLS + HOLD_NUM_COLS + ORDER_NUM_COLS)
FILES = {
    "dispatch": (DATA_FILE, DISPATCH_COLS, DISPATCH_NUM_COLS, "Dispatch CSV"),
    "packing": (PACKING_FILE, PACKING_COLS, PACKING_NUM_COLS, "Packing CSV"),
    "assign": (ASSIGN_FILE, ASSIGN_COLS, [], "Assignments CSV"),
    "holds": (HOLD_FILE, HOLD_COLS, HOLD_NUM_COLS, "Moved / cancelled CSV"),
    "orders": (ORDERS_FILE, ORDER_COLS, ORDER_NUM_COLS, "Sale orders CSV"),
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
    if isinstance(v, str):
        return _parse_dt_text(v)
    return _parse_dt_any(v)


@functools.lru_cache(maxsize=65536)
def _parse_dt_text(v):
    return _parse_dt_any(v)


def _parse_dt_any(v):
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
    # CSV timestamps repeat in bulk saves; parse each distinct value only once.
    unique = series.drop_duplicates()
    parsed = {value: parse_dt(value) for value in unique}
    return pd.to_datetime(series.map(parsed), errors="coerce")


def cell_to_date(v, dominant=None):
    """One Excel journal cell -> date (or None). `dominant` = (year, month) most journal dates use."""
    if v is None:
        return None
    if isinstance(v, (datetime, pd.Timestamp)):
        return v.date()
    if isinstance(v, date):
        return v
    if isinstance(v, (int, float)) and not isinstance(v, bool):
        return None                    # a plain number (summary rows like "31") is never a journal date
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


def _tokens_fresh(force=False):
    """The saved-login list, fetched from Dropbox first (after an app restart the local copy is empty).
    -> (tokens, ok) ; ok=False when the list could not be checked (then nothing is deleted)."""
    if USE_DROPBOX:
        try:
            pull(REMEMBER_FILE, force=force, max_age=60.0)
        except Exception as e:
            bot_log("warn", "Remember login", f"could not refresh: {str(e)[:100]}", "kept the phone's login")
            return _read_tokens(), False
    return _read_tokens(), True


def restore_from_cookie():
    """Logs the person in again from the phone's saved token (after a screen lock, a closed tab, an app restart...).
    The phone's token is only deleted when it is surely invalid — never because Dropbox was slow."""
    token = _request_cookie(COOKIE_TOKEN)
    if not token:
        return False
    h, now = _tok_hash(token), time.time()
    tokens, ok = _tokens_fresh()
    rec = tokens.get(h)
    if rec is None and ok:
        tokens, ok = _tokens_fresh(force=True)          # maybe saved by another session a moment ago
        rec = tokens.get(h)
    if rec is None:
        if ok:                                          # checked the newest list: this token really does not exist
            st.session_state["cookie_cmd"] = ("clear",)
        return False
    try:
        users = load_users()
    except Exception:
        return False                                    # cannot check now: keep the token, try again next time
    u = users.get(rec["user"])
    if rec.get("exp", 0) < now or not u or not u.get("active", True) or rec.get("pw", "") != u.get("pw_changed", ""):
        _modify_tokens(lambda d: (d.pop(h, None), d)[1])
        st.session_state["cookie_cmd"] = ("clear",)
        return False
    st.session_state.update({"user": rec["user"], "role": u["role"], "login_time": now,
                             "must_change": bool(u.get("must_change"))})
    st.session_state["cookie_cmd"] = ("set", token, rec["user"])    # refresh the phone's cookie (iPhone/iPad Safari drops old ones)
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
        if time.time() - st.session_state.get("_users_ok_at", 0) < 3600:   # checked fine less than 1 h ago: stay logged in
            st.warning("Account storage is not reachable right now; you stay logged in. Saving may fail until it is back.")
            return True
        st.error("Cannot verify account access. Please retry when account storage is available.")
        return False
    st.session_state["_users_ok_at"] = time.time()
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


# ===== LANDING PAGE (paste ABOVE def render_login) =====
import streamlit.components.v1 as components

LANDING_HEIGHT = 520          # one-screen poster cover; raise it if the cover is cut off

LANDING_HTML = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Inter:wght@400;600;700;800&family=Noto+Sans+Khmer:wght@400;700&display=swap">
<style>
*{box-sizing:border-box}
:root{--ink:#1E2328;--muted:#6B7280;--line:#E6E0D6;--accent:#B3261E;--soft:#FBEAE8}
body{margin:0;background:transparent;color:var(--ink);font-family:'Inter','Noto Sans Khmer',system-ui,sans-serif;line-height:1.4}
.wrap{max-width:1180px;margin:0 auto;padding:8px 8px 20px}
header{display:flex;flex-wrap:wrap;align-items:center;justify-content:space-between;gap:12px;padding:8px 0 28px}
.brand{display:flex;align-items:center;gap:10px;font-weight:700;font-size:17px}
.dot{width:30px;height:30px;border-radius:9px;background:var(--accent);color:#fff;display:grid;place-items:center;font-size:16px}
.hint{padding:8px 16px;border-radius:999px;border:1px solid var(--line);background:#fff;color:var(--muted);font-weight:600;font-size:14px}
.tag{display:inline-block;padding:5px 12px;border-radius:999px;background:var(--soft);color:var(--accent);font-weight:700;font-size:13px;margin-bottom:16px}
h1{margin:0 0 14px;font-size:clamp(34px,6.2vw,72px);line-height:1.02;letter-spacing:-.035em;font-weight:800}
h1 span{color:var(--accent)}
.lead{margin:0 0 26px;font-size:clamp(16px,1.7vw,19px);color:var(--muted);max-width:600px}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:12px}
.card{background:#fff;border:1px solid var(--line);border-radius:14px;padding:14px 16px;box-shadow:0 1px 2px rgba(30,35,40,.05),0 4px 14px rgba(30,35,40,.05)}
.card b{display:block;font-size:15px;margin-top:6px}
.card small{color:var(--muted);font-size:13px}
.ic{font-size:20px}
</style>
</head>
<body>
<div class="wrap">
  <header>
    <div class="brand"><span class="dot">包</span>នំប៉ាវហុងកុង Supply Chain Hub</div>
    <span class="hint">Log in below &darr;</span>
  </header>
  <span class="tag">Team only</span>
  <h1>Pack it. Send it. <span>Track it.</span></h1>
  <p class="lead">One place for packing, delivery, orders and customer follow-ups. Everyone sees the same day.</p>
  <div class="grid">
    <div class="card"><span class="ic">📦</span><b>Packing</b><small>Who packed what, live</small></div>
    <div class="card"><span class="ic">🚚</span><b>Delivery</b><small>Sent cases &amp; expenses</small></div>
    <div class="card"><span class="ic">📝</span><b>Sale orders</b><small>Typed once, synced</small></div>
    <div class="card"><span class="ic">📊</span><b>Dashboard</b><small>Status of every customer</small></div>
    <div class="card"><span class="ic">🎯</span><b>Sales insights</b><small>Habits, care, data check</small></div>
  </div>
</div>
</body>
</html>"""


def render_landing():
    """Shows the home page. Call it as the first line inside render_login()."""
    components.html(LANDING_HTML, height=LANDING_HEIGHT, scrolling=True)
# ===== END LANDING PAGE =====


def render_login():
    render_landing()
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


def pull(path, force=False, max_age=30.0):
    """Makes the local working copy equal to Dropbox (cheap: only downloads when the file changed)."""
    if not USE_DROPBOX:
        return
    S, name = _sync_state(), os.path.basename(path)
    if not force:
        if time.time() - S["last_pull"].get(path, 0) < max_age:
            return
        try:
            entry = _remote_listing().get(name.lower())
        except Exception:
            entry = None
        if entry is not None:
            with S["lock"]:
                if S["rev"].get(path) == entry["rev"] and os.path.exists(path):
                    S["last_pull"][path] = time.time()
                    return
                downloaded, res = _dbx().files_download(_rpath(name))
                _write_atomic(path, res.content)
                S["rev"][path] = downloaded.rev
                S["last_pull"][path] = time.time()
            return
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
    try:                                       # our own save: the folder list now knows the new version
        state = _remote_list_state()
        with state["lock"]:
            e = state["entries"].get(name.lower())
            state["entries"][name.lower()] = {**(e or {"name": name, "mtime": time.time()}), "rev": md.rev,
                                              "hash": getattr(md, "content_hash", None) or md.rev}
    except Exception:
        pass


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


REMOTE_LIST_EVERY_S = 12         # the Dropbox folder list is refreshed in the background this often
REMOTE_LIST_MAX_AGE_S = 60       # an older list is never trusted: the page then asks Dropbox directly


@st.cache_resource(show_spinner=False)
def _remote_list_state():
    return {"entries": {}, "t": 0.0, "lock": threading.Lock(), "thread": None, "used": 0.0}


def _fetch_remote_folder(dbx):
    out = {}
    res = dbx.files_list_folder(DROPBOX_FOLDER)
    while True:
        for e in res.entries:
            if hasattr(e, "rev"):
                out[e.name.lower()] = {"name": e.name, "rev": e.rev,
                                       "hash": getattr(e, "content_hash", None) or e.rev,
                                       "mtime": e.server_modified.replace(tzinfo=timezone.utc).timestamp()}
        if not res.has_more:
            break
        res = dbx.files_list_folder_continue(res.cursor)
    return out


def _remote_list_worker(state, dbx):
    """One background thread per server: keeps the folder list fresh so page clicks never wait for Dropbox."""
    while time.time() - state["used"] < 900:            # stop after 15 min without visitors
        time.sleep(REMOTE_LIST_EVERY_S)
        try:
            entries = _fetch_remote_folder(dbx)
            with state["lock"]:
                state["entries"], state["t"] = entries, time.time()
        except Exception:
            pass
    with state["lock"]:
        state["thread"] = None


def _remote_listing():
    """{lower-case file name: info} for the Dropbox folder. Instant after the first call."""
    state = _remote_list_state()
    state["used"] = time.time()
    with state["lock"]:
        fresh = time.time() - state["t"] < REMOTE_LIST_MAX_AGE_S
        alive = state["thread"] is not None and state["thread"].is_alive()
    if not fresh:
        entries = _fetch_remote_folder(_dbx())
        with state["lock"]:
            state["entries"], state["t"] = entries, time.time()
    if not alive:
        with state["lock"]:
            if state["thread"] is None or not state["thread"].is_alive():
                th = threading.Thread(target=_remote_list_worker, args=(state, _dbx()), daemon=True, name="dropbox-list")
                state["thread"] = th
                th.start()
    return state["entries"]


def _remote_listing_forget():
    state = _remote_list_state()
    with state["lock"]:
        state["t"] = 0.0


def _remote_entry(name):
    return _remote_listing().get(str(name).lower())


def _list_remote_folder(_token=0):
    return list(_remote_listing().values())


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
        _remote_listing_forget()
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


def prune_backups(dbx=None):
    removed = 0
    try:
        if USE_DROPBOX:
            dbx = dbx or _dbx()
            res = dbx.files_list_folder(_remote_backup_dir())
            ents = list(res.entries)
            while res.has_more:
                res = dbx.files_list_folder_continue(res.cursor)
                ents += list(res.entries)
            now = datetime.now(timezone.utc).timestamp()
            for e in ents:
                if not hasattr(e, "rev"):
                    continue
                age_days = (now - e.server_modified.replace(tzinfo=timezone.utc).timestamp()) / 86400
                extra = re.match(r"^\d{4}-\d{2}-\d{2}_\d{6}_", e.name)
                if age_days > 30 or (extra and age_days > 7):
                    dbx.files_delete_v2(f"{_remote_backup_dir()}/{e.name}")
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


_BACKUP_FILES = lambda: (DATA_FILE, PACKING_FILE, ASSIGN_FILE, HOLD_FILE, ORDERS_FILE, USERS_FILE, LOCATIONS_FILE,
                         MAP_REGISTRY_FILE, CALLS_FILE, SI_ALIAS_FILE, VISITS_FILE, VISIT_ZONE_FILE, VISIT_PIN_FILE, LEADS_FILE,
                         os.path.join(DATA_DIR, "media_shoots.csv"),
                         os.path.join(DATA_DIR, "visit_settings.json"))


def daily_backup_once(day_str):
    """Retry failed backups, cache only success, and protect accounts/locations too.
    Dropbox mode: runs in the background (about 30 Dropbox requests) so the first click of the day never waits."""
    state = _sync_state()
    if not USE_DROPBOX:
        return _daily_backup_local(state, day_str)
    with state["lock"]:
        if state.get("backup_day") != day_str:
            state["backup_day"] = day_str
            state["backup_done"] = set()
            state["backup_failures"] = []
            state["backup_try"] = 0.0
        done_all = state.get("backup_ok_day") == day_str
        running = state.get("backup_running", False)
        recent = time.time() - state.get("backup_try", 0.0) < 600           # failed ones are retried every 10 min
        if done_all or running or recent:
            return list(state.get("backup_failures", []))
        state["backup_running"], state["backup_try"] = True, time.time()
    try:
        dbx = _dbx()
        names = {k: v for k, v in _remote_listing().items()}
    except Exception as e:
        with state["lock"]:
            state["backup_running"] = False
            state["backup_failures"] = [f"Cannot access backup folder: {str(e)[:120]}"]
        return list(state["backup_failures"])
    threading.Thread(target=_daily_backup_dropbox, args=(state, dbx, names, day_str), daemon=True,
                     name="daily-backup").start()
    return list(state.get("backup_failures", []))


def _daily_backup_dropbox(state, dbx, remote_names, day_str):
    failures = []
    try:
        try:
            dbx.files_create_folder_v2(_remote_backup_dir())
        except Exception as e:
            if not _is_conflict(e):
                raise
        for path in _BACKUP_FILES():
            base = os.path.basename(path)
            with state["lock"]:
                if path in state.setdefault("backup_done", set()):
                    continue
            if base.lower() not in remote_names:
                continue
            dest = f"{_remote_backup_dir()}/{day_str}_{base}"
            try:
                try:
                    dbx.files_get_metadata(dest)
                except Exception as e:
                    if not _is_not_found(e):
                        raise
                    dbx.files_copy_v2(_rpath(base), dest)
                with state["lock"]:
                    state["backup_done"].add(path)
            except Exception as e:
                failures.append(f"{base}: {str(e)[:160]}")
        if not failures and state.get("pruned_day") != day_str:
            prune_backups(dbx)
            state["pruned_day"] = day_str
    except Exception as e:
        failures.append(f"Cannot access backup folder: {str(e)[:120]}")
    with state["lock"]:
        state["backup_failures"] = failures
        state["backup_running"] = False
        if not failures:
            state["backup_ok_day"] = day_str


def _daily_backup_local(state, day_str):
    failures = []
    with state["lock"]:
        if state.get("backup_day") != day_str:
            state["backup_day"] = day_str
            state["backup_done"] = set()
        done = state.setdefault("backup_done", set())
        try:
            os.makedirs(BACKUP_DIR, exist_ok=True)
        except OSError as e:
            return [f"Cannot access backup folder: {str(e)[:120]}"]
        for path in _BACKUP_FILES():
            if path in done:
                continue
            base = os.path.basename(path)
            try:
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


@st.cache_data(show_spinner=False, max_entries=32)
def _csv_cached(path, mtime_ns, size, cols):
    return _csv_read(path, list(cols))


def read_raw(path, cols, max_age=30.0):
    """Cleaned DataFrame of a CSV (with hidden `_dt` datetime column). Fast: cached until the file changes.
    max_age: seconds before Dropbox is asked again whether the file changed."""
    if USE_DROPBOX:
        try:
            pull(path, max_age=max_age)                  # cheap check, downloads only if Dropbox changed
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
                pull(path, force=attempt > 0, max_age=10.0)      # first try: no extra Dropbox call; a conflict forces a fresh copy
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
                pull(path, force=attempt > 0, max_age=10.0)      # first try: no extra Dropbox call; a conflict forces a fresh copy
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
            if s.upper().startswith(pre) and len(s) > len(pre) and not CUSTOMER_CODE_RE.match(s):
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
        cases_col = inv_col = rem_col = pay_col = sales_col = None
        bun_cols, top_rows, hdr_i = {}, [], None            # bun_cols = {"N1": column index, ...}
        for r_i, row in enumerate(ws.iter_rows(values_only=True)):
            if r_i < 8:
                top_rows.append(row)
            if r_i < 15 and not bun_cols:
                found = {str(v).strip(): c_i for c_i, v in enumerate(row) if v is not None and BUN_CODE_RE.match(str(v).strip())}
                if len(found) >= 3:
                    bun_cols, hdr_i = found, r_i
            if r_i < 15 and sales_col is None:
                for c_i, v in enumerate(row):
                    text = str(v or '').replace('\n', '').replace(' ', '')
                    if 'ថ្លៃលក់' in text and 'រៀល' in text:
                        sales_col = c_i
                        break
            if r_i < 15 and pay_col is None:
                for c_i, v in enumerate(row):
                    if v is not None and JOURNAL_PAY_HEADER in str(v):
                        pay_col = c_i
                        break
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
            buns = [row[ci] if ci < len(row) else None for ci in bun_cols.values()]
            pay = str(row[pay_col]).strip().upper() if (pay_col is not None and pay_col < len(row) and row[pay_col] is not None) else ""
            actual_sales = row[sales_col] if sales_col is not None and sales_col < len(row) else None
            raw_rows.append((row[0], name, qty, inv, rem or "-", buns, pay, actual_sales, r_i + 1))
    finally:
        wb.close()
    # bun names (row above the header), sell price and cost per piece (rows labelled SELL/PCS and NET/PCS)
    bun_info = {"codes": list(bun_cols), "names": {}, "sell": {}, "cost": {}}
    if bun_cols and hdr_i is not None:
        def _n(v):
            try:
                return float(v)
            except Exception:
                return None
        if hdr_i >= 1 and hdr_i - 1 < len(top_rows):
            for code, ci in bun_cols.items():
                v = top_rows[hdr_i - 1][ci] if ci < len(top_rows[hdr_i - 1]) else None
                bun_info["names"][code] = str(v).strip() if v is not None else ""
        for row in top_rows[:hdr_i]:
            label = " ".join(str(v).upper() for v in row if isinstance(v, str))
            key = "sell" if "SELL/PCS" in label else ("cost" if "NET/PCS" in label else None)
            if key:
                for code, ci in bun_cols.items():
                    bun_info[key][code] = _n(row[ci]) if ci < len(row) else None

    months = Counter((r[0].year, r[0].month) for r in raw_rows if isinstance(r[0], datetime))
    dominant = months.most_common(1)[0][0] if months else None
    out, skipped = [], []
    for v, name, qty, inv, rem, buns, pay, actual_sales, xl_row in raw_rows:
        d = cell_to_date(v, dominant)
        pcs = float(sum(x for x in pd.to_numeric(pd.Series(buns, dtype=object), errors="coerce").fillna(0)))
        sales = pd.to_numeric(actual_sales, errors="coerce")
        if d is None:
            # A row with a customer AND buns / an invoice but no readable date is real data the app cannot use.
            real_invoice = bool(re.match(r"^" + INVOICE_PREFIX + r"\d", str(inv), re.I))
            if (pcs > 0 or real_invoice) and (pay or real_invoice):
                skipped.append({"Excel row": xl_row, "Date cell": _cell_text(v) or "(empty)", "Customer": name,
                                "Invoice": inv, "Bun pcs": int(pcs), "Payment": pay or "-"})
            continue
        try:
            q = pd.to_numeric(qty, errors="coerce")
            q = None if pd.isna(q) else float(q)
        except Exception:
            q = None
        reason = free_reason(pay, rem, pcs, sales)
        out.append((d, name, q, inv, rem, bool(reason), sales, pay or "-", reason, xl_row, *buns))
    journal = pd.DataFrame(out, columns=["Date", "Customer", "Cases", "Invoice", "Remark", "FOC", "SalesActual",
                                         "Pay", "FreeReason", "ExcelRow"] + list(bun_cols))
    for _c in bun_cols:
        journal[_c] = pd.to_numeric(journal[_c], errors="coerce").fillna(0)
    journal["Cases"] = pd.to_numeric(journal["Cases"], errors="coerce")
    return {"customers": customers, "journal": journal, "skipped": skipped, "cases_col_found": cases_col is not None,
            "invoice_col_found": inv_col is not None, "areas": areas, "area_col_found": bool(areas),
            "buns": bun_info}


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
            pull(path)                       # uses the background folder list: no wait unless the file changed
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
            _remote_listing()
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
        for package in ("openpyxl",) + (("dropbox",) if USE_DROPBOX else ()):
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


POSTER_CSS = r"""
<style>
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&family=Noto+Sans+Khmer:wght@400;600;700&display=swap');
:root {
  --bg:#F7F4EE; --card:#FFFFFF; --ink:#1E2328; --muted:#6B7280; --line:#E6E0D6;
  --accent:#B3261E; --accent-soft:#FBEAE8; --ok:#2E7D4F; --ok-soft:#E5F4EA; --shadow:0 1px 2px rgba(30,35,40,.06), 0 4px 14px rgba(30,35,40,.06);
}
.stApp {background: var(--bg); color: var(--ink); color-scheme: light;
    font-family: 'Inter','Noto Sans Khmer',system-ui,-apple-system,sans-serif;}
.stApp button, .stApp input, .stApp textarea {font-family: inherit;}
header[data-testid="stHeader"] {background: transparent;}
::selection {background: var(--accent-soft); color: var(--ink);}

/* text */
.stApp p, .stApp label, .stApp li, .stApp h1, .stApp h2, .stApp h3, .stApp h4, .stApp h5, .stApp h6,
[data-testid="stWidgetLabel"] p, [data-testid="stMetricValue"] {color: var(--ink) !important;}
[data-testid="stCaptionContainer"], [data-testid="stCaptionContainer"] p, [data-testid="stMetricLabel"] p {color: var(--muted) !important;}
.stApp h1 {font-weight: 700; letter-spacing: -0.02em;}
.stApp h2, .stApp h3, .stApp h4 {font-weight: 650; letter-spacing: -0.01em;}
.stApp a {color: var(--accent); text-decoration: none; font-weight: 600;}
.stApp a:hover {text-decoration: underline;}

/* buttons */
.stButton > button, .stDownloadButton > button, div[data-testid="stFormSubmitButton"] > button, .stLinkButton > a {
    background: var(--card); color: var(--ink); border: 1px solid var(--line); border-radius: 10px;
    box-shadow: 0 1px 2px rgba(30,35,40,.05); font-weight: 600; transition: background .15s, border-color .15s, box-shadow .15s;}
.stButton > button:hover, .stDownloadButton > button:hover, div[data-testid="stFormSubmitButton"] > button:hover, .stLinkButton > a:hover {
    border-color: var(--accent); color: var(--accent); background: var(--card); box-shadow: var(--shadow);}
.stButton > button:active, .stDownloadButton > button:active {transform: translateY(1px);}
.stApp button[kind="primary"], .stApp button[data-testid="stBaseButton-primary"],
.stApp button[data-testid="stBaseButton-primaryFormSubmit"] {background: var(--accent); border-color: var(--accent); color: #FFFFFF;}
.stApp button[kind="primary"]:hover, .stApp button[data-testid="stBaseButton-primary"]:hover,
.stApp button[data-testid="stBaseButton-primaryFormSubmit"]:hover {background: #951F18; border-color: #951F18; color:#FFFFFF;}
.stApp button[kind="primary"] p, .stApp button[data-testid="stBaseButton-primary"] p,
.stApp button[data-testid="stBaseButton-primaryFormSubmit"] p {color: #FFFFFF !important;}
.stApp button:disabled {opacity: .45;}

/* inputs */
[data-baseweb="input"], [data-baseweb="textarea"], [data-baseweb="select"] > div {
    background: var(--card) !important; border: 1px solid var(--line) !important; border-radius: 10px !important;}
[data-baseweb="input"]:focus-within, [data-baseweb="textarea"]:focus-within, [data-baseweb="select"] > div:focus-within {
    border-color: var(--accent) !important; box-shadow: 0 0 0 3px var(--accent-soft) !important;}
[data-baseweb="input"] > div, [data-baseweb="base-input"] {background: transparent !important; border: 0 !important;}
.stApp input, .stApp textarea {color: var(--ink) !important; -webkit-text-fill-color: var(--ink) !important;}
[data-baseweb="select"] div, [data-baseweb="select"] span {color: var(--ink);}
[data-baseweb="tag"] {background: var(--accent-soft) !important; border-radius: 999px !important;}
[data-baseweb="tag"] span, [data-baseweb="tag"] svg {color: var(--accent) !important; fill: var(--accent) !important;}
[data-baseweb="popover"] > div {background: var(--card) !important; border: 1px solid var(--line); border-radius: 12px; box-shadow: var(--shadow);}
[data-baseweb="popover"] li, [data-baseweb="popover"] li * {color: var(--ink) !important; background: transparent;}
[data-baseweb="popover"] li:hover {background: var(--bg) !important;}

/* section chips (radio groups = navigation) */
div[role="radiogroup"] {gap: 2px 0;}
label[data-baseweb="radio"] {background: var(--card); border: 1px solid var(--line); border-radius: 999px;
    padding: 6px 14px; margin: 3px 6px 3px 0; cursor: pointer; transition: border-color .15s, background .15s;}
label[data-baseweb="radio"]:hover {border-color: var(--accent);}
label[data-baseweb="radio"] > div:first-child {display: none;}
label[data-baseweb="radio"] p {font-weight: 600; font-size: .92rem;}
label[data-baseweb="radio"]:has(input:checked) {background: var(--ink); border-color: var(--ink);}
label[data-baseweb="radio"]:has(input:checked) *, label[data-baseweb="radio"]:has(input:checked) p {color: #FFFFFF !important;}

/* tabs */
button[data-baseweb="tab"] {background: transparent; border-radius: 8px 8px 0 0; padding: 8px 14px; height: auto;}
button[data-baseweb="tab"] p {font-weight: 600; color: var(--muted) !important;}
button[data-baseweb="tab"][aria-selected="true"] p {color: var(--ink) !important;}
[data-baseweb="tab-highlight"] {background: var(--accent) !important; height: 3px;}
[data-baseweb="tab-border"] {background: var(--line) !important;}

/* cards: forms, expanders, metrics, alerts, tables, sidebar */
[data-testid="stForm"] {background: var(--card); border: 1px solid var(--line); border-radius: 16px;
    box-shadow: var(--shadow); padding: 20px;}
[data-testid="stExpander"] {background: var(--card); border: 1px solid var(--line); border-radius: 14px; box-shadow: var(--shadow); overflow: hidden;}
[data-testid="stExpander"] details, [data-testid="stExpander"] summary {background: transparent; border: 0;}
[data-testid="stExpander"] summary p {font-weight: 600;}
div[data-testid="stMetric"] {background: var(--card); border: 1px solid var(--line); border-left: 4px solid var(--accent);
    border-radius: 12px; box-shadow: var(--shadow); padding: 12px 16px;}
[data-testid="stMetricValue"] {font-weight: 700; font-size: 1.6rem;}
[data-testid="stAlert"] {border-radius: 12px; border: 1px solid var(--line);}
[data-testid="stDataFrame"] {border: 1px solid var(--line); border-radius: 12px; overflow: hidden; background: var(--card); box-shadow: var(--shadow);}
section[data-testid="stSidebar"] {background: var(--card); border-right: 1px solid var(--line);}
[data-testid="stVerticalBlockBorderWrapper"]:has(> div > [data-testid="stVerticalBlock"]) {border-radius: 14px;}
hr {border-color: var(--line) !important;}

/* the app's own cards and pills */
.hk-card {background: var(--card); border: 1px solid var(--line); border-radius: 14px; box-shadow: var(--shadow);}
.hk-pill {background: var(--card); border: 1px solid var(--line); font-weight: 600; color: var(--ink);}
.hk-badge {font-weight: 600;}
.hk-group {border-bottom: 2px solid var(--line); color: var(--ink);}
.hk-sub {color: var(--muted); opacity: 1;}

@media (max-width: 640px) {
  label[data-baseweb="radio"] {padding: 5px 11px; margin-right: 4px;}
  [data-testid="stForm"] {padding: 14px;}
  [data-testid="stMetricValue"] {font-size: 1.3rem;}
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
    if st.checkbox("Prepare today's downloadable checklist", key="prepare_packing_checklist"):
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
    packing_mode = st.radio("Packing method", ["📋 Quick tick list", "📤 Upload a file", "✍️ One customer"],
                            horizontal=True, key="packing_method")
    if packing_mode.startswith("📋"):
        _ticklist_tab()
    elif packing_mode.startswith("📤"):
        _upload_tab()
    else:
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
    if not has_permission("edit") or not has_permission("tasks"):
        st.warning("Editing delivery expenses is disabled for your account.")
        return
    is_admin = current_role() == "admin"
    st.caption("Fill in expenses for deliveries you already sent. Self-delivered orders need no transport expense unless a taxi station is recorded. Tick **Done** for each row you finish, then save.")
    with st.form("expense_filters"):
        c1, c2 = st.columns(2)
        scope = c1.radio("Show", ["Today", "Last 7 days", "All waiting"], horizontal=True, key="exp_scope")
        who = me
        if is_admin:
            pick = c2.selectbox("Handler", ["(everyone)"] + DELIVERY_HANDLERS, key="exp_who")
            who = None if pick == "(everyone)" else pick
        if st.form_submit_button("Apply expense filter"):
            _reset_draft("expenses", str((who, scope)))
    if not is_admin and me == "-- Select Staff --":
        st.info("Choose your name at the top first.")
        return
    df = pending_expense_df(who, scope)
    if df.empty and not _has_editor_draft("expenses", str((who, scope))):
        st.success("Nothing is waiting for expenses. 🎉")
        return
    st.info(f"⏳ {len(df)} deliveries are waiting for expenses.")
    rows = [{"Done ✅": False, "Customer": r["Customer"], "When": str(r["Date"])[5:16], "Via": r["Local_Driver"],
             "Taxi station": "" if r["Taxi_Station"] in ("-", "") else r["Taxi_Station"],
             "Phnom Penh ៛": int(r["Phnom_Penh_Expense"]), "Taxi ៛": int(r["Taxi_Expense"]),
             "By": r["Handled_By"], "Date": r["Date"]} for r in df.to_dict("records")]
    draft_scope = str((who, scope))
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
                m = (frame["Date"].astype(str) == dt) & (frame["Customer"] == cust) & (frame["Handled_By"] == by) & (frame["Expense_Status"] == "Pending")
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
    step = st.radio("Delivery step", ["1️⃣ Choose my customers", "2️⃣ Send", "3️⃣ Fill my expenses",
                                    "✍️ One customer", "📊 Today's log"], horizontal=True, key="delivery_step")
    need_name = me == "-- Select Staff --"
    if step.startswith(("1️⃣", "2️⃣")) and need_name:
        st.info("Choose your name at the top first.")
    elif step.startswith("1️⃣"):
        _claim_tab(me, ctx)
    elif step.startswith("2️⃣"):
        _send_tab(me, ctx)
    elif step.startswith("3️⃣"):
        _expense_tab(me)
    elif step.startswith("✍️"):
        st.caption("Expenses are optional now. Save this form before changing steps.")
        dispatch_form("expense_form")
    else:
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


DASH_COLUMNS = ["🔥", "Customer", "In Master", "Area", "Province", "Region", "Invoice", "Status", "កេស", "Buns", "Buns total", "Packed Cases", "Packed Note", "Prepared By",
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
        sub = journal_plus_orders(snap, selected_date)
        _bc = bun_codes(snap)
        for name, g in sub.groupby("Customer", sort=False):
            tot = g["Cases"].sum(min_count=1)
            _bsum = g[_bc].sum() if _bc else None
            scheduled[name] = {"cases": int(tot) if pd.notna(tot) else None,
                               "site_only": bool(g["_site"].all()),
                               "buns": bun_text(_bsum, _bc) if _bsum is not None else "",
                               "buns_total": int(_bsum.sum()) if _bsum is not None else 0,
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
            "Buns": (info.get("buns", "") if info else ""),
            "Buns total": (info.get("buns_total", 0) if info else 0),
            "Moved/Cancel Reason": (f"{h['reason']} (by {h['by']})" if h else ""),
            "Note": s["note"] if s else "-", "Time": s["time"] if s else "-",
            "Source": ("📝 Site order" if info.get("site_only") else "Journal") if info else "⚠️ Not in journal",
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
COMPACT_COLUMNS = ["🔥", "Customer", "In Master", "Province", "Status", "កេស", "Buns", "Packed Cases", "Sent Cases", "Left to send", "Verified By", "Taxi Station", "Taxi No.", "Assigned To", "Invoice", "Map link", "Directions", "Map status"]
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
            f"<div class='hk-nums'><span>កេស <b>{ordered}</b></span><span>🥐 {_e(r.get('Buns') or '-')}</span><span>📦 <b>{int(r['Packed Cases'])}</b>{' ✏️' if r.get('Packed Note') else ''}{prep}</span>"
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
    if not st.checkbox("Prepare Excel report (takes a few seconds)", key="rep_prep_xl"):
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
    _bun_panel(df_scope, selected_date, mobile)
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
        if can_reports and not st.checkbox("Prepare Excel report", key="dash_prep_xl"):
            st.caption("Tick to prepare the Excel report.")
        elif can_reports:
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
    if p_row.get("Buns"):
        st.success(f"🥐 Buns ordered (journal): {p_row['Buns']}  =  {int(p_row['Buns total'])} pcs")
    if p_row["Journal Note"] not in ("-", ""):
        st.warning(f"📌 Journal note: {p_row['Journal Note']}")
    pack_default = max((ordered_n or 0) - packed_n, 0) or 1
    send_default = (target_n - sent_n) if (target_n - sent_n) > 0 else 1

    st.markdown(f"#### 🚚 Final sent: **{sent_n} កេស**  ·  ordered {ordered_n if ordered_n is not None else '-'}  ·  "
                f"packed {packed_n}  ·  left to send **{max(target_n - sent_n, 0)}**"
                + (f"   \n✏️ {p_row['Sent Note']}" if p_row["Sent Note"] else "")
                + (f"   \n✏️ {p_row['Packed Note']}" if p_row["Packed Note"] else ""))
    _upd_steps = ["📦 Step 1: Packing (who prepared the buns)", "🚚 Step 2: Send (who delivered + verify កេស)",
                  "✏️ Edit final packed / sent", "📅 Move to tomorrow / ❌ Cancel"]
    _upd_pick = st.radio("Update step", _upd_steps, horizontal=True, key=f"upd_step_{selected}")
    t_pack, t_send, t_final, t_hold = (_upd_pick == name for name in _upd_steps)           # only the chosen one is built
    if t_pack:
        packing_form(f"dash_pack_{selected}_{pack_default}", fixed_customer=selected, default_cases=pack_default)
    if t_send:
        st.caption("Check the កេស number (you can edit it), choose who verified it, then save.")
        dispatch_form(f"dash_send_{selected}_{send_default}", fixed_customer=selected,
                      default_cases=send_default, verify=True)
    if t_final:
        _final_panel(selected, p_row)
    if t_hold:
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
    j = journal_plus_orders(snap, day)
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


def site_orders_df(day=None, status=("Active",)):
    """Orders typed on the site, as a DataFrame (one day, or all days)."""
    df = read_raw(ORDERS_FILE, ORDER_COLS)
    if df.empty:
        return df
    df = df[df["Status"].isin(status)]
    if day is not None:
        df = rows_for_day(df, day)
    return df


def journal_plus_orders(snap, day=None):
    """The journal rows (one day or all) + the active orders typed on the site, in the same shape.
    A site order matching customer, invoice and date in the journal is not counted twice."""
    j = snap["journal"]
    codes = bun_codes(snap)
    j = j if day is None else j[j["Date"] == day]
    j = j.assign(_site=False)
    try:
        o = site_orders_df(day)
    except Exception:
        return j
    if o.empty:
        return j
    def order_keys(frame, dates):
        return list(zip(frame["Customer"].map(norm_name),
                        frame["Invoice"].fillna("").astype(str).str.strip().str.upper(),
                        pd.to_datetime(dates, errors="coerce").dt.strftime("%Y-%m-%d")))
    in_journal = {key for key in order_keys(snap["journal"], snap["journal"]["Date"]) if key[1] not in ("", "-")}
    o = o.loc[[key not in in_journal for key in order_keys(o, o["_dt"])]]
    if o.empty:
        return j
    site = pd.DataFrame({"Date": o["_dt"].dt.date, "Customer": o["Customer"], "Cases": o["Cases"].astype(float),
                         "Invoice": o["Invoice"], "Remark": o["Remark"], "FOC": o["Payment"].str.upper().eq("FOC"), "_site": True})
    for c in codes:
        site[c] = o[c].astype(float) if c in o.columns else 0.0
    return pd.concat([j, site[[c for c in j.columns if c in site.columns]]], ignore_index=True).fillna({"FOC": False})


def bun_codes(snap):
    return list((snap or {}).get("buns", {}).get("codes", []))


def bun_text(row, codes):
    """'N1 36 · N2 96' for one customer."""
    return " · ".join(f"{c} {int(row[c])}" for c in codes if row.get(c, 0) > 0)


def bun_table_by_type(j, snap):
    """Per bun type: pieces paid / FOC / total and sales in riel for the journal rows in j."""
    info, rows = snap["buns"], []
    for c in info["codes"]:
        paid, foc = int(j.loc[~j["FOC"], c].sum()), int(j.loc[j["FOC"], c].sum())
        sell = info["sell"].get(c) or 0
        rows.append({"Code": c, "Bun": info["names"].get(c, ""), "Sell/pcs ៛": int(sell), "Paid pcs": paid, "FOC pcs": foc,
                     "Total pcs": paid + foc, "Sales ៛": int(paid * sell)})
    out = pd.DataFrame(rows)
    if not out.empty:
        tot = {"Code": "TOTAL", "Bun": "", "Sell/pcs ៛": "", "Paid pcs": int(out["Paid pcs"].sum()), "FOC pcs": int(out["FOC pcs"].sum()),
               "Total pcs": int(out["Total pcs"].sum()), "Sales ៛": int(out["Sales ៛"].sum())}
        out = pd.concat([out, pd.DataFrame([tot])], ignore_index=True)
    return out


def _bun_panel(df_scope, selected_date, mobile=False):
    """Review of the number of buns (N1-N43) sold: per type, and per customer."""
    snap, _, _, _ = current_snapshot()
    codes = bun_codes(snap)
    if not codes:
        return
    with st.expander("🥐 Bun sales: number of buns N1-N43 (for review)", expanded=False):
        span = st.radio("Show", ["Selected day", "Whole month in the journal"], horizontal=True, key="bun_span")
        j = journal_plus_orders(snap, selected_date if span == "Selected day" else None)
        if span == "Selected day":
            names_in_view = set(df_scope["Customer"])           # follows the Phnom Penh / Province choice above
            j = j[j["Customer"].isin(names_in_view)]
        if j.empty or float(j[codes].to_numpy().sum()) == 0:
            st.info("No bun quantities (N1-N43) in the journal for this selection yet.")
            return
        by_type = bun_table_by_type(j, snap)
        tot = by_type.iloc[-1]
        m1, m2, m3, m4 = st.columns(4)
        kpi(m1, "Buns total (pcs)", f"{int(tot['Total pcs']):,}")
        kpi(m2, "Paid pcs", f"{int(tot['Paid pcs']):,}")
        kpi(m3, "FOC (free) pcs", f"{int(tot['FOC pcs']):,}")
        kpi(m4, "Sales (៛)", f"{int(tot['Sales ៛']):,}")
        st.markdown("**By bun type**")
        show_df(by_type)
        try:
            st.bar_chart(by_type.iloc[:-1].set_index("Code")["Total pcs"])
        except Exception:
            pass
        st.markdown("**By customer** (pieces of each bun)")
        q = st.text_input("🔎 Search customer", key="bun_q", max_chars=60)
        g = j.groupby("Customer", sort=False)[codes].sum()
        foc_g = j[j["FOC"]].groupby("Customer")[codes].sum().sum(axis=1) if j["FOC"].any() else pd.Series(dtype=float)
        g["Total"] = g[codes].sum(axis=1)
        g["of which FOC"] = foc_g.reindex(g.index).fillna(0)
        g = g[g["Total"] > 0].sort_values("Total", ascending=False).reset_index()
        meta = df_scope.drop_duplicates("Customer").set_index("Customer")[["Province", "Status"]] if not df_scope.empty else None
        if meta is not None and span == "Selected day":
            g.insert(1, "Province", g["Customer"].map(meta["Province"]).fillna("-"))
            g.insert(2, "Status", g["Customer"].map(meta["Status"]).fillna("-"))
        if q.strip():
            for w in q.strip().split():
                g = g[g["Customer"].str.contains(w, case=False, regex=False, na=False)]
        for c in codes + ["Total", "of which FOC"]:
            g[c] = g[c].astype(int)
        st.caption(f"{len(g)} customer(s)")
        show_df(g, height=420)
        buf = io.BytesIO()
        with pd.ExcelWriter(buf, engine="openpyxl") as w:
            by_type.to_excel(w, index=False, sheet_name="By bun type")
            g.to_excel(w, index=False, sheet_name="By customer")
        st.download_button("📥 Download bun sales (Excel)", data=buf.getvalue(), file_name=f"Bun_Sales_{selected_date}.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", key="bun_dl")


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


# ==========================================
# TAB: SALE ORDER INPUT (sales types the order here; it is saved to Dropbox as sale_orders.csv)
# ==========================================
JOURNAL_EXPORT_HEADERS = (["កាលបរិច្ឆេទ", "ឈ្មោះអតិថិជន", "Column2", "NO", "ចំណាំ", "វិក្កយប័ត្រ"] + ORDER_BUNS +
                          ["Column1", "កេស", "សេវាដឹក", "ថ្លៃដើម", "ថ្លៃលក់ជារៀល", "ថ្លៃលក់ជាដុល្លា", "ចំណេញដុល", "ការទូទាត់"])


def build_orders_journal_export(df):
    """Excel in the same column order as the DAILY SALE JOUNAL sheet (A..AA). Formula / price columns are left empty:
    paste with 'Paste special > Skip blanks' so the journal's own formulas stay."""
    rows = []
    for r in df.sort_values(["_dt", "Customer"]).to_dict("records"):
        rec = {h: None for h in JOURNAL_EXPORT_HEADERS}
        rec.update({"កាលបរិច្ឆេទ": r["_dt"].date(), "ឈ្មោះអតិថិជន": r["Customer"],
                    "ចំណាំ": None if r["Remark"] in ("-", "") else r["Remark"],
                    "វិក្កយប័ត្រ": None if r["Invoice"] in ("-", "") else r["Invoice"],
                    "កេស": int(r["Cases"]) or None, "ការទូទាត់": r["Payment"]})
        for c in ORDER_BUNS:
            rec[c] = int(r[c]) or None
        rows.append(rec)
    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine="openpyxl", datetime_format="yyyy-mm-dd", date_format="yyyy-mm-dd") as w:
        pd.DataFrame(rows, columns=JOURNAL_EXPORT_HEADERS).to_excel(w, index=False, sheet_name="Orders for journal")
        ws = w.sheets["Orders for journal"]
        ws.freeze_panes = "A2"
        ws.column_dimensions["A"].width = 12
        ws.column_dimensions["B"].width = 34
    return buf.getvalue()


def _order_prices(snap):
    info = (snap or {}).get("buns", {})
    return ({c: info.get("names", {}).get(c, "") for c in ORDER_BUNS}, {c: info.get("sell", {}).get(c) or 0 for c in ORDER_BUNS})


def tab_sale_order():
    if ROLE == "viewer":
        st.info("Your account can only view. Ask Admin if you need to enter orders.")
        return
    snap, _, _, _ = current_snapshot()
    names, sell = _order_prices(snap)
    me = current_user() or "-"
    gen = st.session_state.get("order_gen", 0)
    k = lambda n: f"ord_{n}_{gen}"
    st.markdown("### 📝 Sale order input")
    st.caption("Type the order here. It is saved straight to Dropbox (`sale_orders.csv`), appears on the Live Dashboard at once, "
               "and you can export it later in the journal's column layout.")
    c1, c2 = st.columns([1, 2])
    order_date = c1.date_input("Order date (delivery day)", value=today_kh(), key=k("date"))
    master = get_customer_list()
    choice = c2.selectbox("Customer (type to search)", ["-- Select a customer --", "➕ New customer (type the name below)"] + master, key=k("cust"))
    new_name = ""
    if choice.startswith("➕"):
        new_name = st.text_input("New customer name (same spelling as on the invoice)", max_chars=MAX_TEXT, key=k("new"))
    st.markdown("**Number of buns** (pieces)")
    qty = {}
    cols = st.columns(4)
    for i, c in enumerate(ORDER_BUNS):
        label = f"{c} {names.get(c, '')}" + (f" · ៛{int(sell[c]):,}" if sell.get(c) else "")
        qty[c] = cols[i % 4].number_input(label, min_value=0, max_value=1_000_000, step=1, value=0, key=k("q_" + c))
    pcs = sum(qty.values())
    amount = sum(qty[c] * (sell.get(c) or 0) for c in ORDER_BUNS)
    m1, m2 = st.columns(2)
    kpi(m1, "Total buns (pcs)", f"{pcs:,}")
    kpi(m2, "Amount (៛)", f"{int(amount):,}")
    d1, d2, d3, d4 = st.columns(4)
    cases = d1.number_input("កេស (cases)", min_value=0, max_value=MAX_CASES, step=1, value=0, key=k("cases"))
    pay = d2.selectbox("Payment", ["AR", "FOC"], key=k("pay"), help="FOC = free of charge")
    inv = d3.text_input("Invoice no. (optional)", max_chars=40, key=k("inv"), placeholder="NP312345")
    remark = d4.text_input("Remark (optional)", max_chars=MAX_TEXT, key=k("rem"), placeholder="ប្រញាប់ / 5+1 ...")

    customer = new_name.strip() if choice.startswith("➕") else ("" if choice.startswith("--") else choice)
    customer = re.sub(r"\s+", " ", customer)
    warn_dup = False
    if customer:
        canon = {norm_name(n): n for n in master}
        if norm_name(customer) in canon:
            customer = canon[norm_name(customer)]                 # same name as in the master: use the master spelling
        elif choice.startswith("➕"):
            near = difflib.get_close_matches(customer, master, n=3, cutoff=0.85)
            if near:
                st.warning("⚠️ Looks like an existing customer: " + " / ".join(near) + ". Choose it from the list if it is the same.")
            else:
                st.info("🆕 This customer is not in the Master List yet. The order is saved, and Sales will be asked to add it to the master data.")
        try:
            same = site_orders_df(order_date)
            same = same[(same["Customer"] == customer) & (same[ORDER_BUNS].astype(int).apply(tuple, axis=1) == tuple(qty[c] for c in ORDER_BUNS))]
            warn_dup = pcs > 0 and not same.empty
        except Exception:
            pass
    allow_dup = True
    if warn_dup:
        st.warning("⚠️ The same order (same customer, day and quantities) was already entered. Tick the box to save it again.")
        allow_dup = st.checkbox("Yes, save it again", key=k("dup"))
    if st.button("💾 Save order", type="primary", key=k("save")):
        if not customer:
            st.error("❌ Choose a customer, or type the new customer name.")
        elif pcs <= 0:
            st.error("❌ Enter the number of buns for at least one type.")
        elif not allow_dup:
            st.error("❌ Tick 'Yes, save it again' or change the order.")
        else:
            try:
                now = now_kh()
                row = {"Date": f"{order_date} {now:%H:%M:%S}", "Customer": customer,
                       "OrderID": f"SO-{now:%Y%m%d%H%M%S}-{pysecrets.token_hex(2)}", "Invoice": inv.strip() or "-",
                       "Remark": remark.strip() or "-", "Payment": pay, "Cases": int(cases),
                       "Entered_By": me, "Entered_At": now_str(), "Status": "Active"}
                row.update({c: int(qty[c]) for c in ORDER_BUNS})
                append_row(ORDERS_FILE, row)
                audit("sale_order", f"{customer} | {order_date} | {pcs} pcs")
                st.session_state["order_gen"] = gen + 1
                st.session_state["flash"] = f"Order saved: {customer} | {pcs:,} pcs | ៛{int(amount):,} (synced to Dropbox)" if USE_DROPBOX else \
                    f"Order saved: {customer} | {pcs:,} pcs | ៛{int(amount):,}"
                st.rerun()
            except (RuntimeError, ConflictError) as e:
                st.error(f"❌ {e}")

    # ---- the orders already entered ----
    st.markdown("---")
    st.markdown("#### 📋 Orders entered on the site")
    f1, f2 = st.columns([1, 2])
    view_day = f1.date_input("Show day", value=today_kh(), key="ord_view_day")
    q = f2.text_input("🔎 Search customer / invoice", key="ord_q", max_chars=60)
    try:
        day_df = site_orders_df(view_day, status=("Active", "InJournal"))
    except Exception as e:
        st.error(f"❌ {e}")
        return
    if q.strip():
        hay = (day_df["Customer"] + " " + day_df["Invoice"]).str.casefold()
        for w in q.strip().casefold().split():
            day_df = day_df[hay.reindex(day_df.index).str.contains(w, regex=False, na=False)]
    if day_df.empty:
        st.info("No orders entered on the site for this day.")
    else:
        pcs_day = int(day_df[ORDER_BUNS].astype(int).to_numpy().sum())
        st.caption(f"{len(day_df)} order(s) · {pcs_day:,} pcs. You can fix the numbers in the table or tick Delete, then press Save changes.")
        edit = day_df[["OrderID", "Customer", "Invoice", "Payment", "Cases"] + ORDER_BUNS + ["Remark", "Entered_By", "Status"]].copy()
        edit.insert(0, "Delete", False)
        cfg = {"Delete": st.column_config.CheckboxColumn("Delete"),
               "Payment": st.column_config.SelectboxColumn("Payment", options=["AR", "FOC"])}
        for c in ORDER_BUNS + ["Cases"]:
            cfg[c] = st.column_config.NumberColumn(c, min_value=0, step=1)
        edited = st.data_editor(edit, hide_index=True, height=min(90 + 36 * len(edit), 460), key=f"ord_edit_{view_day}_{len(edit)}",
                                disabled=["OrderID", "Customer", "Entered_By", "Status"], column_config=cfg)
        if st.button("💾 Save changes", key="ord_save_changes"):
            changes = {}
            for _, r in edited.iterrows():
                changes[r["OrderID"]] = r
            denied = []

            def _apply(df):
                for i, row in df.iterrows():
                    r = changes.get(row["OrderID"])
                    if r is None:
                        continue
                    if ROLE == "sales" and row["Entered_By"] != me:
                        denied.append(row["Customer"])
                        continue
                    if bool(r["Delete"]):
                        df.at[i, "Status"] = "Deleted"
                        continue
                    for c in ORDER_BUNS + ["Cases"]:
                        df.at[i, c] = max(int(r[c]) if pd.notna(r[c]) else 0, 0)
                    for c in ("Invoice", "Remark"):
                        df.at[i, c] = (str(r[c]).strip() or "-")
                    df.at[i, "Payment"] = r["Payment"]
                return df
            try:
                modify_csv(ORDERS_FILE, ORDER_COLS, _apply)
                audit("sale_order_edit", f"{view_day}: {len(changes)} rows checked by {me}")
                if denied:
                    st.warning("You can only change your own orders. Not changed: " + ", ".join(sorted(set(denied))))
                st.session_state["flash"] = "Orders updated"
                st.rerun()
            except (RuntimeError, ConflictError) as e:
                st.error(f"❌ {e}")

    # ---- export to the journal ----
    with st.expander("📤 Export orders to the Sale Journal (Excel, same column layout)"):
        e1, e2 = st.columns(2)
        d_from = e1.date_input("From", value=today_kh(), key="ord_ex_from")
        d_to = e2.date_input("To", value=today_kh(), key="ord_ex_to")
        try:
            allo = site_orders_df(None)
            allo = allo[(allo["_dt"].dt.date >= d_from) & (allo["_dt"].dt.date <= d_to)]
        except Exception as e:
            st.error(f"❌ {e}")
            return
        if allo.empty:
            st.info("No active orders (not yet in the journal) in these dates.")
        else:
            st.caption(f"{len(allo)} order(s) not yet copied to the journal. Paste the file into the journal with "
                       "**Paste special > Skip blanks** so the journal's formulas stay. Then press the green button.")
            data = build_orders_journal_export(allo)
            st.download_button("📥 Download orders for the journal", data=data, file_name=f"Orders_for_journal_{d_from}_{d_to}.xlsx",
                               mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", key="ord_dl")
            if USE_DROPBOX and st.button("☁️ Also save this file in the Dropbox folder", key="ord_dbx"):
                try:
                    import dropbox
                    _dbx().files_upload(data, _rpath(f"Orders_for_journal_{d_from}_{d_to}.xlsx"),
                                        mode=dropbox.files.WriteMode.overwrite, mute=True)
                    st.success("Saved in the Dropbox folder.")
                except Exception as e:
                    st.error(f"❌ Could not save to Dropbox: {str(e)[:150]}")
            if ROLE in ("admin", "staff", "sales") and st.button("✅ I pasted them into the journal: mark as copied", key="ord_mark"):
                ids = set(allo["OrderID"])

                def _mark(df):
                    df.loc[df["OrderID"].isin(ids) & (df["Status"] == "Active"), "Status"] = "InJournal"
                    return df
                try:
                    modify_csv(ORDERS_FILE, ORDER_COLS, _mark)
                    audit("sale_order_marked", f"{len(ids)} orders by {me}")
                    st.session_state["flash"] = f"{len(ids)} order(s) marked as copied to the journal"
                    st.rerun()
                except (RuntimeError, ConflictError) as e:
                    st.error(f"❌ {e}")



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
{"id": "nphk-20261015-0001", "customer": "CHHIM SAYORN ទួលគោក", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/kmeov5GDr5oW875dA", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 3, "lead_no": 1, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0002", "customer": "MO ទួលពង្រ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.518901,104.876871&ll=11.518901,104.876871&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 4, "lead_no": 2},
{"id": "nphk-20261015-0003", "customer": "ស្រីលីន ក្រចេះ", "province": "ក្រចេះ", "url": "https://maps.app.goo.gl/fmUAVum6c6joAkR36", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 5, "lead_no": 3, "resolved_url": "https://www.google.com/maps/place/12%C2%B029'29.9%22N+106%C2%B003'55.5%22E/@12.491629,106.065429,1302m/data=!3m1!1e3!4m4!3m3!8m2!3d12.491629!4d106.065429?entry=tts&g_ep=EgoyMDI2MTAxMS4wIPu8ASoASAFQAw%3D%3D&skid=1e0918d0-4a09-4bb6-8f0f-94836d11cbc9", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0004", "customer": "LY MEY", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.528484,104.957959&ll=11.528484,104.957959&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 6, "lead_no": 4},
{"id": "nphk-20261015-0005", "customer": "SEANG HAI ផ្សារព្រែកថ្មី កៀនស្វាយ", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/PDtGo2oRZGsm7acz7", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 7, "lead_no": 5, "resolved_url": "https://www.google.com/maps/place/11%C2%B017'10.1%22N+105%C2%B008'22.8%22E/@11.286135,105.139678,1336m/data=!3m1!1e3!4m4!3m3!8m2!3d11.286135!4d105.139678?entry=tts&g_ep=EgoyMDI2MTAwNS4wIPu8ASoASAFQAw%3D%3D&skid=471f9c7b-a880-4720-86ad-18b986c57d7e", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0006", "customer": "ម៉ៅ ចន្ធី ក្រុងស្វាយរៀង", "province": "ស្វាយរៀង", "url": "https://goo.gl/maps/qDgJr3DkWZx5Adxk8?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 8, "lead_no": 6, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.045241,105.817289&entry=gps&g_ep=CAESBzI2LjM4LjEYACDXggMqvQEsOTQyNjc3MjcsOTQyOTIxOTUsOTQyOTk1MzIsMTAwNzk2NDk4LDEwMDc5Nzc2MSwxMDA3OTY1MzUsOTQyODA1NzYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksMTAwODA4NjU0LDk0Mjc1MTY4LDk0Mjc5NjE5LDEwMDgzNTcwNCwxMDA4MjUwMjUsMTAwODIwMjM3LDEwMDgyMjQ5NCwxMDA4Mjc5NzVCAktI&skid=f4dac2ed-dd5f-44b5-a5f6-2eed44ffbb83&shorturl=1"},
{"id": "nphk-20261015-0007", "customer": "SREY TUCH", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/oKiq5Sba38YpU6CGA", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 9, "lead_no": 7, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0008", "customer": "MAO SREYNICH វិទ្យាល័យជាតិ បាត់ដំបង", "province": "បាត់ដំបង", "url": "https://maps.app.goo.gl/4HG2iRYneSnRYfXj7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 10, "lead_no": 8, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0009", "customer": "SAIFONG កប់ស្រូវ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/HHAhyhkvFP9EX4tG6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 11, "lead_no": 9, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0010", "customer": "UNG RAKSMEY ជិតព្តលានថ្មី", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/GmRUA4t1Ur12HmBL8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 12, "lead_no": 10, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0011", "customer": "SUO SORPHOIN បារាយណ៍ កំពង់ធំ", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/vpAak8j9jLELdUXZ8", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 13, "lead_no": 11, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0012", "customer": "SREYDIN KEO", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.503340,103.611797&ll=13.503340,103.611797&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 14, "lead_no": 12},
{"id": "nphk-20261015-0013", "customer": "HAPPY DAILY MART គួរស្រូវ2", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/ABhHRyLa4u4HaFwY8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 15, "lead_no": 13, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
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
{"id": "nphk-20261015-0024", "customer": "ROMDOUL SAM ផ្សារឈូក", "province": "កំពត", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 26, "lead_no": 24},
{"id": "nphk-20261015-0025", "customer": "JEE LEANG ព្រះវិហារ", "province": "ព្រះវិហារ", "url": "https://maps.google.com/maps?q=14.238279,104.731919&ll=14.238279,104.731919&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 27, "lead_no": 25},
{"id": "nphk-20261015-0027", "customer": "SOKAN THUCH កំរៀង បាត់ដំបង", "province": "បាត់ដំបង", "url": "https://maps.google.com/maps?q=13.085018,102.484079&ll=13.085018,102.484079&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 29, "lead_no": 27},
{"id": "nphk-20261015-0028", "customer": "MEY ព្រែកព្នៅ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/yJsSRve1rhtzphyw9?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 30, "lead_no": 28, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0030", "customer": "ទ្រី ផារី កំបូល3", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.476493,104.787410&ll=11.476493,104.787410&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 32, "lead_no": 30},
{"id": "nphk-20261015-0031", "customer": "JEE LANG", "province": "ព្រះវិហារ", "url": "https://maps.google.com/maps?q=14.238279,104.731919&ll=14.238279,104.731919&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 33, "lead_no": 31},
{"id": "nphk-20261015-0032", "customer": "KIT KHUNNY ផ្សារសៃវ៉ា តាកែវ", "province": "តាកែវ", "url": "https://goo.gl/maps/gbvYaR8rvmEdhRfZ7?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 34, "lead_no": 32, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.162750,104.875431&entry=gps&g_ep=CAESBzI2LjMxLjIYACCdtwgqlQEsOTQyNjc3MjcsOTQyOTIxOTUsOTQyOTk1MzIsMTAwNzk2NDk4LDEwMDc5Nzc2MSwxMDA3OTY1MzUsOTQyODA1NzYsOTQyMDczOTQsOTQyMDc1MDYsOTQyMDg1MDYsOTQyMTg2NTMsOTQyMjk4MzksOTQyNzUxNjgsOTQyNzk2MTksMTAwODE1NjQwLDEwMDgyMDIzN0ICS0g%3D&skid=d96271f7-d43f-4f33-9d71-07cf20c3a6db&shorturl=1"},
{"id": "nphk-20261015-0033", "customer": "CHHIM SAYORN ឈូកមាស", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/WQ64GazKVkia1Exp7?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 35, "lead_no": 33, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0034", "customer": "THING បុរីសុខសាន្ដ ព្រែកឯក", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.502566,105.007372&ll=11.502566,105.007372&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 36, "lead_no": 34},
{"id": "nphk-20261015-0036", "customer": "SOTHEANY សែនសុខ", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.575709,104.878839&ll=11.575709,104.878839&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 38, "lead_no": 36},
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
{"id": "nphk-20261015-0052", "customer": "VANNAK កែប", "province": "កែប", "url": "https://maps.app.goo.gl/bc75BzayehpJuabm9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 54, "lead_no": 52, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
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
{"id": "nphk-20261015-0067", "customer": "SO NITA ផ្សារស្វៃវ៉ា តាកែវ", "province": "តាកែវ", "url": "https://maps.app.goo.gl/ZnmWBQH67GSGjMP6A?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 69, "lead_no": 67, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0068", "customer": "RACHANA ចល័ចរ កាហ្វេ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/sjag1gLzbBWAMx5M9?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 70, "lead_no": 68, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0069", "customer": "THEARA គូស្រូវ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/eEPLivNuFr8u1YJj7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 71, "lead_no": 69, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.4406193,104.8933391&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,100821559,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMzLjEuOTYxODkxNDMyMBgAINeCAypnLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDEwMDgyMTU1OSw0NzA3MTcwNCw5NDIxODY0MSw5NDI4MjEzNCwxMDA4MTM0NjQsOTQyODY4NjksMTAwODIwMjQ3LDEwMDgyMjUwNEICS0g%3D&skid=562076a0-e81b-4b3f-8dc7-4bb785a7780d&g_st=it"},
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
{"id": "nphk-20261015-0087", "customer": "អាង ឈឹម ត្រែងត្រយឹង កំពង់ស្ពឺ", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.278807,104.206944&ll=11.278807,104.206944&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 89, "lead_no": 87},
{"id": "nphk-20261015-0088", "customer": "ពុំ ស្រីនិត អូរពី កំពង់សោម", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=12.401523,105.435468&ll=12.401523,105.435468&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 90, "lead_no": 88},
{"id": "nphk-20261015-0089", "customer": "SOK KHEA ពន្ធធានាគា សៀមរាប", "province": "សៀមរាប", "url": "https://youtu.be/rAMq3cEQSVM?si=KFfX3n3wFbC_CU4o", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 91, "lead_no": 89, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
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
{"id": "nphk-20261015-0100", "customer": "CROIS CAFÉ 271", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/4DfzCcsRwTf6VgwHA?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 102, "lead_no": 100, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0101", "customer": "SREY PICH ទួលពង្រ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/TWdw6Ka1RmUhoRg66?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 103, "lead_no": 101, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0102", "customer": "ង៉ែត ញាណ ថ្មបាំង ក្រចេះ", "province": "ក្រចេះ", "url": "https://maps.app.goo.gl/SS9GfTdZNtVAFr9P6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 104, "lead_no": 102, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0103", "customer": "HENG SONY", "province": "កំពត", "url": "https://maps.app.goo.gl/Lj7axsZME21ZYRFF8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 105, "lead_no": 103, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0104", "customer": "MONITA TANN សាលាកំរើក សៀមរាប", "province": "សៀមរាប", "url": "https://maps.app.goo.gl/atmJZK616MVppEoJ7?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 106, "lead_no": 104, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0105", "customer": "POV POV", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.833427,104.451803&ll=10.833427,104.451803&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 107, "lead_no": 105},
{"id": "nphk-20261015-0106", "customer": "WAYU STEAM&SAUNA", "province": "កំពត", "url": "https://maps.google.com/maps?q=10.619675,104.174688&ll=10.619675,104.174688&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 108, "lead_no": 106},
{"id": "nphk-20261015-0107", "customer": "សុជាតា​ អ៊ុយ ផ្សារក្រគរ", "province": "ពោធិ៍សាត់", "url": "https://maps.google.com/maps?q=42.553084,0.000008&ll=42.553084,0.000008&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 109, "lead_no": 107},
{"id": "nphk-20261015-0108", "customer": "NAMHENG CHEANG", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/i9nQMiwhVVT1TXrC6?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 110, "lead_no": 108, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0109", "customer": "ម៉ីង ទៀង អូត្រេះ", "province": "ព្រះសីហនុ", "url": "https://maps.app.goo.gl/Z6NP579sHZCEAh2T8?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 111, "lead_no": 109, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=10.5617710,103.5578800&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjUuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=bb1c7680-220a-4d5e-a17c-7cc7802a3b69&g_st=ifm"},
{"id": "nphk-20261015-0110", "customer": "PHAN NA វត្តអង្គតាមិញ", "province": "ភ្នំពេញ", "url": "https://www.google.com/maps/place/11%C2%B032'45.3%22N+104%C2%B051'37.1%22E/@11.545903,104.860301,16z/data=!4m4!3m3!8m2!3d11.545903!4d104.860301?entry=ttu&g_ep=EgoyMDI2MDgwNS4xIKXMDSoASAFQAw%3D%3D", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 112, "lead_no": 110},
{"id": "nphk-20261015-0111", "customer": "LY SOK", "province": "ព្រៃវែង", "url": "https://maps.google.com/maps?q=11.259908,105.274687&ll=11.259908,105.274687&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 113, "lead_no": 111},
{"id": "nphk-20261015-0112", "customer": "ឌុល សុវណ្ណនិត ផ្សារស្ពឺ កំពង់ចាម", "province": "កំពង់ចាម", "url": "https://maps.google.com/maps?q=12.329244,105.327782&ll=12.329244,105.327782&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 114, "lead_no": 112, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0113", "customer": "OUK PONLEU", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.455301,105.000743&ll=11.455301,105.000743&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 115, "lead_no": 113},
{"id": "nphk-20261015-0114", "customer": "UTH SIEMHONG ច្បារអំពៅ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/GUmLkozJ6H9Kiuz89", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 116, "lead_no": 114, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0115", "customer": "CHUNGMEI LY", "province": "កំពង់ឆ្នាំង", "url": "https://maps.app.goo.gl/ZmrGSK5sVVtmgTEk6?g_st=ipc", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 117, "lead_no": 115, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0116", "customer": "CHHING GERRA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/K87quDujsBvqACYNA?g_st=afm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 118, "lead_no": 116, "resolved_url": "https://www.google.com/maps/place/11.530821,104.923610/data=!4m6!3m5!1s0!7e2!8m2!3d11.5308207!4d104.9236105!17m2!4m1!1e3!18m1!1e1?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBjI2LjcuNRgAIPrsDSqLASw5NDI2NzcyNyw5NDI5MjE5NSw5NDI5OTUzMiwxMDA3OTY0OTgsMTAwNzk3NzU3LDEwMDc5NjUzNSw5NDI4MDU3Niw5NDIwNzM5NCw5NDIwNzUwNiw5NDIwODUwNiw5NDIxODY1Myw5NDIyOTgzOSw5NDI3NTE2OCw5NDI3OTYxOSwxMDA3OTE0ODNCAktI&skid=db4e1f9c-e742-41e7-9dc2-f2ccbfdd7d81&g_st=afm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0117", "customer": "MAK NANA ផ្សារទម្លាប់តាកែវ", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 119, "lead_no": 117},
{"id": "nphk-20261015-0118", "customer": "ម៉ាក់ ម៉ីយ៉ីង", "province": "កំពង់ចាម", "url": "https://maps.google.com/maps?q=12.301544,105.568075&ll=12.301544,105.568075&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 120, "lead_no": 118},
{"id": "nphk-20261015-0119", "customer": "NONG DAVY ត្រពាំងថ្លឹង", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/2ycX1P4jWtsfkGtg8", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 121, "lead_no": 119, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0120", "customer": "VA KHIM", "province": "កំពង់ស្ពឺ", "url": "https://maps.apple/p/HMUUc2MNszxsA9", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 122, "lead_no": 120, "resolved_url": "https://maps.apple.com/place?coordinate=11.808148,104.164605&name=My%20Location&map=h", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0121", "customer": "KA ANGEL កៀនស្វាយ", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.511703,105.053247&ll=11.511703,105.053247&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 123, "lead_no": 121},
{"id": "nphk-20261015-0122", "customer": "KET KIKO បឹងកេងកង", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/yJvqVu1YvTzH5C7V7?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 124, "lead_no": 122, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
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
{"id": "nphk-20261015-0164", "customer": "ផ្សារយូស្តា កំពង់សោម", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/LKfhzX1mvLRSAvGp8", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 166, "lead_no": 164, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
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
{"id": "nphk-20261015-0187", "customer": "CHANBO VIBOL គួរស្រូវ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 189, "lead_no": 187},
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
{"id": "nphk-20261015-0214", "customer": "ម៉ី ក្បាលស្ពាន", "province": "ប៉ោយប៉ែត", "url": "https://maps.google.com/maps?q=13.660573,102.551352&ll=13.660573,102.551352&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 216, "lead_no": 214},
{"id": "nphk-20261015-0215", "customer": "LEANG", "province": "ត្បូងឃ្មុំ", "url": "https://maps.google.com/maps?q=11.826201,105.783795&ll=11.826201,105.783795&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 217, "lead_no": 215},
{"id": "nphk-20261015-0216", "customer": "CHOUN CHEASEYHA", "province": "កំពង់ឆ្នាំង", "url": "https://maps.google.com/maps?q=12.253794,104.670043&ll=12.253794,104.670043&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 218, "lead_no": 216},
{"id": "nphk-20261015-0217", "customer": "ទេពនិមន្ដ", "province": "កណ្តាល", "url": "https://goo.gl/maps/zDfGmNn5UzMqfPhG8?g_st=ac", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 219, "lead_no": 217, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.582924,104.970368&entry=gps&g_ep=CAESBzI2LjE2LjUYACCIJyqLASw5NDI2NzcyNyw5NDI5MjE5NSw5NDI5OTUzMiwxMDA3OTY0OTgsMTAwNzk3NzYxLDEwMDc5NjUzNSw5NDI4MDU3Niw5NDIwNzM5NCw5NDIwNzUwNiw5NDIwODUwNiw5NDIxODY1Myw5NDIyOTgzOSw5NDI3NTE2OCw5NDI3OTYxOSwxMDA4MTA0NThCAktI&skid=49a92ffc-f193-488e-9473-134b2e240b7d&shorturl=1"},
{"id": "nphk-20261015-0218", "customer": "Caltex ស្វាយអន្ទរ", "province": "ព្រៃវែង", "url": "https://maps.app.goo.gl/CCxpHExShQG87UUL8", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 220, "lead_no": 218, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
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
{"id": "nphk-20261015-0233", "customer": "NY TANG CALTEX កំពង់ឆ្នាំង", "province": "កំពង់ឆ្នាំង", "url": "https://maps.app.goo.gl/ZU885NiPvFDd1nkq5", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 235, "lead_no": 233, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0234", "customer": "OUNPOV", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.502077,104.809401&ll=11.502077,104.809401&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 236, "lead_no": 234},
{"id": "nphk-20261015-0235", "customer": "CHENG DANET", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.367083,103.838365&ll=13.367083,103.838365&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 237, "lead_no": 235},
{"id": "nphk-20261015-0236", "customer": "JEE DAEN", "province": "កំពង់ចាម", "url": "https://maps.google.com/maps?q=11.939365,105.167322&ll=11.939365,105.167322&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 238, "lead_no": 236},
{"id": "nphk-20261015-0237", "customer": "MI NEA", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/CfQrSEwa7ah9esWQ7?g_st=ifm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 239, "lead_no": 237, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0238", "customer": "SAR KEOKANHA", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.478527,104.894221&ll=11.478527,104.894221&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 240, "lead_no": 238},
{"id": "nphk-20261015-0239", "customer": "LEANG LEANG", "province": "ប៉ៃលិន", "url": "https://maps.google.com/maps?q=12.927933,102.497464&ll=12.927933,102.497464&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 241, "lead_no": 239},
{"id": "nphk-20261015-0240", "customer": "PHENG AN AN", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.333880,104.719774&ll=11.333880,104.719774&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 242, "lead_no": 240},
{"id": "nphk-20261015-0241", "customer": "YU MI", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.488753,104.813017&ll=11.488753,104.813017&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 243, "lead_no": 241},
{"id": "nphk-20261015-0242", "customer": "Central Beach Resort Long Set Beach កោះរ៉ុង", "province": "ព្រះសីហនុ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 244, "lead_no": 242},
{"id": "nphk-20261015-0243", "customer": "MOLII COFFEE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/2Q7f3eShrBa1mFsu5?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 245, "lead_no": 243, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0244", "customer": "NONG DAVY", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.514568,104.854154&ll=11.514568,104.854154&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 246, "lead_no": 244},
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
{"id": "nphk-20261015-0292", "customer": "សម្បត្ដិរក្សាតេលា អង្គរតាសោម", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 294, "lead_no": 292},
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
{"id": "nphk-20261015-0314", "customer": "សារិកា ​កាហ្វេ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/D213L6hWGpKkMgWz7", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 316, "lead_no": 314, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0315", "customer": "EANG BORA បាវិត", "province": "ស្វាយរៀង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 317, "lead_no": 315},
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
{"id": "nphk-20261015-0378", "customer": "ម៉ៃ បោយប៉ែត", "province": "ប៉ោយប៉ែត", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 380, "lead_no": 378},
{"id": "nphk-20261015-0379", "customer": "VICHARA", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.458049,104.923536&ll=11.458049,104.923536&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 381, "lead_no": 379},
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
{"id": "nphk-20261015-0414", "customer": "ហាងបាយពូហេង_ ព្រះសីហនុ", "province": "កោះពេជ្រ", "url": "https://maps.app.goo.gl/gtxKrmoJ23f9JKWe7?g_st=com.google.maps.preview.copy", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 416, "lead_no": 414, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
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
{"id": "nphk-20261015-0427", "customer": "CHENG HOUR", "province": "កំពង់ធំ", "url": "https://maps.google.com/maps?q=12.733231,104.896563&ll=12.733231,104.896563&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 429, "lead_no": 427},
{"id": "nphk-20261015-0428", "customer": "LIDA JOLIE MART", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=11.462188,104.949840&ll=11.462188,104.949840&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 430, "lead_no": 428},
{"id": "nphk-20261015-0429", "customer": "SROS SAING", "province": "កំពត", "url": "https://maps.app.goo.gl/n9crDHY5d9VG5CdR6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 431, "lead_no": 429, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0430", "customer": "LIM LONG", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Bva2ppmK7HjW1k7C7?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 432, "lead_no": 430, "resolution_note": "<urlopen error timed out>"},
{"id": "nphk-20261015-0431", "customer": "ម៉ាក់ណា កាហ្វេ បែកគូស", "province": "តាកែវ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 433, "lead_no": 431},
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
{"id": "nphk-20261015-0443", "customer": "SREY KHOUCH ព្រែកព្នៅ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 445, "lead_no": 443},
{"id": "nphk-20261015-0445", "customer": "OUNKHIM LOVE", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/Yg69EwJQAeJnNsqU7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 447, "lead_no": 445, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0446", "customer": "ម៉ុង បរមី", "province": "", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 448, "lead_no": 446},
{"id": "nphk-20261015-0447", "customer": "TON CHANNY", "province": "កោះកុង", "url": "https://maps.app.goo.gl/3pyXDbYCkTiyZCyGA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 449, "lead_no": 447, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0451", "customer": "CHANRA CHOUN", "province": "បាត់ដំបង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 453, "lead_no": 451},
{"id": "nphk-20261015-0452", "customer": "ម៉ុង បរមី", "province": "", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 454, "lead_no": 452},
{"id": "nphk-20261015-0454", "customer": "BARANG KTH", "province": "កំពត", "url": "https://maps.app.goo.gl/jZfSv5DgZDP97hTm9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 456, "lead_no": 454, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0456", "customer": "LEONG KUNTHEA", "province": "តាកែវ", "url": "https://maps.google.com/maps?q=11.183393,104.780581&ll=11.183393,104.780581&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 458, "lead_no": 456},
{"id": "nphk-20261015-0457", "customer": "RASY HR", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/16niAUFaiU2GdJYN7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 459, "lead_no": 457, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.4439860,104.8838930&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b9120834-9311-4f8c-8026-86d7a99b7e79&g_st=it"},
{"id": "nphk-20261015-0458", "customer": "ROS SARADANY", "province": "ឧត្តរមានជ័យ", "url": "https://maps.app.goo.gl/3LeWNWXj2c6pMKmS7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 460, "lead_no": 458, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0459", "customer": "NY TANG CALTEX កណ្ដាលស្ទឹង", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/ZbHvpqii8Sj7PzRu6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 461, "lead_no": 459, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0460", "customer": "អ៊ុក កញ្ញា ថ្មបាំង", "province": "កោះកុង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 462, "lead_no": 460},
{"id": "nphk-20261015-0462", "customer": "សៀក នី", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/u6qQkKy9wUf2FS1L9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 464, "lead_no": 462, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.2110680,104.5835330&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b8c863db-6d37-4ffb-a264-a75298a4b2ec&g_st=it"},
{"id": "nphk-20261015-0464", "customer": "DARA PICH", "province": "កណ្តាល", "url": "https://maps.google.com/maps?q=13.645170,102.590579&ll=13.645170,102.590579&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 466, "lead_no": 464},
{"id": "nphk-20261015-0467", "customer": "BELLA SMITT", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/SgaLfpMkbU5goa3KA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 469, "lead_no": 467, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0471", "customer": "ម៉ាក់អូន ឈីញ", "province": "ព្រះវិហារ", "url": "https://maps.app.goo.gl/LGwFe8YMrQisKQLC9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 473, "lead_no": 471, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0473", "customer": "អា នី", "province": "ត្បូងឃ្មុំ", "url": "https://maps.app.goo.gl/WVmaXBosd8HPrjut8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 475, "lead_no": 473, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.7610000,106.3343890&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=d4ebf53f-e308-4cd3-9169-e6b6fcddf316&g_st=it"},
{"id": "nphk-20261015-0474", "customer": "SN79 MART & TOYS បឹងស្នោរ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/nkp5ur1dP5s34ecj9", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 476, "lead_no": 474, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0475", "customer": "SREYPICH THAI ត្បូងឃ្មុំ", "province": "ត្បូងឃ្មុំ", "url": "https://maps.app.goo.gl/GbdG4wNgwusRYfSn8", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 477, "lead_no": 475, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0477", "customer": "CHEA MOLIVANN", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/9xqAkdZRKyogKbQ57?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 479, "lead_no": 477, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0478", "customer": "កង់ទីនសាលា BRIGHT LINE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Hq9d89aF7kn1356CA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 480, "lead_no": 478, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0479", "customer": "JEE DA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/VRHK5ono4srsGgaC9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 481, "lead_no": 479, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5121940,104.9300002&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b2d141e1-bb9b-46eb-8b85-5e66cd816145&g_st=it"},
{"id": "nphk-20261015-0480", "customer": "MALAY MALAY", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/AEgveS7ThaQzveEY9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 482, "lead_no": 480, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=12.8717070,105.0431690&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=78cf2575-4095-49d0-8d80-61fadb58adb0&g_st=it"},
{"id": "nphk-20261015-0481", "customer": "PHAL LA មន្ទីរពេទ្យកុមារជាតិ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/z1KyybEDmHyr9CNBA", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 483, "lead_no": 481, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0482", "customer": "OUK CHENDA", "province": "ព្រះសីហនុ", "url": "https://maps.app.goo.gl/FYnAD4G6vc94jEAA8?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 484, "lead_no": 482, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0484", "customer": "RAINBO", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/HizthsHTMDdR15N8A?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 486, "lead_no": 484, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0489", "customer": "MOLIKA បុរីអ័រគីដេ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/Hn9Nf2KqBm4zHX7U8?g_st=ac", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 491, "lead_no": 489, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0490", "customer": "PHAI VITA", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/pHMXdVTRx5neeMkNA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 492, "lead_no": 490, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0491", "customer": "CHANRA CHOUN", "province": "បាត់ដំបង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 493, "lead_no": 491},
{"id": "nphk-20261015-0492", "customer": "CHANRA CHOUN", "province": "បាត់ដំបង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 494, "lead_no": 492},
{"id": "nphk-20261015-0493", "customer": "CHANRA CHOUN", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 495, "lead_no": 493},
{"id": "nphk-20261015-0495", "customer": "FAML NU ផ្សារត្រពាំងផុង កំពង់ស្ពឺ", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 497, "lead_no": 495},
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
{"id": "nphk-20261015-0507", "customer": "ដេប៉ូតេលាគីឡូម៉ែត្រ65 ផ្លូវជាតិលេខ5", "province": "កំពង់ឆ្នាំង", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 509, "lead_no": 507},
{"id": "nphk-20261015-0508", "customer": "ដើមកាហ្វេ​ ដេអិន", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/JLuobf423tnhfK6n7", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 510, "lead_no": 508, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0509", "customer": "ដើមកាហ្វេ បឹងកក់", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/NS6rxYzRAHRPnS5D6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 511, "lead_no": 509, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5318309,104.9296739&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=9cca0c1c-bb8e-4c08-b09b-30d4daf2be8c&g_st=it"},
{"id": "nphk-20261015-0513", "customer": "THEARY", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/fCyvZSzrEx2Mc8u56?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 515, "lead_no": 513, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5141191,104.9024659&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=4d59d915-2af7-462b-9fc2-9a16214896ca&g_st=it"},
{"id": "nphk-20261015-0514", "customer": "មុំ ចន្ទ័រតនា", "province": "តាកែវ", "url": "https://maps.app.goo.gl/m2wRWPwMwYbHedGB7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 516, "lead_no": 514, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=10.9794480,104.7747130&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=f4e2a8d6-a20f-4d99-a704-4187c4b5bedc&g_st=it"},
{"id": "nphk-20261015-0515", "customer": "និនិកាហ្វេ- NINI CAFÉ", "province": "កំពង់ធំ", "url": "https://maps.google.com/maps?q=13.036699,104.513791&ll=13.036699,104.513791&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 517, "lead_no": 515},
{"id": "nphk-20261015-0516", "customer": "SOEURNG SREY NEANG", "province": "កំពង់ធំ", "url": "https://maps.app.goo.gl/oaWKqDxFCaxQnCyJ7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 518, "lead_no": 516, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=12.6128550,105.0031460&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=8929b6f1-adde-4fdc-a46f-afa4d2004a74&g_st=it"},
{"id": "nphk-20261015-0517", "customer": "SON CHANDY", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/38LexCPMCQExx1TM9?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 519, "lead_no": 517, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0520", "customer": "MALIKA YURI", "province": "កំពង់ចាម", "url": "https://maps.app.goo.gl/fkka935UGb9iAkLF7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 522, "lead_no": 520, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0521", "customer": "SAMNEANG LUN", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.583637,104.841023&ll=11.583637,104.841023&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 523, "lead_no": 521},
{"id": "nphk-20261015-0522", "customer": "DIAMOND BICYCLE ឬស្សីកែវ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/MewdYicvXvikCkJv6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 524, "lead_no": 522, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0523", "customer": "ដេប៉ូតេលាគីឡូម៉ែត្រ65", "province": "កំពង់ឆ្នាំង", "url": "https://maps.app.goo.gl/MUMtHk5JzN65nqg88?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 525, "lead_no": 523, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0529", "customer": "BELLA SMITT", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.395932,104.801630&ll=11.395932,104.801630&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 531, "lead_no": 529},
{"id": "nphk-20261015-0531", "customer": "POP CAFÉ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/YVHnyEySsoBitf4f7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 533, "lead_no": 531, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0534", "customer": "ចណ្ណា កាហ្វេ", "province": "តាកែវ", "url": "https://maps.app.goo.gl/wURSFi2aqQRxotLKA?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 536, "lead_no": 534, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0538", "customer": "ហួត លៀងទុយ", "province": "កោះកុង", "url": "https://maps.google.com/maps?q=11.139767,103.768197&ll=11.139767,103.768197&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 540, "lead_no": 538},
{"id": "nphk-20261015-0542", "customer": "NIMOL VOEUN ផ្សារសំរោងយ៉ោង", "province": "តាកែវ", "url": "https://maps.app.goo.gl/zXPtWxg5vmygyQTo6", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 544, "lead_no": 542, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0543", "customer": "LAY KONG RETAIL", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/8tzE4c8pDT5kFAm7A?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 545, "lead_no": 543, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0545", "customer": "HENG CHHUNIM", "province": "ភ្នំពេញ", "url": "https://maps.google.com/maps?q=11.530185,104.864197&ll=11.530185,104.864197&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 547, "lead_no": 545},
{"id": "nphk-20261015-0546", "customer": "តុប ណៃអេង ផ្សារតាឡាត់", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 548, "lead_no": 546},
{"id": "nphk-20261015-0547", "customer": "ប៉ុក វ៉ាត", "province": "រតនគិរី", "url": "https://maps.app.goo.gl/jr1FMhFTVrpzXqfdA?g_st=atm", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 549, "lead_no": 547, "resolved_url": "https://www.google.com/maps/place/13.685918,107.216926/data=!4m6!3m5!1s0!7e2!8m2!3d13.6859176!4d107.2169263?utm_source=mstt_1&entry=gps&coh=192189&g_ep=CAESBzI1LjEzLjYYACDj7Q0qYyw5NDIyMzI5OSw5NDIxNjQxMyw5NDIxMjQ5Niw5NDIwNzM5NCw5NDIwNzUwNiw5NDIwODUwNiw5NDIxNzUyMyw5NDIxODY1Myw5NDIyOTgzOSw0NzA4NDM5Myw5NDIxMzIwMEICS0g%3D&skid=648cd766-2ce9-4479-823b-f383d4f044c7&g_st=atm", "resolution_note": "Expanded from supplied map link"},
{"id": "nphk-20261015-0549", "customer": "សឿន ប៊ុនឆៃ បុរីសូនី", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/k3penyvvMnXeUpSn6?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 551, "lead_no": 549, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5275120,104.8807430&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b525be45-d9cb-4ce9-9240-272f9257a9a0&g_st=it"},
{"id": "nphk-20261015-0552", "customer": "ដើមកាហ្វេ បឹងកក់", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/fFDF5LYAwGFKpn5m8", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 554, "lead_no": 552, "resolution_note": "Link updated 2026-10-30 (Location update.xlsx)"},
{"id": "nphk-20261015-0553", "customer": "SOMA LY", "province": "ព្រះសីហនុ", "url": "https://maps.google.com/maps?q=10.620510,103.542128&ll=10.620510,103.542128&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 555, "lead_no": 553},
{"id": "nphk-20261015-0554", "customer": "BTA WATCH", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/SPjvFBGQkcD5o2nT7", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 556, "lead_no": 554, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0556", "customer": "នំបុ័ងភ្នំពេញ", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 558, "lead_no": 556},
{"id": "nphk-20261015-0559", "customer": "KIM SEU LY", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/1aNgLMuepZNhrQXk7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 561, "lead_no": 559, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5237610,104.9075820&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=b35e3b10-1f9c-4374-b435-68abc3a3b458&g_st=it"},
{"id": "nphk-20261015-0560", "customer": "ចេ ស្រស់", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.278135,104.210464&ll=11.278135,104.210464&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 562, "lead_no": 560},
{"id": "nphk-20261015-0561", "customer": "EI SOK MENG", "province": "កំពង់ស្ពឺ", "url": "https://maps.google.com/maps?q=11.389148,104.378740&ll=11.389148,104.378740&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 563, "lead_no": 561},
{"id": "nphk-20261015-0562", "customer": "SOU SARITH បឹងកេងកង3", "province": "ភ្នំពេញ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 564, "lead_no": 562},
{"id": "nphk-20261015-0563", "customer": "THEARYNA SENG", "province": "មណ្ឌលគិរី", "url": "https://maps.google.com/maps?q=12.460194,107.185893&ll=12.460194,107.185893&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 565, "lead_no": 563},
{"id": "nphk-20261015-0564", "customer": "ម៉ាក់ កូនវិ", "province": "កណ្តាល", "url": "https://maps.app.goo.gl/dwtmMviNLSTYdSNW7?g_st=it", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 566, "lead_no": 564, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5008200,104.7504870&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMwLjMuOTUwNDkyMTU1MBgAINeCAypdLDk0Mjk3Njk5LDk0MjMxMTg4LDk0MjgwNTY4LDQ3MDcxNzA0LDk0MjE4NjQxLDk0MjgyMTM0LDEwMDgxMzQ2NCw5NDI4Njg2OSwxMDA4MjAyNDcsMTAwODIyNTA0QgJLSA%3D%3D&skid=31fa9195-cfcd-4d90-b258-6ee98f2267b6&g_st=it"},
{"id": "nphk-20261015-0565", "customer": "NIN NOCH កំពង់ស្ពឺ", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 567, "lead_no": 565},
{"id": "nphk-20261015-0566", "customer": "THY CHOURY", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/yYPf4eriKD3qvbF6A?g_st=com.google.maps.preview.copy", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 568, "lead_no": 566, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.7587270,104.9232300&entry=gps&lucs=,94259550,94242520,94224825,94227247,94227248,94231188,47071704,94259573,47069508,94218641,94203019,47084304,94208458,94208447&g_ep=CAISEjI1LjA4LjAuNzI3OTM5NzI3MBgAIIgnKn4sOTQyNTk1NTAsOTQyNDI1MjAsOTQyMjQ4MjUsOTQyMjcyNDcsOTQyMjcyNDgsOTQyMzExODgsNDcwNzE3MDQsOTQyNTk1NzMsNDcwNjk1MDgsOTQyMTg2NDEsOTQyMDMwMTksNDcwODQzMDQsOTQyMDg0NTgsOTQyMDg0NDdCAktI&g_st=com.google.maps.preview.copy"},
{"id": "nphk-20261015-0567", "customer": "SREY LIN ព្រែកចាក", "province": "កំពត", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 569, "lead_no": 567},
{"id": "nphk-20261015-0568", "customer": "MORIKO KREE", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/oVxQR1sv3GSBVCi78?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 570, "lead_no": 568, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.7293560,104.5577810&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjQuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=af70c0b9-cab8-4b4c-aaa1-9d7b32839142&g_st=ic"},
{"id": "nphk-20261015-0569", "customer": "ស្រី នាត​ វត្តស្អាងស្រែ កណ្ដាល", "province": "កណ្តាល", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 571, "lead_no": 569},
{"id": "nphk-20261015-0570", "customer": "កោះកាហ្វេ", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/18SoQZcfJb72jGqV8", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 572, "lead_no": 570, "resolution_note": "Link opened but no usable destination coordinates were found. Paste a full dropped-pin link instead."},
{"id": "nphk-20261015-0571", "customer": "RADET JASPER ឈូកវ៉ា 2", "province": "ភ្នំពេញ", "url": "https://nphk-pos.balancikaapps.com/login", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 573, "lead_no": 571},
{"id": "nphk-20261015-0573", "customer": "VOUCH CHHENG", "province": "សៀមរាប", "url": "https://maps.google.com/maps?q=13.126683,104.336279&ll=13.126683,104.336279&z=16", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 575, "lead_no": 573},
{"id": "nphk-20261015-0576", "customer": "ជឹមជ័យសិរីមុន្និន", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/VTeN9fhx6P3hCadZ8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 578, "lead_no": 576, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5513240,104.9396820&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjQuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=aede89dd-bf1b-4c7e-8fff-fc5f7f543902&g_st=ic"},
{"id": "nphk-20261015-0577", "customer": "ជា សុភ័ក្រ្ត", "province": "ភ្នំពេញ", "url": "https://maps.app.goo.gl/BPoYiJgLGyzeANsw8?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 579, "lead_no": 577, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.5389860,104.9028930&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjQuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=1baf7668-37c7-4c70-ad93-9e562cbd05c7&g_st=ic"},
{"id": "nphk-20261015-0581", "customer": "SEAV AY ផ្សារក្រាំងចេក កំពង់ស្ពឺ", "province": "កំពង់ស្ពឺ", "url": "", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 583, "lead_no": 581},
{"id": "nphk-20261015-0590", "customer": "LAY LYCHING SOK SOTHEAVORN", "province": "កំពង់ស្ពឺ", "url": "https://maps.app.goo.gl/oVxQR1sv3GSBVCi78?g_st=ic", "source": "NPHK_Leads_Report_20261015_152318.xlsx", "source_row": 592, "lead_no": 590, "resolution_note": "Expanded from supplied map link", "resolved_url": "https://maps.google.com/?q=11.7293560,104.5577810&entry=gps&shh=CAE&lucs=,94297699,94231188,94280568,47071704,94218641,94282134,100813464,94286869,100820247,100822504&g_ep=CAISEjI2LjMxLjQuOTU0MzA2MDQzMBgAIIgnKl0sOTQyOTc2OTksOTQyMzExODgsOTQyODA1NjgsNDcwNzE3MDQsOTQyMTg2NDEsOTQyODIxMzQsMTAwODEzNDY0LDk0Mjg2ODY5LDEwMDgyMDI0NywxMDA4MjI1MDRCAktI&skid=af70c0b9-cab8-4b4c-aaa1-9d7b32839142&g_st=ic"}
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


@st.cache_data(show_spinner=False, max_entries=1)
def _map_seed_records():
    return {r["id"]: dict(r) for r in json.loads(_MAP_SEED_JSON)}


def load_map_registry(force=False):
    with _sync_state()["lock"]:
        if USE_DROPBOX:
            pull(MAP_REGISTRY_FILE, force=force)
        overlay = _read_map_overlay()
        records = _map_seed_records()
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


@functools.lru_cache(maxsize=8192)
def _analyse_map_link_cached(url):
    return analyse_map_link(url)


def map_record_analysis(record):
    analysis = dict(_analyse_map_link_cached(record.get("resolved_url") or record.get("url", "")))
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


def _map_name_index(registry):
    """{normalised name: [records]} — built once per loaded registry (kept on the registry dict itself)."""
    idx = registry.get("_name_index")
    if idx is None or registry.get("_name_index_n") != len(registry.get("records", {})):
        idx = {}
        for rec in registry.get("records", {}).values():
            idx.setdefault(norm_name(rec["customer"]), []).append(rec)
        registry["_name_index"], registry["_name_index_n"] = idx, len(registry.get("records", {}))
    return idx


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
        candidates = _map_name_index(registry).get(key, [])
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


_MAP_CONSENT_HOSTS = frozenset({"consent.google.com", "consent.youtube.com"})
_MAP_HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
                   "Chrome/124.0 Safari/537.36"),
    "Accept-Language": "en-US,en;q=0.8",
    "Cookie": "CONSENT=YES+cb; SOCS=CAI",          # skip Google's cookie page so the map page itself comes back
}


def _map_consent_target(url):
    """Google sometimes sends links to its cookie page first; the real map address is in ?continue=."""
    try:
        parsed = urllib.parse.urlsplit(url)
        if parsed.hostname in _MAP_CONSENT_HOSTS:
            nxt = urllib.parse.parse_qs(parsed.query).get("continue", [""])[0]
            return trusted_map_url(nxt)
    except (ValueError, TypeError):
        pass
    return ""


class _MapRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        target = _map_consent_target(newurl)
        if target:
            newurl = target
        if not trusted_map_url(newurl):
            if fp is not None:
                fp.close()
            raise ValueError("Map link redirected outside the supported map providers.")
        if analyse_map_link(newurl)["Map status"] == "Ready pin":
            if fp is not None:
                fp.close()
            raise _ResolvedMapPin(newurl)
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def _map_in_cambodia(lat, lon):
    return math.isfinite(lat) and math.isfinite(lon) and 10 <= lat <= 15 and 102 <= lon <= 108


def _map_coords_from_page(final_url, html):
    """(lat, lon, how) of the shop on a Google Maps place page, or None.
    New share links (maps.app.goo.gl → ?q=name&ftid=… or /maps/place/name/data=…) carry no numbers in the address,
    but the page itself does. Marker positions are used first; the page centre only for a single-place page."""
    text = urllib.parse.unquote(html.replace("\\u0026", "&").replace("\u0026", "&").replace("&amp;", "&"))
    num = r"([-+]?\d{1,3}\.\d{3,})"
    # 1) static map preview with a marker on the place
    for la, lo in re.findall(r"staticmap\?[^\"'\s]*?markers=[^\"'\s]*?" + num + r"(?:,|%2C)" + num, text):
        if _map_in_cambodia(float(la), float(lo)):
            return float(la), float(lo), "marker on the Google place page"
    # 2) the place's own pin (!3d lat !4d lon); several different pins = not safe to choose
    pins = {(round(float(la), 5), round(float(lo), 5)) for la, lo in re.findall(r"!3d" + num + r"!4d" + num, text)}
    pins = {p for p in pins if _map_in_cambodia(*p)}
    if len(pins) == 1:
        la, lo = next(iter(pins))
        return la, lo, "pin on the Google place page"
    path = urllib.parse.urlsplit(final_url)
    single_place = "/maps/place/" in path.path or "ftid=" in path.query or "cid=" in path.query
    if not single_place:
        return None
    # 3) static map preview centred on the place
    for la, lo in re.findall(r"staticmap\?[^\"'\s]*?center=" + num + r"(?:,|%2C)" + num, text):
        if _map_in_cambodia(float(la), float(lo)):
            return float(la), float(lo), "centre of the Google place page"
    # 4) the place address itself: /maps/place/<name>/@lat,lon,zoom
    m = re.search(r"/@" + num + "," + num + ",", urllib.parse.unquote(final_url))
    if m and _map_in_cambodia(float(m.group(1)), float(m.group(2))):
        return float(m.group(1)), float(m.group(2)), "Google place address"
    # 5) the first map view of the page (centred on the place)
    m = re.search(r"APP_INITIALIZATION_STATE=\[\[\[[-+\d.e]+," + num + "," + num + r"\]", text)
    if m and _map_in_cambodia(float(m.group(2)), float(m.group(1))):
        return float(m.group(2)), float(m.group(1)), "centre of the Google place page"
    return None


def resolve_map_link(url):
    """Network-only worker: no Streamlit/session access. Returns a link that contains the shop's coordinates."""
    if not trusted_map_url(url):
        raise ValueError("Unsupported map link")
    if analyse_map_link(url)["Map status"] == "Ready pin":
        return url
    opener = urllib.request.build_opener(_MapRedirectHandler())
    request = urllib.request.Request(url, headers=_MAP_HEADERS)
    try:
        with opener.open(request, timeout=12) as response:
            final_url = response.geturl()
            target = _map_consent_target(final_url)
            if target:
                final_url = target
            if not trusted_map_url(final_url):
                raise ValueError("Unsupported map destination")
            if analyse_map_link(final_url)["Map status"] == "Ready pin":
                return final_url
            html = response.read(3_000_000).decode("utf-8", "ignore") if not target else ""
        if target:                                       # cookie page: open the real map page once
            with opener.open(urllib.request.Request(final_url, headers=_MAP_HEADERS), timeout=12) as response:
                html = response.read(3_000_000).decode("utf-8", "ignore")
        found = _map_coords_from_page(final_url, html)
        if found:
            lat, lon, _how = found
            return f"https://maps.google.com/?q={lat:.6f},{lon:.6f}"
        raise ValueError("Link opened but no usable destination coordinates were found. "
                         "In Google Maps press and hold on the shop to drop a pin, then Share that pin.")
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
        retry = ("Needs link expansion", "Needs full pin link", "Link has no destination coordinates")
        pending = locations[locations["Map status"].isin(retry)
                            & ~locations["Resolution note"].astype(str).str.contains("press and hold", regex=False)]
        st.caption(f"{len(pending)} links need expansion (links that failed before are tried again with the new reader). "
                   "The app opens up to 20 links at a time. Your server needs access to Google / Apple Maps.")
        if st.button("Resolve next 20 map links", key="map_resolve", disabled=pending.empty):
            order = pending["Map status"].map({"Needs link expansion": 0}).fillna(1)
            selected = pending.assign(_o=order).sort_values(["_o", "Resolution note"], kind="stable").head(20)
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
# TAB: SALES INSIGHTS  (top customers, missed orders, no order this month, customer care)
# Uses only data the app already has: journal + orders typed on the site (journal_plus_orders).
# FOC (free) rows are ignored: a free gift is not an order. STAFF / GENERAL are ignored.
# ==========================================
SI_HIST_DAILY_FILE = os.path.join(DATA_DIR, "sales_history_daily.csv")      # older months, one row per invoice line
SI_HIST_MONTHLY_FILE = os.path.join(DATA_DIR, "sales_history_monthly.csv")  # older months, bun pieces per customer per month
SI_IGNORE_NAMES = {x.upper() for x in IGNORE_NEW} | {"STAF"}          # staff / general sales are not customers
SI_PERIODS = ["This month", "Last month", "Last 30 days", "Last 90 days", "All time"]
SI_METRICS = {"Sales ៛": "Sales", "Bun pcs": "Pcs", "Cases": "Cases", "Orders (days)": "Orders"}


def _si_period(choice, today):
    first_this = today.replace(day=1)
    last_prev = first_this - timedelta(days=1)
    if choice == "This month":
        return first_this, today
    if choice == "Last month":
        return last_prev.replace(day=1), last_prev
    if choice == "Last 30 days":
        return today - timedelta(days=29), today
    if choice == "Last 90 days":
        return today - timedelta(days=89), today
    return date(2000, 1, 1), today


@st.cache_data(show_spinner=False, max_entries=4)
def _si_hist_cached(path, mtime_ns, size):
    return pd.read_csv(path, encoding="utf-8-sig")


def _si_read_hist(path):
    """History CSV (empty DataFrame if the file is not there). In Dropbox mode it is pulled from the data folder."""
    if USE_DROPBOX:
        try:
            pull(path)
        except Exception as e:
            bot_log("warn", "Sales history", f"Could not refresh {os.path.basename(path)}: {str(e)[:100]}", "using the saved copy")
    if not os.path.exists(path):
        return pd.DataFrame()
    try:
        stt = os.stat(path)
        return _si_hist_cached(path, stt.st_mtime_ns, stt.st_size).copy()
    except Exception as e:
        bot_log("warn", "Sales history", f"{os.path.basename(path)} could not be read: {str(e)[:120]}", "ignored")
        return pd.DataFrame()


def _si_add_history(j, codes, hist_daily, hist_monthly):
    """Older daily rows are added to the journal rows. A day that is already in the journal is never added twice."""
    if hist_daily is None or hist_daily.empty or not {"Date", "Customer"} <= set(hist_daily.columns):
        return j, codes, 0
    h = hist_daily.copy()
    h["Date"] = pd.to_datetime(h["Date"], errors="coerce").dt.normalize()
    h = h.dropna(subset=["Date"])
    if j is not None and not j.empty:
        have = set(pd.to_datetime(j["Date"], errors="coerce").dt.normalize().dropna())
        h = h[~h["Date"].isin(have)]
    if h.empty:
        return j, codes, 0
    if hist_monthly is not None and not hist_monthly.empty and "Code" in h.columns and "Code" in hist_monthly.columns:
        code_name = dict(zip(hist_monthly["Code"], hist_monthly["Customer"]))      # same customer, same spelling as the master list
        h["Customer"] = h["Code"].map(code_name).fillna(h["Customer"])
    extra = [c for c in h.columns if re.match(r"^N\d+$", str(c)) and c not in codes]
    all_codes = list(codes) + extra
    out = pd.DataFrame({"Date": h["Date"].dt.date, "Customer": h["Customer"].astype(str),
                        "Cases": pd.to_numeric(h["Cases_est"] if "Cases_est" in h.columns else 0, errors="coerce"),
                        "Invoice": h["Invoice"] if "Invoice" in h.columns else "-",
                        "Remark": h["Remark"] if "Remark" in h.columns else "-", "FOC": False, "_site": False})
    for c in all_codes:
        out[c] = pd.to_numeric(h[c], errors="coerce").fillna(0.0) if c in h.columns else 0.0
    if "SalesActual" in h:
        out["SalesActual"] = pd.to_numeric(h["SalesActual"], errors="coerce")
    base = j if (j is not None and not j.empty) else out.iloc[0:0]
    if "SalesActual" in base and "SalesActual" not in out:
        out["SalesActual"] = float("nan")
    for c in all_codes:
        if c not in base.columns:
            base = base.assign(**{c: 0.0})
    merged = pd.concat([base, out[[c for c in base.columns if c in out.columns]]], ignore_index=True)
    return merged, all_codes, len(out)


SI_JOURNAL_HISTORY_FILE = os.path.join(DATA_DIR, 'sales_journal_history.csv')


def _si_is_journal_name(name):
    cleaned = re.sub(r'[\s\u200b_\-.]+', '', name).lower()
    return (name.lower().endswith('.xlsx') and 'sale' in cleaned and 'jou' in cleaned
            and not name.startswith('~$') and 'conflictedcopy' not in cleaned
            and '__status' not in name.lower())


@st.cache_data(show_spinner=False, max_entries=8)
def _si_archive_snapshot(path, mtime_ns, size):
    return _read_excel_snapshot(path)


def _si_merge_month_sources(sources, live, today):
    """Replace whole monthly snapshots, not individual rows, so deleted invoices stay deleted.
    Sources are ordered old -> new. Live journal wins for the months it contains.
    """
    months={};codes=[]
    for label,frame in sources+[('Live journal',live)]:
        if frame is None or frame.empty:continue
        data=frame.copy()
        data['Date']=pd.to_datetime(data['Date'],errors='coerce').dt.date
        data=data[data['Date'].notna()]
        # September onward is authoritative journal detail. Older history stays in its own files.
        data=data[data['Date']>=date(2026,9,1)]
        for c in data:
            if re.fullmatch(r'N\d+',str(c)) and c not in codes:codes.append(c)
        data['_month']=data['Date'].map(lambda d:d.strftime('%Y-%m'))
        primary = data['_month'].value_counts().index[0] if not data.empty else None
        for month,g in data.groupby('_month',sort=False):
            # September workbooks may contain a few October rows. They must not replace October's journal.
            owns_month = month == primary
            if month not in months or owns_month or not months[month][2]:
                months[month]=(label,g.drop(columns='_month').assign(Source=label),owns_month)
    coverage=[]
    expected=pd.period_range('2026-09',max(pd.Period(today,'M'),pd.Period('2026-12','M')),freq='M').strftime('%Y-%m')
    for month in sorted(set(months)|set(expected)):
        if month in months:
            label,g,_=months[month]
            dated=g[g['Date']<=today]
            coverage.append({'Month':month,'Data status':'Available through '+str(dated['Date'].max()) if not dated.empty else 'Future-dated records only',
                             'Source':label,'Journal rows':len(g),'Last recorded date':str(g['Date'].max())})
        elif month>today.strftime('%Y-%m'):coverage.append({'Month':month,'Data status':'Not started yet','Source':'','Journal rows':0,'Last recorded date':''})
        else:coverage.append({'Month':month,'Data status':'Not loaded — not zero sales','Source':'','Journal rows':0,'Last recorded date':''})
    parts=[g for _,g,_ in months.values()]
    combined=pd.concat(parts,ignore_index=True,sort=False) if parts else live.iloc[0:0].copy()
    for c in codes:combined[c]=pd.to_numeric(combined[c],errors='coerce').fillna(0)
    if 'FOC' in combined:combined['FOC']=combined['FOC'].map(lambda v: str(v).strip().lower() in ('true','1','yes'))
    else:combined['FOC']=False
    # Saved history was written with the old rule; apply the current free-row rule to every row.
    for c in ('Pay','Remark','FreeReason'):
        if c not in combined:combined[c]=''
    combined[['Pay','Remark','FreeReason']]=combined[['Pay','Remark','FreeReason']].fillna('').astype(str)
    if not combined.empty:
        pcs=combined[codes].sum(axis=1) if codes else pd.Series(0.0,index=combined.index)
        sales=pd.to_numeric(combined.get('SalesActual',pd.Series(index=combined.index,dtype=float)),errors='coerce')
        again=[free_reason(p,r,n,v) for p,r,n,v in zip(combined['Pay'],combined['Remark'],pcs,sales)]
        old_rule=combined['FOC'] & combined['FreeReason'].isin(['','nan'])
        combined['FreeReason']=[a or (f if f not in ('','nan') else ('FOC (saved history)' if o else '')) for a,f,o in zip(again,combined['FreeReason'],old_rule)]
        combined['FOC']=combined['FreeReason'].ne('')
    return combined,codes,pd.DataFrame(coverage)


def _si_collect_journals(snap):
    sources=[];warnings_out=[];skipped=[]
    seed=_si_read_hist(SI_JOURNAL_HISTORY_FILE)
    if not seed.empty and {'Date','Customer','Cases','Invoice'} <= set(seed):
        if 'Source_File' in seed:
            for label,frame in seed.groupby('Source_File',sort=False):
                sources.append(('Saved history: '+str(label),frame))
        else:
            for month,frame in seed.groupby(pd.to_datetime(seed['Date'],errors='coerce').dt.strftime('%Y-%m')):
                sources.append(('Saved history: '+str(month),frame))
    try:
        if USE_DROPBOX:
            candidates=[r for r in _list_remote_folder() if _si_is_journal_name(r['name'])]
        else:
            candidates=[{'name':os.path.basename(p),'mtime':os.path.getmtime(p),'path':p} for p in glob.glob(os.path.join(CURRENT_DIR,'*.xlsx')) if _si_is_journal_name(os.path.basename(p))]
        current=find_excel_file()
        current_name=os.path.basename(current) if current else ''
        for item in sorted(candidates,key=lambda r:(r['mtime'],r['name'])):
            if item['name']==current_name:continue
            try:
                if USE_DROPBOX:
                    local=os.path.join(CACHE_DIR,'analysis_journals',item['name'])
                    state=_sync_state()
                    with state['lock']:
                        revs=state.setdefault('analysis_revs',{})
                        if not os.path.exists(local) or revs.get(item['name'])!=item['rev']:
                            md,response=_dbx().files_download(_rpath(item['name']))
                            _write_atomic(local,response.content)
                            revs[item['name']]=md.rev
                else:local=item['path']
                info=os.stat(local)
                archive=_si_archive_snapshot(local,info.st_mtime_ns,info.st_size)
                sources.append((item['name'],archive['journal']))
                skipped+=[dict(r,Source=item['name']) for r in archive.get('skipped',[])]
            except Exception as error:
                warnings_out.append(item['name']+': '+str(error)[:100])
    except Exception as error:
        warnings_out.append('Journal folder could not be checked: '+str(error)[:100])
    merged,codes,coverage=_si_merge_month_sources(sources,snap['journal'],today_kh())
    # Add unposted site orders only after merging every month's invoices.
    combined_snap=dict(snap,journal=merged,buns=dict(snap.get('buns',{}),codes=codes))
    combined=journal_plus_orders(combined_snap)
    skipped+=[dict(r,Source='Live journal') for r in snap.get('skipped',[])]
    st.session_state['si_journal_coverage']=coverage
    st.session_state['si_journal_warnings']=warnings_out
    st.session_state['si_skipped']=pd.DataFrame(skipped)
    st.session_state['si_combined']=combined          # used by the Data check section
    return combined,codes


@st.cache_resource(show_spinner=False)
def _si_prepare_memo():
    return {}


_SI_PREP_STATE_KEYS = ("si_journal_coverage", "si_journal_warnings", "si_skipped", "si_combined")


def _si_prepare_sig():
    """Changes only when a journal, a history file or the site orders change (or the day changes)."""
    files = (SI_JOURNAL_HISTORY_FILE, SI_HIST_DAILY_FILE, SI_HIST_MONTHLY_FILE, ORDERS_FILE)
    if USE_DROPBOX:
        for p in files:
            try:
                pull(p)
            except Exception:
                pass
        journals = tuple(sorted((r["name"], r["rev"]) for r in _list_remote_folder() if _si_is_journal_name(r["name"])))
    else:
        journals = tuple(sorted((os.path.basename(p), _file_sig(p)) for p in glob.glob(os.path.join(CURRENT_DIR, "*.xlsx"))
                                if _si_is_journal_name(os.path.basename(p))))
    cur = find_excel_file()
    return (str(cur), _file_sig(cur) if cur else (0, 0), journals, tuple(_file_sig(p) for p in files), str(today_kh()))


def _si_prepare(snap):
    """One row per customer per day: (Key, D, Customer, Cases, Sales, Pcs) + the bun-level rows.
    Reused by every page and every person until a journal / history / order file changes (was rebuilt on each click)."""
    try:
        sig = _si_prepare_sig()
    except Exception:
        sig = None
    memo = _si_prepare_memo()
    hit = memo.get("v")
    if sig is not None and hit and hit[0] == sig:
        for k, v in hit[2].items():
            st.session_state[k] = v
        return hit[1]
    j, codes = _si_collect_journals(snap)
    history_daily = _si_read_hist(SI_HIST_DAILY_FILE)
    history_monthly = _si_read_hist(SI_HIST_MONTHLY_FILE)
    sell = (snap.get("buns", {}) or {}).get("sell", {}) or {}
    out = _si_prepare_cached(j, codes, history_daily, history_monthly, sell, today_kh())
    if sig is not None:
        memo["v"] = (sig, out, {k: st.session_state.get(k) for k in _SI_PREP_STATE_KEYS})
    return out


@st.cache_data(show_spinner=False, max_entries=4)
def _si_prepare_cached(j, codes, history_daily, history_monthly, sell, as_of):
    """Inputs include current orders, both history sources, product codes and prices."""
    j, codes, _n_hist = _si_add_history(j, codes, history_daily, history_monthly)
    if j is None or j.empty:
        return pd.DataFrame(), pd.DataFrame(), codes
    df = j.copy()
    df["Customer"] = df["Customer"].astype(str).str.strip()
    df = df[df["Customer"].ne("") & ~df["Customer"].str.upper().isin(SI_IGNORE_NAMES)]
    df = df[~df["FOC"].fillna(False).astype(bool)]                       # free buns are not orders
    df["D"] = pd.to_datetime(df["Date"], errors="coerce").dt.normalize()
    df = df.dropna(subset=["D"]).copy()
    df["Key"] = df["Customer"].map(norm_name)
    for c in codes:
        df[c] = pd.to_numeric(df[c], errors="coerce").fillna(0.0)
    if codes:
        price = pd.Series({c: float(sell.get(c) or 0) for c in codes})
        df["Sales"] = (df[codes] * price).sum(axis=1)
        df["Pcs"] = df[codes].sum(axis=1)
    else:
        df["Sales"], df["Pcs"] = 0.0, 0.0
    if "SalesActual" in df:
        actual = pd.to_numeric(df["SalesActual"], errors="coerce")
        df["Sales basis"] = actual.notna().map({True: "Journal amount", False: "Estimated from product prices"})
        df["Sales"] = actual.fillna(df["Sales"])
    else:
        df["Sales basis"] = "Estimated from product prices"
    # Future orders are not treated as actual historical sales. Lines without buns (fridge, umbrella,
    # deposit...) are not bun orders: they would add riel and a fake "order day". Data check lists them.
    df = df[(df["D"] <= pd.Timestamp(as_of)) & (df["Pcs"] > 0)].copy()
    df["Cases"] = pd.to_numeric(df["Cases"], errors="coerce").fillna(0.0)
    daily = df.groupby(["Key", "D"], as_index=False).agg(
        Customer=("Customer", "first"), Cases=("Cases", "sum"), Sales=("Sales", "sum"), Pcs=("Pcs", "sum"))
    return daily, df, codes


def _si_names_areas(snap, daily):
    names = {norm_name(n): n for n in snap.get("customers", [])}
    for k, n in zip(daily["Key"], daily["Customer"]):
        names.setdefault(k, n)
    amap = areas_lookup(snap)
    areas = {k: AREA_LABEL.get(amap.get(k, "Unknown"), AREA_LABEL["Unknown"]) for k in names}
    return names, areas


def _si_top(daily, start, end, metric, names, areas, top_n=20, df=None, codes=()):
    s, e = pd.Timestamp(start), pd.Timestamp(end)

    def _agg(a, b):
        part = daily[(daily["D"] >= a) & (daily["D"] <= b)]
        return part.groupby("Key").agg(Orders=("D", "nunique"), Cases=("Cases", "sum"), Pcs=("Pcs", "sum"),
                                       Sales=("Sales", "sum"), Last=("D", "max"))
    cur = _agg(s, e)
    if cur.empty:
        return pd.DataFrame(), 0
    total = float(cur[metric].sum())
    if start.year > 2001:                                                 # not "All time" -> compare with the period before
        length = (e - s).days + 1
        prev = _agg(s - pd.Timedelta(days=length), s - pd.Timedelta(days=1))[metric]
        cur["Prev"] = prev.reindex(cur.index)
    else:
        cur["Prev"] = float("nan")
    cur = cur.sort_values([metric, "Sales"], ascending=False).head(top_n).reset_index()
    mix = {}
    if df is not None and len(codes):
        per = df[(df["D"] >= s) & (df["D"] <= e) & df["Key"].isin(cur["Key"])].groupby("Key")[list(codes)].sum()
        mix = {k: " · ".join(f"{c} {int(v)}" for c, v in row.items() if v > 0) for k, row in per.iterrows()}
    out = pd.DataFrame({
        "Rank": range(1, len(cur) + 1),
        "Customer": cur["Key"].map(lambda k: names.get(k, k)),
        "Area": cur["Key"].map(lambda k: areas.get(k, AREA_LABEL["Unknown"])),
        "Orders (days)": cur["Orders"].astype(int),
        "Cases": cur["Cases"].round(1),
        "Bun pcs": cur["Pcs"].round(0).astype("int64"),
        "Sales ៛": cur["Sales"].round(0).astype("int64"),
        "Avg order ៛": (cur["Sales"] / cur["Orders"].clip(lower=1)).round(0).astype("int64"),
        "Buns by type": cur["Key"].map(lambda k: mix.get(k, "")),
        "Share %": (cur[metric] / total * 100).round(1) if total else 0.0,
        "Last order": cur["Last"].dt.strftime("%Y-%m-%d"),
        "vs previous %": ((cur[metric] - cur["Prev"]) / cur["Prev"] * 100).where(cur["Prev"] > 0).round(0),
    })
    return out, total


def _si_habits(daily, today, min_orders=4, lookback=180, factor=1.5, dormant_factor=4.0, names=None, areas=None):
    """Usual ordering rhythm of each customer and whether they are late. Status: On track | Missing | Dormant.
    Works on plain number arrays per customer (about 10x faster than pandas per group)."""
    import numpy as np
    names, areas = names or {}, areas or {}
    t = pd.Timestamp(today)
    d = daily[daily["D"] >= t - pd.Timedelta(days=lookback)].sort_values(["Key", "D"], kind="mergesort")
    rows = []
    if not d.empty:
        keys = d["Key"].to_numpy()
        days = d["D"].to_numpy().astype("datetime64[D]").astype("int64")
        sales = d["Sales"].to_numpy(dtype="float64")
        pcs = d["Pcs"].to_numpy(dtype="float64")
        cases = pd.to_numeric(d["Cases"], errors="coerce").to_numpy(dtype="float64")
        custs = d["Customer"].to_numpy()
        t_day = int(np.datetime64(t.normalize(), "D").astype("int64"))
        starts = np.flatnonzero(np.r_[True, keys[1:] != keys[:-1]])
        ends = np.r_[starts[1:], len(keys)]
        day_names = "Mon Tue Wed Thu Fri Sat Sun".split()
        for s0, e0 in zip(starts, ends):
            n = e0 - s0
            if n < min_orders:
                continue
            key = keys[s0]
            dts = days[s0:e0]
            gaps = np.diff(dts).astype("float64")
            gap = max(1.0, float(np.median(gaps))) if len(gaps) else 1.0
            gm = gaps.mean() if len(gaps) else 0.0
            cv = float(gaps.std(ddof=1) / gm) if len(gaps) > 1 and gm > 0 else 0.0
            last_i = int(dts[-1])
            last = pd.Timestamp(np.datetime64(last_i, "D"))
            since = int(t_day - last_i)
            late_at = max(gap * factor, gap + 1)
            dormant_at = max(min(gap * dormant_factor, 90), late_at + 1)
            status = "Dormant" if since > dormant_at else ("Missing" if since >= late_at else "On track")
            wd = np.bincount(((dts + 3) % 7).astype("int64"), minlength=7)      # 1970-01-01 was a Thursday
            wd_name = day_names[int(wd.argmax())] if wd.max() / n >= 0.5 else "-"
            avg_order = float(sales[s0:e0].mean())
            avg_pcs = float(pcs[s0:e0].mean())
            cs = cases[s0:e0]
            cs = cs[~np.isnan(cs)]
            usual_cases = round(float(np.median(cs)), 1) if len(cs) else float("nan")
            cycles = max(1, int(since // gap)) if status != "On track" else 0
            rows.append({
                "Key": key, "Customer": names.get(key, custs[s0]), "Area": areas.get(key, AREA_LABEL["Unknown"]),
                "Orders in period": int(n), "Usual gap (days)": round(gap, 1), "Usual day": wd_name,
                "Pattern": "🟢 Regular" if cv <= 0.6 else "🟡 Irregular",
                "Last order": last.strftime("%Y-%m-%d"), "Days since": since,
                "Expected by": (last + pd.Timedelta(days=gap)).strftime("%Y-%m-%d"),
                "Days late": max(0, int(round(since - gap))), "Usual cases": usual_cases,
                "Usual pcs": int(round(float(np.median(pcs[s0:e0])))), "Avg order ៛": int(round(avg_order)),
                "Missed orders (est.)": cycles, "Lost pcs (est.)": int(round(cycles * avg_pcs)),
                "Lost sales ៛ (est.)": int(round(cycles * avg_order)), "Status": status})
    cols = ["Key", "Customer", "Area", "Orders in period", "Usual gap (days)", "Usual day", "Pattern", "Last order",
            "Days since", "Expected by", "Days late", "Usual cases", "Usual pcs", "Avg order ៛",
            "Missed orders (est.)", "Lost pcs (est.)", "Lost sales ៛ (est.)", "Status"]
    return pd.DataFrame(rows, columns=cols)


def _si_month_avgs(mon, daily, today):
    """Average per month the customer really BOUGHT (months with no purchase are not counted), and what it is based on.
    Only finished months are used. A customer with no finished month yet gets this month so far, based on order days."""
    cur_m = pd.Timestamp(today).strftime("%Y-%m")
    done = {m for m in mon["Month"].unique() if m < cur_m}
    p = mon[mon["Month"].isin(done) & (mon["Pcs"] > 0)].groupby("Key").agg(P=("Pcs", "sum"), n=("Month", "nunique"))
    dd = daily.assign(Month=daily["D"].dt.strftime("%Y-%m"))
    ms = dd[dd["Month"].isin(done)].groupby(["Key", "Month"])["Sales"].sum().reset_index()
    ms = ms[ms["Sales"] > 0].groupby("Key").agg(S=("Sales", "sum"), ns=("Month", "nunique"))
    cm = dd[dd["Month"] == cur_m].groupby("Key").agg(Pm=("Pcs", "sum"), Sm=("Sales", "sum"), days=("D", "nunique"))
    rows = {}
    for k in set(p.index) | set(ms.index) | set(cm.index):
        if k in p.index:
            avg_p, basis = p.loc[k, "P"] / p.loc[k, "n"], f"{int(p.loc[k, 'n'])} month(s)"
        elif k in cm.index:
            avg_p, basis = cm.loc[k, "Pm"], f"{int(cm.loc[k, 'days'])} day(s) this month"
        else:
            avg_p, basis = float("nan"), "-"
        if k in ms.index:
            avg_s = ms.loc[k, "S"] / ms.loc[k, "ns"]
            if k in p.index and int(ms.loc[k, "ns"]) != int(p.loc[k, "n"]):
                basis += f" · ៛ from {int(ms.loc[k, 'ns'])}"
        elif k in cm.index and k not in p.index:
            avg_s = cm.loc[k, "Sm"]
        else:
            avg_s = float("nan")
            if k in p.index:
                basis += " · ៛ n/a"
        rows[k] = {"AvgPcs": avg_p, "AvgSales": avg_s, "Basis": basis}
    return pd.DataFrame.from_dict(rows, orient="index", columns=["AvgPcs", "AvgSales", "Basis"])


def _si_avg_get(avgs, key):
    if avgs is not None and key in avgs.index:
        r = avgs.loc[key]
        return r["AvgPcs"], r["AvgSales"], r["Basis"]
    return float("nan"), float("nan"), "-"


def _si_no_order(daily, names, areas, month_start, month_end, today, avgs=None):
    """Customers (master list + journal) with no order in the chosen month."""
    s, e = pd.Timestamp(month_start), pd.Timestamp(month_end)
    ref = min(pd.Timestamp(today), e)
    ordered = set(daily.loc[(daily["D"] >= s) & (daily["D"] <= e), "Key"])
    prev_end = s - pd.Timedelta(days=1)
    prev_start = prev_end.replace(day=1)
    in_prev = set(daily.loc[(daily["D"] >= prev_start) & (daily["D"] <= prev_end), "Key"])
    before = daily[daily["D"] < s]
    last = before.groupby("Key")["D"].max()
    cnt = before.groupby("Key")["D"].nunique()
    rows = []
    for key, name in names.items():
        if key in ordered:
            continue
        if key in last.index:
            group = "Ordered last month" if key in in_prev else "Ordered earlier"
            rows.append({"Group": group, "Customer": name, "Area": areas.get(key, AREA_LABEL["Unknown"]),
                         "Last order": last[key].strftime("%Y-%m-%d"), "Days since": int((ref - last[key]).days),
                         "Total order days": int(cnt[key]), "Avg pcs/month": _si_avg_get(avgs, key)[0],
                         "Avg ៛/month": _si_avg_get(avgs, key)[1], "Avg based on": _si_avg_get(avgs, key)[2]})
        else:
            rows.append({"Group": "Never ordered", "Customer": name, "Area": areas.get(key, AREA_LABEL["Unknown"]),
                         "Last order": "-", "Days since": None, "Total order days": 0, "Avg pcs/month": float("nan"),
                         "Avg ៛/month": float("nan"), "Avg based on": "-"})
    cols = ["Group", "Customer", "Area", "Last order", "Days since", "Total order days", "Avg pcs/month",
            "Avg ៛/month", "Avg based on"]
    out = pd.DataFrame(rows, columns=cols)
    rank = {"Ordered last month": 0, "Ordered earlier": 1, "Never ordered": 2}
    if out.empty:
        return out
    out["Days since"] = out["Days since"].astype("Int64")
    out["_r"] = out["Group"].map(rank)
    out = out.sort_values(["_r", "Avg pcs/month", "Customer"], ascending=[True, False, True], na_position="last").drop(columns="_r")
    for c in ("Avg pcs/month", "Avg ៛/month"):
        out[c] = out[c].round(0).astype("Int64")
    return out.reset_index(drop=True)


# ---------- possible duplicate customer names (same shop written two ways) ----------
SI_ALIAS_COLS = ["Date", "Customer", "Same as", "Decision", "By"]
SI_DUP_MIN = 0.80                 # name likeness (0-1) from which two names are shown as "maybe the same customer"


def _si_name_tokens(name):
    t = unicodedata.normalize("NFC", str(name)).replace("​", "").replace("‌", "").replace("្ដ", "្ត")
    t = re.sub(r"([A-Za-z])([^\sA-Za-z0-9])", r"\1 \2", t)          # "COFFEEចោមចៅ" -> "COFFEE ចោមចៅ"
    return [w.upper() for w in re.split(r"[\s(),.\-_/:]+", t) if len(w) >= 2]


def _si_name_score(a, b, word_count):
    """0-1. Rare words (a person's name) count much more than common words (khan, province, 'MART', 'AEON'):
    two shops in the same place with different owners are not the same customer."""
    import difflib
    ka, kb = _visit_match_key(a), _visit_match_key(b)
    if not ka or not kb:
        return 0.0
    if ka == kb:
        return 1.0
    r = difflib.SequenceMatcher(None, ka, kb).ratio()
    ta, tb = _si_name_tokens(a), _si_name_tokens(b)
    if not ta or not tb:
        return r * 0.8
    short, long_ = (ta, tb) if len(ta) <= len(tb) else (tb, ta)
    def sim(x):
        return max(1.0 if x == y else difflib.SequenceMatcher(None, x, y).ratio() for y in long_)
    sims = {x: sim(x) for x in short}
    weight = {x: 1.0 / max(1, word_count.get(x, 1)) for x in short}
    total = sum(weight.values())
    cover = sum(w for x, w in weight.items() if sims[x] >= 0.75) / total if total else 0.0
    rare_match = any(word_count.get(x, 1) <= 3 and sims[x] >= 0.75 for x in short)
    if not rare_match:
        return r if r >= 0.9 else r * 0.6
    return 0.6 * cover + 0.4 * r


@st.cache_data(show_spinner=False, max_entries=6)
def _si_dup_scan(missing_items, ordered_items, all_names):
    """{missing key: (ordered key, score)} best look-alike that DID order, for every customer without an order."""
    import difflib
    word_count = Counter()
    for n in set(all_names):
        word_count.update(set(_si_name_tokens(n)))
    okeys = [(k, n, _visit_match_key(n)) for k, n in ordered_items]
    gidx = _gram_index([o[2] for o in okeys])
    out = {}
    for k, n in missing_items:
        mk = _visit_match_key(n)
        best = None
        for j in _gram_shortlist(mk, gidx, 0.3):
            ok, on, omk = okeys[j]
            if ok == k or not mk or not omk:
                continue
            if mk != omk:
                sm = difflib.SequenceMatcher(None, mk, omk)
                if sm.real_quick_ratio() < 0.45 or sm.quick_ratio() < 0.45:
                    continue
            sc = _si_name_score(n, on, word_count)
            if sc >= SI_DUP_MIN and (best is None or sc > best[1]):
                best = (ok, round(sc, 2))
        if best:
            out[k] = best
    return out


def _si_alias_read():
    try:
        return read_raw(SI_ALIAS_FILE, SI_ALIAS_COLS, max_age=60)
    except Exception:
        return pd.DataFrame(columns=SI_ALIAS_COLS)


def _si_alias_decisions():
    """-> (same: {key: set(keys)}, different: set(frozenset({key, key}))). The newest decision for a pair wins."""
    df = _si_alias_read()
    pairs = {}
    for r in df.to_dict("records"):
        a, b = norm_name(r.get("Customer", "")), norm_name(r.get("Same as", ""))
        if a and b and a != b:
            pairs[frozenset((a, b))] = str(r.get("Decision", ""))
    same, diff = {}, set()
    for pair, dec in pairs.items():
        a, b = tuple(pair)
        if dec == "Same":
            same.setdefault(a, set()).add(b)
            same.setdefault(b, set()).add(a)
        elif dec == "Different":
            diff.add(pair)
    return same, diff


def _si_alias_save(name, same_as, decision):
    if not has_permission("edit"):
        raise PermissionError("Your account needs Create, edit, and submit changes permission.")
    row = {"Date": now_str(), "Customer": safe_text(name, maxlen=MAX_TEXT), "Same as": safe_text(same_as, maxlen=MAX_TEXT),
           "Decision": decision, "By": current_user() or "-"}
    modify_csv(SI_ALIAS_FILE, SI_ALIAS_COLS, lambda f: pd.concat([f, pd.DataFrame([row])], ignore_index=True))
    audit("customer same-name decision", f"{name} | {same_as} | {decision}")


def _si_no_order_split(table, daily, names, month_start, month_end):
    """Remove customers who DID order under another spelling (remembered until the data or a decision changes).
    -> (table without them, review table of look-alikes, number hidden because Admin confirmed / same spelling)."""
    if table is None or table.empty or daily.empty:
        return table, pd.DataFrame(), 0
    try:
        _si_alias_read()                                    # refresh the decisions file first
        key = (_si_frame_sig(table), _si_frame_sig(daily), str(month_start), str(month_end), _file_sig(SI_ALIAS_FILE))
    except Exception:
        key = None
    memo = st.session_state.setdefault("_si_split_memo", {})
    if key is not None and key in memo:
        return memo[key]
    out = _si_no_order_split_calc(table, daily, names, month_start, month_end)
    if key is not None:
        if len(memo) > 6:
            memo.clear()
        memo[key] = out
    return out


def _si_no_order_split_calc(table, daily, names, month_start, month_end):
    s, e = pd.Timestamp(month_start), pd.Timestamp(month_end)
    month = daily[(daily["D"] >= s) & (daily["D"] <= e)]
    if month.empty:
        return table, pd.DataFrame(), 0
    ordered = month.groupby("Key").agg(Customer=("Customer", "first"), Pcs=("Pcs", "sum"), Last=("D", "max"))
    same, diff = _si_alias_decisions()
    keys = table["Customer"].map(norm_name)
    confirmed = keys.map(lambda k: bool(same.get(k, set()) & set(ordered.index)))
    scan = _si_dup_scan(tuple(sorted(zip(keys[~confirmed], table.loc[~confirmed, "Customer"]))),
                        tuple(sorted(zip(ordered.index, ordered["Customer"]))),
                        tuple(sorted(set(names.values()) | set(ordered["Customer"]))))
    auto_same, review = set(), []
    for k, cust in zip(keys[~confirmed], table.loc[~confirmed, "Customer"]):
        hit = scan.get(k)
        if not hit or frozenset((k, hit[0])) in diff:
            continue
        o = ordered.loc[hit[0]]
        if hit[1] >= 1.0:
            auto_same.add(k)                  # identical apart from spaces / punctuation / spelling marks
            continue
        review.append({"Customer": cust, "Ordered as": o["Customer"], "Pcs this month": int(o["Pcs"]),
                       "Last order (other name)": o["Last"].strftime("%Y-%m-%d"), "Likeness %": int(round(hit[1] * 100))})
    review = pd.DataFrame(review)
    hide = confirmed | keys.isin(auto_same) | (keys.isin(set(review["Customer"].map(norm_name))) if not review.empty else False)
    if not review.empty:
        review = review.sort_values("Likeness %", ascending=False).reset_index(drop=True)
    return table[~hide].reset_index(drop=True), review, int(confirmed.sum() + len(auto_same))


def _si_contacted_map(history, month_start):
    """{customer key: latest contact (dict) recorded on or after month_start}."""
    if history is None or history.empty:
        return {}
    h = history.copy()
    h["_d"] = pd.to_datetime(h["Date"], errors="coerce")
    h = h[h["_d"] >= pd.Timestamp(month_start)]
    if h.empty:
        return {}
    h["_k"] = h["Customer"].map(norm_name)
    return {r["_k"]: r for r in h.drop_duplicates("_k", keep="last").to_dict("records")}


def _si_contact_text(c):
    if not c:
        return "⏳ មិនទាន់ទាក់ទង"
    d = pd.to_datetime(c.get("Date"), errors="coerce")
    bits = [f"✅ {d:%d %b}" if pd.notna(d) else "✅", _si_platform_of(c)]
    for col in ("Notes", "Recorded by"):
        v = str(c.get(col, "") or "").strip()
        if v and v not in ("-", "nan"):
            bits.append(v[:60])
    return " · ".join(b for b in bits if b)


def _si_no_order_contact_table(frame, history, month_start, key, height=420):
    """No-order list with a ✅ contacted state per customer. Tick, choose platform, Save -> saved in call history."""
    if frame.empty:
        st.caption("គ្មាន")
        return
    # Contacted = a contact saved AFTER the customer's last order (so it does not reset on the 1st of the month).
    # Customers who never ordered: a contact in the last 60 days.
    calls = _si_contacted_map(history, pd.Timestamp(month_start) - pd.Timedelta(days=400))
    view = frame.copy()
    view["_k"] = view["Customer"].map(norm_name)
    contacted = {}
    for k, last in zip(view["_k"], view.get("Last order", pd.Series("-", index=view.index))):
        c = calls.get(k)
        if not c:
            continue
        cd = pd.to_datetime(c.get("Date"), errors="coerce")
        lo = pd.to_datetime(last, errors="coerce")
        if pd.notna(cd) and ((pd.notna(lo) and cd.normalize() > lo.normalize())
                             or (pd.isna(lo) and cd >= pd.Timestamp(today_kh()) - pd.Timedelta(days=60))):
            contacted[k] = c
    view["Contact"] = view["_k"].map(lambda k: _si_contact_text(contacted.get(k)))
    n_done = int(view["_k"].isin(contacted).sum())
    f1, f2 = st.columns([3, 2])
    show = f1.radio("បង្ហាញ", ["ទាំងអស់", "⏳ មិនទាន់ទាក់ទង", "✅ ទាក់ទងហើយ"], horizontal=True, key=f"{key}_flt")
    f2.caption(f"✅ ទាក់ទងហើយ {n_done} / {len(view)} នាក់ (ក្រោយការបញ្ជាទិញចុងក្រោយ)")
    if show.startswith("⏳"):
        view = view[~view["_k"].isin(contacted)]
    elif show.startswith("✅"):
        view = view[view["_k"].isin(contacted)]
    if view.empty:
        st.caption("គ្មាន")
        return
    view.insert(0, "✅ ទាក់ទងហើយ", view["_k"].isin(contacted))
    view["Platform"] = [(_si_platform_of(contacted[k]) if k in contacted else "") or _si_platform_guess(history, c)
                        for k, c in zip(view["_k"], view["Customer"])]
    view["Outcome"] = [contacted[k].get("Outcome") if k in contacted and contacted[k].get("Outcome") in CALL_OUTCOMES
                       else "Reached customer" for k in view["_k"]]
    view["Note"] = ""
    show_cols = ["✅ ទាក់ទងហើយ", "Customer", "Area", "Last order", "Days since", "Avg pcs/month", "Contact", "Platform", "Outcome", "Note"]
    show_cols = [c for c in show_cols if c in view.columns]
    base = view[show_cols + ["_k"]].reset_index(drop=True)
    ver = st.session_state.get(f"{key}_ver", 0)
    can_edit = has_permission("edit")
    edited = st.data_editor(
        base[show_cols], hide_index=True, use_container_width=True, height=min(height, 38 + 35 * (len(base) + 1)),
        key=f"{key}_ed_{ver}", disabled=[c for c in show_cols if c not in ("✅ ទាក់ទងហើយ", "Platform", "Outcome", "Note")] if can_edit else True,
        column_config={
            "✅ ទាក់ទងហើយ": st.column_config.CheckboxColumn("✅ ទាក់ទងហើយ", help="Tick when you have contacted this customer, then press Save."),
            "Platform": st.column_config.SelectboxColumn("Platform", options=CALL_PLATFORMS, required=True,
                                                         help="Picked automatically from the last contact. Change it if needed."),
            "Outcome": st.column_config.SelectboxColumn("Outcome", options=CALL_OUTCOMES, required=True),
            "Note": st.column_config.TextColumn("Note (optional)", max_chars=500),
            "Contact": st.column_config.TextColumn("ស្ថានភាពទាក់ទង"),
            "Avg pcs/month": st.column_config.NumberColumn("Avg pcs/month", format="%d"),
        })
    if not can_edit:
        return
    new = [(i, r) for i, r in edited.iterrows() if bool(r["✅ ទាក់ទងហើយ"]) and base.at[i, "_k"] not in contacted]
    if st.button(f"💾 រក្សាទុក ({len(new)} នាក់ ទាក់ទងហើយ)", key=f"{key}_save", disabled=not new, type="primary"):
        saved, errors = 0, []
        latest = _si_call_latest(history) if history is not None and not history.empty else pd.DataFrame()
        prev = latest.set_index("_key").to_dict("index") if not latest.empty else {}
        for i, r in new:
            k = base.at[i, "_k"]
            p = prev.get(k, {})
            status = p.get("Customer status") if p.get("Customer status") in CALL_STATUSES else "Active"
            if status == "Do not contact":
                errors.append(f"{r['Customer']}: marked Do not contact")
                continue
            row = {"Date": now_str(), "Customer": r["Customer"],
                   "CallID": hashlib.sha256(f"{k}|{today_kh()}|{current_user()}|noorder".encode()).hexdigest()[:32],
                   "Outcome": r["Outcome"], "Notes": str(r.get("Note") or "").strip() or "Contacted: no order this month",
                   "Customer status": status, "Contact person": p.get("Contact person", ""), "Phone": p.get("Phone", ""),
                   "Next action": "", "Follow-up date": "", "Assigned to": current_user() or "", "Recorded by": current_user() or "-",
                   "Reason": "Not specified", "Follow-up state": "No follow-up", "Priority": "Normal", "Result": "",
                   "Platform": r["Platform"]}
            try:
                _si_save_call(row)
                saved += 1
            except Exception as e:
                errors.append(f"{r['Customer']}: {str(e)[:80]}")
        st.session_state[f"{key}_ver"] = ver + 1
        if errors:
            st.warning("មិនបានរក្សាទុក: " + "; ".join(errors[:5]))
        st.session_state["flash"] = f"✅ បានកត់ត្រា {saved} នាក់ ថាទាក់ទងហើយ"
        st.rerun()


def _si_dup_review(review, key="si_dup", all_names=()):
    """Table of look-alike names (one did not order, the other did). Choose ✅ Same / ❌ Different per row, then Save."""
    st.markdown(f"**🔁 ប្រហែលជាអតិថិជនដដែល — បានបញ្ជាទិញក្រោមឈ្មោះផ្សេង ({len(review)})**")
    can = has_permission("edit")
    if not review.empty:
        st.caption("ឈ្មោះទាំងនេះមិនបង្ហាញក្នុងតារាង 'មិនបញ្ជាទិញ' ខាងក្រោមទេ រហូតដល់អ្នកសម្រេច។ ជ្រើស ✅ ដូចគ្នា ឬ ❌ ផ្សេងគ្នា "
                   "ក្នុងជួរ 'សម្រេច' (ឬប្រើប៊ូតុងជ្រើសទាំងអស់) ហើយចុច 💾 រក្សាទុក។ "
                   "✅ ដូចគ្នា = ចាត់ទុកជាអតិថិជនតែមួយ · ❌ ផ្សេងគ្នា = បង្ហាញវិញ ហើយមិនសួរទៀត។")
        CHOICES = ["—", "✅ ដូចគ្នា", "❌ ផ្សេងគ្នា"]
        ver = st.session_state.get(f"{key}_ver", 0)
        preset = st.session_state.get(f"{key}_preset", "—")
        b1, b2, b3, _sp = st.columns([1.4, 1.4, 1.6, 3])
        if b1.button("✅ ជ្រើស ≥95% ជាដូចគ្នា", key=f"{key}_p95", disabled=not can, use_container_width=True):
            st.session_state[f"{key}_preset"] = "95"
            st.session_state[f"{key}_ver"] = ver + 1
            st.rerun()
        if b2.button("✅ ជ្រើសទាំងអស់ ដូចគ្នា", key=f"{key}_pall", disabled=not can, use_container_width=True):
            st.session_state[f"{key}_preset"] = "all"
            st.session_state[f"{key}_ver"] = ver + 1
            st.rerun()
        if b3.button("↩️ សម្អាតការជ្រើស", key=f"{key}_pclr", disabled=not can, use_container_width=True):
            st.session_state[f"{key}_preset"] = "—"
            st.session_state[f"{key}_ver"] = ver + 1
            st.rerun()
        view = review.copy()
        view.insert(0, "សម្រេច", ["✅ ដូចគ្នា" if preset == "all" or (preset == "95" and p >= 95) else "—"
                                  for p in view["Likeness %"]])
        edited = st.data_editor(
            view, hide_index=True, use_container_width=True, key=f"{key}_ed_{ver}",
            height=min(520, 38 + 35 * (len(view) + 1)),
            disabled=[c for c in view.columns if c != "សម្រេច"] if can else True,
            column_config={
                "សម្រេច": st.column_config.SelectboxColumn("សម្រេច", options=CHOICES, required=True, width="small"),
                "Customer": st.column_config.TextColumn("ឈ្មោះមិនបញ្ជាទិញ"),
                "Ordered as": st.column_config.TextColumn("បានបញ្ជាទិញជា"),
                "Pcs this month": st.column_config.NumberColumn("Pcs ខែនេះ", format="%d"),
                "Last order (other name)": st.column_config.TextColumn("បញ្ជាទិញចុងក្រោយ"),
                "Likeness %": st.column_config.ProgressColumn("ស្រដៀង", min_value=0, max_value=100, format="%d%%"),
            })
        picked = edited[edited["សម្រេច"] != "—"] if can else edited.iloc[0:0]
        n_same = int((picked["សម្រេច"] == "✅ ដូចគ្នា").sum())
        n_diff = len(picked) - n_same
        if st.button(f"💾 រក្សាទុក ({n_same} ដូចគ្នា · {n_diff} ផ្សេងគ្នា)", key=f"{key}_save", type="primary",
                     disabled=picked.empty):
            done, errs = 0, []
            for r in picked.to_dict("records"):
                try:
                    _si_alias_save(r["Customer"], r["Ordered as"], "Same" if r["សម្រេច"].startswith("✅") else "Different")
                    done += 1
                except Exception as e:
                    errs.append(f"{r['Customer']}: {str(e)[:60]}")
            st.session_state[f"{key}_preset"] = "—"
            st.session_state[f"{key}_ver"] = ver + 1
            if errs:
                st.warning("មិនបានរក្សាទុក: " + "; ".join(errs[:5]))
            st.session_state["flash"] = f"✅ បានរក្សាទុក {done} ការសម្រេច ({n_same} ដូចគ្នា · {n_diff} ផ្សេងគ្នា)"
            st.rerun()
    else:
        st.caption("រកមិនឃើញឈ្មោះស្រដៀងគ្នាទេ។")
    with st.expander("🔗 ភ្ជាប់ឈ្មោះ 2 ដោយខ្លួនឯង (ឈ្មោះដែលកម្មវិធីរកមិនឃើញ)"):
        opts = sorted(set(all_names), key=str.casefold)
        if not opts or not can:
            st.caption("មិនមានឈ្មោះ ឬគណនីរបស់អ្នកមិនអាចកែបាន។")
        else:
            c1, c2 = st.columns(2)
            n1 = c1.selectbox("ឈ្មោះទី 1", opts, index=None, key=f"{key}_m1", placeholder="វាយឈ្មោះ…")
            n2 = c2.selectbox("ឈ្មោះទី 2 (អតិថិជនតែមួយ)", opts, index=None, key=f"{key}_m2", placeholder="វាយឈ្មោះ…")
            ok = bool(n1 and n2 and n1 != n2)
            if st.button("✅ ចាត់ទុកជាអតិថិជនតែមួយ", key=f"{key}_mset", disabled=not ok) and ok:
                try:
                    _si_alias_save(n1, n2, "Same")
                    st.session_state["flash"] = f"✅ {n1} = {n2}"
                    st.rerun()
                except Exception as e:
                    st.error(str(e)[:150])
        same, _diff = _si_alias_decisions()
        saved = _si_alias_read()
        if not saved.empty:
            st.markdown("**ការសម្រេចដែលបានរក្សាទុក**")
            last = saved.assign(_p=[frozenset((norm_name(a), norm_name(b))) for a, b in zip(saved["Customer"], saved["Same as"])])
            last = last.drop_duplicates("_p", keep="last").drop(columns=["_p", "_dt"], errors="ignore").iloc[::-1]
            st.dataframe(last, hide_index=True, use_container_width=True, height=min(300, 38 + 35 * (len(last) + 1)))
            undo = st.selectbox("ដកការសម្រេចចេញ (សួរម្តងទៀត)", [f"{a} ↔ {b}" for a, b in zip(last["Customer"], last["Same as"])],
                                index=None, key=f"{key}_undo", placeholder="ជ្រើសដើម្បីដកចេញ…")
            if undo and st.button("↩️ ដកចេញ", key=f"{key}_undo_btn", disabled=not can):
                a, b = undo.split(" ↔ ", 1)
                try:
                    _si_alias_save(a, b, "Undecided")
                    st.session_state["flash"] = "↩️ បានដកការសម្រេចចេញ"
                    st.rerun()
                except Exception as e:
                    st.error(str(e)[:150])

def _si_care(daily, df, codes, habits, names, areas, today, month_start, avgs=None, measure="Pcs"):
    """Rule-based customer-care list: who to contact, why, and what to say / offer."""
    t = pd.Timestamp(today)
    if daily.empty:
        return pd.DataFrame()
    d90 = daily[daily["D"] > t - pd.Timedelta(days=90)]
    d30 = daily[daily["D"] > t - pd.Timedelta(days=30)]
    p30 = daily[(daily["D"] > t - pd.Timedelta(days=60)) & (daily["D"] <= t - pd.Timedelta(days=30))]
    mcol = "Pcs" if measure == "Pcs" else "Sales"                       # measure customers by bun pieces or by riel
    unit = "pcs" if measure == "Pcs" else "៛"
    s90, s30, sp30 = (x.groupby("Key")[mcol].sum() for x in (d90, d30, p30))
    c_last, c_prev, c_avg = f"Last 30d {unit}", f"Prev 30d {unit}", f"Avg {unit}/month"
    first, last = daily.groupby("Key")["D"].min(), daily.groupby("Key")["D"].max()
    total_days = daily.groupby("Key")["D"].nunique()
    this_month = set(daily.loc[daily["D"] >= pd.Timestamp(month_start), "Key"])
    active = s90[s90 > 0]
    vip_cut = active.quantile(0.8) if len(active) >= 5 else (active.max() if len(active) else 0)
    vips = set(active[active >= vip_cut].index) if len(active) else set()
    hab = habits.set_index("Key") if not habits.empty else pd.DataFrame()
    best = []
    if codes and not df.empty:
        recent = df[df["D"] > t - pd.Timedelta(days=90)]
        best = list(recent[codes].sum().sort_values(ascending=False).head(3).index)
        mine = recent.groupby("Key")[codes].sum()
    else:
        mine = pd.DataFrame()
    rows = []
    for key in last.index:
        since = int((t - last[key]).days)
        if since > 180:
            continue                                                       # lost long ago: not a care case
        h = hab.loc[key] if (not hab.empty and key in hab.index) else None
        status = h["Status"] if h is not None else ""
        a30, b30 = float(s30.get(key, 0)), float(sp30.get(key, 0))
        _ap, _as, basis = _si_avg_get(avgs, key)
        avg_p = _ap if measure == "Pcs" else _as
        if measure == "Pcs":
            basis = str(basis).split(" · ")[0]
        avg_txt = (f"≈{avg_p:,.0f} {unit}" if pd.notna(avg_p) else f"≈- {unit}") + f" per month, based on {basis}"
        chg = (a30 - b30) / b30 * 100 if b30 > 0 else None
        is_vip = key in vips
        no_order_month = key not in this_month
        gap = float(h["Usual gap (days)"]) if h is not None else None
        usual_cases = h["Usual cases"] if h is not None else None
        seg = pr = why = act = None
        if is_vip and (status in ("Missing", "Dormant") or (no_order_month and since >= 14)):
            seg, pr = "🔴 VIP at risk", 1
            why = f"Top customer ({avg_txt}) but no order for {since} days" + (f"; usually every {gap:g} days" if gap else "")
            act = "Call the owner personally today. Ask if anything went wrong (quality, price, late delivery) and offer to take the usual order now."
        elif status == "Missing":
            seg, pr = "🟠 Missed usual order", 2
            why = f"Usually orders every ~{gap:g} days (≈{usual_cases:g} cases / {h['Usual pcs']:,} pcs), now {since} days without an order"
            act = "Message or call: remind them and offer their usual order for the next delivery day."
        elif chg is not None and chg <= -40 and a30 >= 0:
            seg, pr = "🟠 Ordering less", 2
            why = f"Last 30 days {a30:,.0f} {unit} vs {b30:,.0f} {unit} the 30 days before ({chg:.0f}%)"
            act = "Ask for feedback: stock, price, quality or delivery problem? Check if another supplier is taking part of the order."
        elif status == "Dormant" or (45 <= since <= 180 and total_days[key] >= 2 and status != "On track"):
            seg, pr = "🟡 Win-back", 3
            why = f"No order for {since} days (last: {last[key]:%Y-%m-%d})"
            act = "Visit or call to win them back. Consider a free sample (FOC) of a best seller with the next order."
        elif (t - first[key]).days <= 30:
            seg, pr = "🟢 New customer", 4
            why = f"First order {first[key]:%Y-%m-%d}; {int(total_days[key])} order day(s) so far"
            act = "Call after the first delivery: is the quality OK? Confirm their usual order day and save their phone and map location."
        elif chg is not None and chg >= 40 and b30 > 0:
            seg, pr = "🟢 Growing", 4
            why = f"Last 30 days {a30:,.0f} {unit} vs {b30:,.0f} {unit} before (+{chg:.0f}%)"
            act = "Thank them, check stock is ready for the higher volume, and suggest extra bun types."
        elif is_vip:
            seg, pr = "⭐ VIP – keep happy", 5
            why = f"Top 20% customer ({avg_txt}), ordering normally"
            act = "Give stock priority, send a thank-you at month end and ask for feedback or a referral."
        if seg is None:
            continue
        tip = ""
        if len(mine) and key in mine.index and best:
            miss = [c for c in best if mine.loc[key, c] <= 0]
            tip = ("Try offering: " + ", ".join(miss)) if miss else ""
        rows.append({"Priority": pr, "Segment": seg, "Customer": names.get(key, key), "Area": areas.get(key, AREA_LABEL["Unknown"]),
                     "Why": why, "Suggested action": act, "Cross-sell idea": tip, "Last order": f"{last[key]:%Y-%m-%d}",
                     c_last: int(round(a30)), c_prev: int(round(b30)),
                     "Change %": round(chg) if chg is not None else None,
                     c_avg: avg_p, "Avg based on": basis})
    out = pd.DataFrame(rows, columns=["Priority", "Segment", "Customer", "Area", "Why", "Suggested action",
                                      "Cross-sell idea", "Last order", c_last, c_prev, "Change %",
                                      c_avg, "Avg based on"])
    if out.empty:
        return out
    out = out.sort_values(["Priority", c_avg], ascending=[True, False], na_position="last").reset_index(drop=True)
    out[c_avg] = pd.to_numeric(out[c_avg], errors="coerce").round(0).astype("Int64")
    out["Change %"] = pd.to_numeric(out["Change %"], errors="coerce").round(0).astype("Int64")
    return out


def _si_monthly_table(hist_monthly, daily):
    """Bun pieces per customer per month: the monthly file for older months + the daily data for every month it covers."""
    d = daily.copy()
    d["Month"] = d["D"].dt.strftime("%Y-%m")
    dm = d.groupby(["Month", "Key"], as_index=False).agg(Customer=("Customer", "first"), Pcs=("Pcs", "sum"))
    parts = [dm]
    if hist_monthly is not None and not hist_monthly.empty and {"Month", "Customer", "Pcs"} <= set(hist_monthly.columns):
        m = hist_monthly.copy()
        m["Key"] = m["Customer"].map(norm_name)
        m["Pcs"] = pd.to_numeric(m["Pcs"], errors="coerce").fillna(0)
        m = m[~m["Month"].isin(set(dm["Month"])) & ~m["Customer"].astype(str).str.strip().str.upper().isin(SI_IGNORE_NAMES)]
        parts.append(m[["Month", "Key", "Customer", "Pcs"]])
    allm = pd.concat(parts, ignore_index=True)
    return allm.groupby(["Month", "Key"], as_index=False).agg(Customer=("Customer", "first"), Pcs=("Pcs", "sum"))


def _si_month_summary(mon):
    rows, prev = [], set()
    for m in sorted(mon["Month"].unique()):
        cur = mon[(mon["Month"] == m) & (mon["Pcs"] > 0)]
        act = set(cur["Key"])
        rows.append({"Month": m, "Bun pcs": int(cur["Pcs"].sum()), "Active customers": len(act),
                     "New / resumed": len(act - prev) if prev else 0, "Dropped (ordered last month, not now)": len(prev - act) if prev else 0})
        prev = act
    return pd.DataFrame(rows)


def _si_month_detail(mon, month, names, areas, top_n=20):
    months = sorted(mon["Month"].unique())
    i = months.index(month)
    prev_m = months[i - 1] if i > 0 else None
    cur = mon[mon["Month"] == month].set_index("Key")["Pcs"]
    prev = mon[mon["Month"] == prev_m].set_index("Key")["Pcs"] if prev_m else pd.Series(dtype=float)

    def _frame(series, with_prev=True):
        out = pd.DataFrame({"Customer": [names.get(k, k) for k in series.index],
                            "Area": [areas.get(k, AREA_LABEL["Unknown"]) for k in series.index],
                            "Bun pcs": series.round(0).astype("int64").values})
        if with_prev:
            pv = prev.reindex(series.index).fillna(0)
            out["Previous month pcs"] = pv.round(0).astype("int64").values
            out["Change %"] = ((series.values - pv.values) / pv.where(pv > 0).values * 100).round(0)
        return out
    top = _frame(cur[cur > 0].sort_values(ascending=False).head(top_n))
    top.insert(0, "Rank", range(1, len(top) + 1))
    top["Share %"] = (top["Bun pcs"] / max(float(cur.sum()), 1) * 100).round(1)
    dropped_s = prev[(prev > 0) & (cur.reindex(prev.index).fillna(0) <= 0)].sort_values(ascending=False)
    dropped = pd.DataFrame({"Customer": [names.get(k, k) for k in dropped_s.index],
                            "Area": [areas.get(k, AREA_LABEL["Unknown"]) for k in dropped_s.index],
                            f"Pcs in {prev_m}": dropped_s.round(0).astype("int64").values})
    new_s = cur[(cur > 0) & (prev.reindex(cur.index).fillna(0) <= 0)].sort_values(ascending=False)
    new = pd.DataFrame({"Customer": [names.get(k, k) for k in new_s.index],
                        "Area": [areas.get(k, AREA_LABEL["Unknown"]) for k in new_s.index],
                        "Bun pcs": new_s.round(0).astype("int64").values})
    return top, dropped, new, prev_m


def _si_customer_detail(key, daily, df, codes, mon, today, snap, factor=1.5, dormant_factor=4.0):
    """Everything about ONE customer: bun types (N1..N43), sum, averages, monthly table, habit, recent orders."""
    cur_m = pd.Timestamp(today).strftime("%Y-%m")
    info = snap.get("buns", {}) or {}
    sell, bnames = info.get("sell", {}) or {}, info.get("names", {}) or {}
    d = daily[daily["Key"] == key]
    rows = df[df["Key"] == key].copy()
    out = {"daily": d, "buns": pd.DataFrame(), "orders": pd.DataFrame(), "habit": None}
    pm = pd.DataFrame()
    if len(rows):
        rows["Month"] = rows["D"].dt.strftime("%Y-%m")
        pm = rows.groupby("Month")[list(codes)].sum()
        fin = pm[pm.index < cur_m]
        recs = []
        total_all = float(rows[list(codes)].sum().sum())
        last30 = rows[rows["D"] > pd.Timestamp(today) - pd.Timedelta(days=30)]
        for c in codes:
            tot = float(rows[c].sum())
            bought = rows[rows[c] > 0]
            fc = fin[c][fin[c] > 0]
            if len(fc):
                avg_m, n_m = float(fc.mean()), len(fc)
            elif pm[c].get(cur_m, 0) > 0:
                avg_m, n_m = float(pm[c][cur_m]), 0
            else:
                avg_m, n_m = 0.0, 0
            price = float(sell.get(c) or 0)
            recs.append({"Code": c, "Bun": bnames.get(c, ""), "Price ៛": int(price), "Total pcs": int(tot),
                         "Share %": round(tot / total_all * 100, 1) if total_all else 0.0,
                         "Order days": int(bought["D"].nunique()),
                         "Avg per order": int(round(tot / bought["D"].nunique())) if len(bought) else 0,
                         "Avg per month": int(round(avg_m)), "Months (finished)": n_m,
                         "Last 30 days pcs": int(last30[c].sum()),
                         "Last bought": bought["D"].max().strftime("%Y-%m-%d") if len(bought) else "-",
                         "Sales ៛": int(tot * price)})
        out["buns"] = pd.DataFrame(recs)
        show = [c for c in codes if rows[c].sum() > 0]
        o = rows.sort_values("D", ascending=False).head(60)
        keep = ["D", "Invoice", "Remark", "Cases", "Pcs", "Sales"] + show
        o = o[[c for c in keep if c in o.columns]].copy()
        o["D"] = o["D"].dt.strftime("%Y-%m-%d")
        out["orders"] = o.rename(columns={"D": "Date", "Pcs": "Bun pcs", "Sales": "Sales ៛"})
    m = mon[mon["Key"] == key][["Month", "Pcs"]].rename(columns={"Pcs": "Bun pcs"})
    if len(d):
        dm = d.assign(Month=d["D"].dt.strftime("%Y-%m")).groupby("Month").agg(
            **{"Order days": ("D", "nunique"), "Sales ៛": ("Sales", "sum")}).reset_index()
        m = m.merge(dm, on="Month", how="left")
    else:
        m["Order days"], m["Sales ៛"] = pd.NA, pd.NA
    if len(pm):
        pmx = pm.loc[:, (pm.sum() > 0)].reset_index()
        m = m.merge(pmx, on="Month", how="left")
    m["Bun pcs"] = m["Bun pcs"].round(0).astype("int64")
    out["monthly"] = m.sort_values("Month").reset_index(drop=True)
    hb = _si_habits(d, today, 2, 3650, factor, dormant_factor) if len(d) else pd.DataFrame()
    out["habit"] = hb.iloc[0] if len(hb) else None
    out["orders_n"] = int(d["D"].nunique())
    out["first"] = d["D"].min() if len(d) else None
    out["last"] = d["D"].max() if len(d) else None
    out["sum_pcs"] = int(mon.loc[mon["Key"] == key, "Pcs"].sum())
    out["sum_sales"] = float(d["Sales"].sum()) if len(d) else 0.0
    out["pcs_per_order"] = float(d["Pcs"].mean()) if len(d) else float("nan")
    return out


# ---------- UI helpers ----------
def _si_set_seg(seg):
    st.session_state["si_seg_sel"] = seg


def _si_show(df, money=(), pct=(), height=None):
    """Table with thousands separators where the Streamlit version supports it."""
    cfg = {}
    try:
        for c in money:
            if c in df.columns:
                cfg[c] = st.column_config.NumberColumn(c, format="localized")
        for c in pct:
            if c in df.columns:
                cfg[c] = st.column_config.NumberColumn(c, format="%.1f")
    except Exception:
        cfg = {}
    try:
        show_df(df, height=height, column_config=cfg or None)
    except Exception:
        show_df(df, height=height)


# Each call is an immutable customer snapshot; the newest call supplies current details.
CALL_COLS = ["Date", "Customer", "CallID", "Outcome", "Notes", "Customer status",
             "Contact person", "Phone", "Next action", "Follow-up date", "Assigned to", "Recorded by", "Reason", "Follow-up state", "Priority", "Result",
             "Platform"]
CALL_PLATFORMS = ["📞 Phone call", "✈️ Telegram", "💬 Messenger / Facebook", "🟢 WhatsApp", "💚 WeChat", "🟩 LINE",
                  "📱 SMS", "🚶 Visit shop", "🗨️ Other"]


_PLAT_MEMO = {}


def _si_platform_map(history):
    """{customer key: (last platform used, last phone text)} — built once per loaded call history."""
    hit = _PLAT_MEMO.get("v")
    if hit is not None and hit[0] is history:
        return hit[1]
    out = {}
    if history is not None and not history.empty:
        plats = history["Platform"].astype(str) if "Platform" in history else pd.Series("", index=history.index)
        phones = history["Phone"].astype(str) if "Phone" in history else pd.Series("", index=history.index)
        for k, pl, ph in zip(history["Customer"].map(norm_name), plats, phones):
            prev = out.get(k, ("", ""))
            out[k] = (pl if pl in CALL_PLATFORMS else prev[0], ph)
    _PLAT_MEMO["v"] = (history, out)
    return out


def _si_platform_guess(history, customer, phone=""):
    """Platform to pre-select: the one used last time with this customer, else a guess from the phone / Telegram field."""
    try:
        if history is not None and not history.empty:
            used, last_phone = _si_platform_map(history).get(norm_name(customer), ("", ""))
            if used:
                return used
            if not phone:
                phone = last_phone
    except Exception:
        pass
    ph = str(phone or "").strip().lower()
    if "t.me" in ph or ph.startswith("@") or ph.startswith("tel") or "telegram" in ph or "telrgram" in ph or "telegarm" in ph:
        return "✈️ Telegram"
    if "facebook" in ph or "fb.com" in ph or "m.me" in ph or ph.startswith("page") or "messenger" in ph:
        return "💬 Messenger / Facebook"
    if "whatsapp" in ph:
        return "🟢 WhatsApp"
    if "wechat" in ph:
        return "💚 WeChat"
    return CALL_PLATFORMS[0]


def _si_platform_of(call):
    """Platform of one saved contact. Older notes have no Platform column: staff typed 'Telegram' / 'Page' in Phone."""
    p = str(call.get("Platform", "") or "")
    if p in CALL_PLATFORMS:
        return p
    ph = str(call.get("Phone", "") or "").strip()
    return _si_platform_guess(None, "", ph) if ph and ph not in ("-", "nan") else ""
CALL_OUTCOMES = ["Reached customer", "No answer", "Busy / call back", "Wrong number",
                 "Order requested", "Complaint / problem", "Not interested", "Customer update only"]
CALL_STATUSES = ["Active", "Follow-up needed", "Temporarily closed", "Stopped buying", "Do not contact"]


FOLLOWUP_REASONS = ['Not specified', 'Price', 'Product quality', 'Delivery problem', 'Still has stock',
                    'Low demand', 'Shop closed', 'Competitor', 'No answer', 'Wrong contact', 'Other']
FOLLOWUP_STATES = ['Open', 'Awaiting order', 'Resolved', 'No follow-up']
FOLLOWUP_PRIORITIES = ['Normal', 'High', 'Urgent']


def _followup_review_data(history, orders, today, names=None, sales_available=True):
    """Read-only report. Dates without time cannot prove a same-day order followed a call."""
    latest = _si_call_latest(history)
    last_orders = {}
    if orders is not None and not orders.empty and {'Date', 'Customer'} <= set(orders.columns):
        for r in orders.to_dict('records'):
            if r.get('FOC') is True:
                continue
            dt = parse_dt(r['Date'])
            if pd.notna(dt) and dt.date() <= today:
                key = norm_name(r['Customer'])
                last_orders[key] = max(last_orders.get(key, date.min), dt.date())
    def clean(v, default=''):
        return default if v is None or str(v).strip() in ('', '-', 'nan', 'None', 'NaT') else str(v).strip()
    rows=[]
    for r in latest.to_dict('records'):
        customer=clean(r.get('Customer'));key=norm_name(customer)
        due=parse_dt(r.get('Follow-up date'));called=parse_dt(r.get('Date'))
        due_day=due.date() if pd.notna(due) else None
        state=clean(r.get('Follow-up state'), 'Open' if due_day or r.get('Customer status')=='Follow-up needed' else 'No follow-up')
        status=clean(r.get('Customer status'));last=last_orders.get(key)
        next_action=clean(r.get('Next action'));owner=clean(r.get('Assigned to'))
        evidence='Sales data unavailable' if not sales_available else 'No later order found in available data'
        recovered=bool(sales_available and last and pd.notna(called) and last>called.date())
        if recovered:evidence='Order recorded on '+str(last)
        elif sales_available and last and pd.notna(called) and last==called.date():evidence='Same-day order: sequence needs review'
        if status=='Do not contact':alert='Do not contact'
        elif state=='Resolved':alert='Resolved'
        elif state=='No follow-up':alert='No follow-up'
        elif state=='Awaiting order' and recovered:alert='Order received'
        elif not due_day or not owner or not next_action:alert='Needs setup'
        elif due_day<today:alert='Overdue'
        elif due_day==today:alert='Due today'
        else:alert='Scheduled'
        rows.append({'Customer':customer,'Alert':alert,'Priority':clean(r.get('Priority'),'Normal'),
                     'Reason':clean(r.get('Reason'),'Not specified'),'Customer status':status,
                     'Last call':clean(r.get('Date')),'Last order':str(last) if last else '',
                     'Outcome':clean(r.get('Outcome')),'Notes':clean(r.get('Notes')),
                     'Next action':next_action,'Assigned to':owner,'Follow-up date':str(due_day) if due_day else '',
                     'Overdue days':max(0,(today-due_day).days) if due_day and alert=='Overdue' else 0,
                     'Follow-up state':state,'Result':clean(r.get('Result')),'Order evidence':evidence,
                     'Phone':clean(r.get('Phone')),'Recorded by':clean(r.get('Recorded by'))})
    columns=['Customer','Alert','Priority','Reason','Customer status','Last call','Last order','Outcome','Notes',
             'Next action','Assigned to','Follow-up date','Overdue days','Follow-up state','Result','Order evidence','Phone','Recorded by']
    report=pd.DataFrame(rows,columns=columns)
    if not report.empty:
        rank={'Overdue':0,'Due today':1,'Needs setup':2,'Scheduled':3,'Order received':4,'Resolved':5,'No follow-up':6,'Do not contact':7}
        report=report.assign(_rank=report['Alert'].map(rank),_priority=report['Priority'].map({'Urgent':0,'High':1,'Normal':2}).fillna(2))
        report=report.sort_values(['_rank','_priority','Follow-up date','Customer']).drop(columns=['_rank','_priority']).reset_index(drop=True)
    return report


def _followup_sales_context():
    """Use the existing journal cache; keep call management usable during a sales outage."""
    try:
        snap,source,journal_path,error=current_snapshot()
        names={norm_name(n):n for n in (snap or {}).get('customers',[])}
        if error or not snap or source=='stale':
            return names,pd.DataFrame(),False
        # Confirm order storage is readable rather than silently assuming it is empty.
        if USE_DROPBOX:
            entry = _remote_entry(os.path.basename(journal_path))
            if entry is None:
                return names,pd.DataFrame(),False
            if _sync_state()["xl_hash"].get(os.path.basename(journal_path)) != entry["hash"]:
                return names,pd.DataFrame(),False
            pull(ORDERS_FILE)
        read_raw(ORDERS_FILE, ORDER_COLS)
        orders=journal_plus_orders(snap)
        if 'FOC' in orders:orders=orders[~orders['FOC'].fillna(False).astype(bool)]
        return names,orders,True
    except Exception:
        return {},pd.DataFrame(),False


def _followup_review_panel(history):
    names,orders,available=_followup_sales_context()
    report=_followup_review_data(history,orders,today_kh(),names,available)
    st.markdown('#### Follow-up review & results')
    st.caption('Alerts are in this app; no email, Telegram or phone notifications are sent. Record reasons and actions below. Sales-based suggestions do not replace staff follow-up decisions.')
    if not available:st.warning('Sales data is unavailable. Call reports and due alerts still work; order recovery cannot be confirmed.')
    if report.empty:
        st.info('No call updates recorded yet. Choose a customer below to start.')
        return report
    counts=report['Alert'].value_counts()
    for col,label in zip(st.columns(5),['Overdue','Due today','Needs setup','Scheduled','Order received']):
        col.metric(label,int(counts.get(label,0)))
    with st.form('followup_review_filters'):
        a,b,c=st.columns(3)
        status=a.multiselect('Alert status',list(dict.fromkeys(report['Alert'])),key='fu_filter_status')
        owner=b.multiselect('Assigned staff',sorted(set(report['Assigned to'])- {''}),key='fu_filter_owner')
        reason=c.multiselect('Reason',sorted(set(report['Reason'])),key='fu_filter_reason')
        search=st.text_input('Find customer',key='fu_filter_search')
        st.form_submit_button('Apply review filters')
    view=report
    if status:view=view[view['Alert'].isin(status)]
    if owner:view=view[view['Assigned to'].isin(owner)]
    if reason:view=view[view['Reason'].isin(reason)]
    if search.strip():view=view[view['Customer'].str.contains(search.strip(),case=False,regex=False)]
    st.dataframe(view,hide_index=True,use_container_width=True)
    if view.empty:st.info('No follow-ups match these filters. Clear the filters to see all records.')
    st.caption('Order received is detected only from an order dated after the latest call. A same-day order needs manual confirmation. Receipt of an order does not prove a complaint was resolved. Save Resolved with a result after checking.')
    if has_permission('reports'):
        def _fu_frames():
            by_reason=report.groupby(['Reason','Alert'],dropna=False).size().reset_index(name='Customers')
            by_owner=report.assign(**{'Assigned to':report['Assigned to'].replace('','Unassigned')}).groupby(['Assigned to','Alert']).size().reset_index(name='Customers')
            return dict([('Current follow-ups',report),('Filtered review',view),('Reasons',by_reason),('Staff results',by_owner),('Call history',history[[c for c in CALL_COLS if c in history]])])
        _lazy_excel_download('Download follow-up review report', _fu_frames, f'Followup_Review_{today_kh()}.xlsx', 'fu_review_download')
    return report


@st.fragment(run_every=300)
def _file_sig(path):
    try:
        stt = os.stat(path)
        return (stt.st_mtime_ns, stt.st_size)
    except OSError:
        return (0, 0)


def followup_alert_banner():
    if not (has_permission('view') or has_permission('reports')):return
    try:
        history=read_raw(CALLS_FILE,CALL_COLS,max_age=120)
        if history.empty:return
        sig=(_file_sig(CALLS_FILE),_file_sig(ORDERS_FILE),str(find_excel_file() if not USE_DROPBOX else _sync_state()["xl_hash"]),
             str(today_kh()),int(time.time()//300))
        hit=st.session_state.get('_fu_banner')
        if hit and hit[0]==sig:
            due,setup,available=hit[1]
        else:
            _,orders,available=_followup_sales_context()
            report=_followup_review_data(history,orders,today_kh(),sales_available=available)
            due=int(report['Alert'].isin(['Overdue','Due today']).sum())
            setup=int(report['Alert'].eq('Needs setup').sum())
            st.session_state['_fu_banner']=(sig,(due,setup,available))
        if due or setup:
            st.warning(f'Customer follow-ups: {due} due/overdue · {setup} need a date, owner or next action. Open Customer Follow-ups to review.')
        if not available:st.caption('Follow-up alerts: order confirmation is unavailable until sales data is accessible.')
    except Exception as e:
        st.warning('Follow-up alerts could not refresh: '+str(e)[:150])


@st.fragment
def tab_followups():
    if not (has_permission('view') or has_permission('reports')):
        st.error('You do not have permission to view follow-ups.');return
    names,_,_=_followup_sales_context()
    _si_call_panel(names)


CALL_RECENT_DAYS = 7          # a customer contacted in the last N days is not put back in the urgent call list


def _si_contact_context(frame, history, daily, today):
    """Join saved contact history and latest paid orders onto customer lists."""
    result = frame.copy()
    latest = _si_call_latest(history)
    contacts = latest.set_index("_key").to_dict("index") if not latest.empty else {}
    last_orders = daily.groupby("Key")["D"].max().to_dict() if not daily.empty else {}
    def clean(value):
        return "" if pd.isna(value) else str(value).strip()
    rows = []
    for customer in result.get("Customer", pd.Series(dtype=str)):
        key = norm_name(customer)
        call = contacts.get(key, {})
        called = parse_dt(call.get("Date", ""))
        order = last_orders.get(key)
        order = pd.Timestamp(order) if order is not None and pd.notna(order) else pd.NaT
        called_today = pd.notna(called) and called.date() == today
        ordered_today = pd.notna(order) and order.date() == today
        days_ago = (today - called.date()).days if pd.notna(called) else None
        recent = days_ago is not None and 0 <= days_ago <= CALL_RECENT_DAYS
        ordered_after = pd.notna(order) and pd.notna(called) and order.normalize() > called.normalize()
        due = parse_dt(call.get("Follow-up date", ""))
        scheduled = pd.notna(due) and due.date() > today and call.get("Follow-up state") in ("Open", "Awaiting order")
        plat = _si_platform_of(call) if call else ""
        when = (f"{called:%d %b}" + (" (today)" if days_ago == 0 else f" ({days_ago} d ago)")) if pd.notna(called) else ""
        if ordered_today:
            state = "🛒 Ordered today"
        elif call and ordered_after:
            state = f"🛒 Ordered after contact on {when}"
        elif called_today:
            state = "✅ Contacted today" + (f" · {plat}" if plat else "")
        elif scheduled:
            state = f"📅 Follow-up {due:%d %b}"
        elif recent:
            state = f"✅ Contacted {when}" + (f" · {plat}" if plat else "") + " — waiting"
        elif call:
            state = f"☑️ Last contact {when}" + (f" · {plat}" if plat else "")
        else:
            state = "⏳ Not contacted"
        rows.append({"Contact status": state, "Last call": clean(call.get("Date", "")),
                     "Call outcome": clean(call.get("Outcome", "")), "Last call note": clean(call.get("Notes", "")),
                     "Next action": clean(call.get("Next action", "")), "Follow-up date": clean(call.get("Follow-up date", "")),
                     "Last order": order.strftime("%Y-%m-%d") if pd.notna(order) else "",
                     "Call now": not (ordered_today or called_today or scheduled or (recent and not ordered_after)
                                      or call.get("Customer status") in ("Do not contact", "Temporarily closed", "Stopped buying"))})
    if rows:
        for column in rows[0]: result[column] = [r[column] for r in rows]
    else:
        for column in ("Contact status", "Last call", "Call outcome", "Last call note", "Next action", "Follow-up date", "Call now"):
            result[column] = pd.Series(index=result.index, dtype=bool if column == "Call now" else str)
    return result


def _si_call_latest(history):
    if history.empty:
        return history.copy()
    latest = history.copy()
    latest["_key"] = latest["Customer"].map(norm_name)
    # File order is commit order, including multiple calls in the same second.
    return latest.drop_duplicates("_key", keep="last")


def _si_save_call(row):
    if not has_permission("edit"):
        raise PermissionError("Your account needs Create, edit, and submit changes permission.")
    if not str(row.get("Customer", "")).strip() or not str(row.get("Notes", "")).strip():
        raise ValueError("Choose a customer and enter a call note.")
    if row.get("Outcome") not in CALL_OUTCOMES or row.get("Customer status") not in CALL_STATUSES:
        raise ValueError("Choose a valid outcome and customer status.")
    if row.get("Platform", "") and row["Platform"] not in CALL_PLATFORMS:
        raise ValueError("Choose a valid platform.")
    follow = row.get("Follow-up date", "")
    if follow:
        date.fromisoformat(follow)
    state = row.get("Follow-up state", "Open" if follow else "No follow-up")
    if state not in FOLLOWUP_STATES or row.get("Reason", "Not specified") not in FOLLOWUP_REASONS or row.get("Priority", "Normal") not in FOLLOWUP_PRIORITIES:
        raise ValueError("Choose a valid reason, priority and follow-up state.")
    if row["Customer status"] == "Do not contact" and state not in ("Resolved", "No follow-up"):
        raise ValueError("Do not contact customers must have Resolved or No follow-up selected.")
    if state in ("Open", "Awaiting order"):
        if not follow or not str(row.get("Assigned to", "")).strip() or not str(row.get("Next action", "")).strip():
            raise ValueError("An open follow-up requires a date, assigned person and next action.")
        if row.get("Reason", "Not specified") == "Not specified":
            raise ValueError("Choose a reason for this follow-up.")
    if state == "Resolved" and not str(row.get("Result", "")).strip():
        raise ValueError("Enter the result before closing this follow-up.")
    row = dict(row, **{"Follow-up state": state})
    if state in ("Resolved", "No follow-up"):
        row["Follow-up date"] = ""
    clean = {c: safe_text(row.get(c, ""), maxlen=4000 if c in ("Notes", "Result") else MAX_TEXT) for c in CALL_COLS}
    # Same form token can be retried after a network error without a duplicate call.
    def add(frame):
        if clean["CallID"] in set(frame["CallID"]):
            return frame
        return pd.concat([frame, pd.DataFrame([clean])], ignore_index=True)
    modify_csv(CALLS_FILE, CALL_COLS, add)


def _si_choose_call(customer):
    st.session_state["si_call_customer"] = customer
    st.session_state["si_call_popup"] = customer          # open the form right here, not at the bottom of the page


def _si_call_popup_body(customer):
    try:
        history = read_raw(CALLS_FILE, CALL_COLS)
    except Exception as e:
        st.error(f"Call history could not be opened: {e}")
        return
    st.caption("Platform is picked automatically (last one used with this customer). Save once; the window closes.")
    _si_call_form(customer, history, "popup")


_si_call_popup = None
for _dlg_name in ("dialog", "experimental_dialog"):
    try:
        _dlg = getattr(st, _dlg_name, None)
        if _dlg is not None:
            _cand = _dlg("📝 Record call / update customer", width="large")(_si_call_popup_body)
            if callable(_cand):
                _si_call_popup = _cand
                break
    except Exception:
        continue


def _si_open_call_popup_if_asked():
    """Show the form for the customer whose button was just pressed (once per click)."""
    customer = st.session_state.pop("si_call_popup", None)
    if not customer:
        return
    if _si_call_popup is not None:
        _si_call_popup(customer)
    else:                                                   # very old Streamlit: show it at the top of the list instead
        with st.container(border=True):
            st.markdown(f"#### 📝 {customer}")
            _si_call_popup_body(customer)


@st.fragment
def _si_call_panel(names):
    st.markdown("#### 📝 Call notes & customer updates")
    st.caption("Platform is picked automatically (last one used with this customer); change it when you used another app.")
    st.caption("Select a customer, record what happened, and save once. Previous calls stay in the history. "
               "Contact details here are customer-care details; requested orders must be entered in Sales Orders.")
    try:
        if st.button("Refresh follow-up report", key="fu_refresh_now"):
            pull(CALLS_FILE, force=True)
        history = read_raw(CALLS_FILE, CALL_COLS)
    except Exception as e:
        st.error(f"Call history could not be opened: {e}")
        return
    latest = _si_call_latest(history)
    _followup_review_panel(history)
    options = sorted(set(names.values()) | set(history["Customer"]), key=str.casefold)
    if not options:
        manual = st.text_input("Customer name (sales list unavailable)", key="fu_manual_customer", max_chars=MAX_TEXT).strip()
        if not manual:
            st.info("Enter the customer name to record a follow-up without sales data.")
            return
        options = [manual]
    if st.session_state.get("si_call_customer") not in options:
        st.session_state["si_call_customer"] = options[0]
    customer = st.selectbox("Customer to call / update", options, key="si_call_customer")
    _si_call_form(customer, history, "panel")


def _si_call_form(customer, history, where="panel"):
    """The call / customer-update form and this customer's history. Used at the bottom panel and in the pop-up."""
    mine = history[history["Customer"].map(norm_name).eq(norm_name(customer))]
    prev = mine.iloc[-1].to_dict() if not mine.empty else {}
    def value(col, default=""):
        result = prev.get(col, default)
        return default if result in ("-", "", None) else str(result)
    token_key = "si_call_token_" + hashlib.sha256(norm_name(customer).encode()).hexdigest()[:20]
    if token_key not in st.session_state:
        st.session_state[token_key] = pysecrets.token_hex(16)
    token = st.session_state[token_key]
    if value("Customer status") == "Do not contact":
        st.warning("This customer is marked Do not contact. Record an internal update if needed.")
    if has_permission("edit"):
        with st.form(f"call_form_{where}_" + token, clear_on_submit=False):
            a, p_col, b = st.columns(3)
            plat_default = _si_platform_guess(history, customer)
            platform = p_col.selectbox("Platform (how you contacted)", CALL_PLATFORMS, index=CALL_PLATFORMS.index(plat_default),
                                       help="Chosen automatically from the last contact with this customer. Change it if you used another app.")
            outcome = a.selectbox("Call outcome", CALL_OUTCOMES)
            status = b.selectbox("Customer status", CALL_STATUSES,
                                 index=CALL_STATUSES.index(value("Customer status", "Active"))
                                 if value("Customer status", "Active") in CALL_STATUSES else 0)
            a, b = st.columns(2)
            contact = a.text_input("Contact person", value("Contact person"), max_chars=MAX_TEXT)
            phone = b.text_input("Phone / Telegram", value("Phone"), max_chars=MAX_TEXT)
            notes = st.text_area("Call notes (required)", max_chars=4000,
                                 placeholder="What did the customer say? Quality, price, delivery, requested products, or agreed actions…")
            a, b, c = st.columns(3)
            reason = a.selectbox("Reason", FOLLOWUP_REASONS, index=FOLLOWUP_REASONS.index(value("Reason", "Not specified")) if value("Reason", "Not specified") in FOLLOWUP_REASONS else 0)
            default_state = value("Follow-up state", "Open" if value("Follow-up date") else "No follow-up")
            follow_state = b.selectbox("Follow-up state", FOLLOWUP_STATES, index=FOLLOWUP_STATES.index(default_state) if default_state in FOLLOWUP_STATES else 0)
            priority = c.selectbox("Priority", FOLLOWUP_PRIORITIES, index=FOLLOWUP_PRIORITIES.index(value("Priority", "Normal")) if value("Priority", "Normal") in FOLLOWUP_PRIORITIES else 0)
            result = st.text_area("Result / resolution (required when Resolved)", max_chars=4000)
            st.caption("Open: action still needed. Awaiting order: watch for a later order. Resolved: close with a result. No follow-up: keep the note without reminders.")
            action = st.text_input("Next action", value("Next action"), max_chars=MAX_TEXT)
            a, b = st.columns(2)
            old_due = pd.to_datetime(value("Follow-up date"), errors="coerce")
            follow = a.date_input("Next follow-up date (required for Open / Awaiting order)",
                                 value=None if pd.isna(old_due) else old_due.date(), format="YYYY-MM-DD")
            owner = b.text_input("Assigned to", value("Assigned to", current_user() or ""), max_chars=MAX_TEXT)
            saved = st.form_submit_button("💾 Save call & customer update", type="primary")
        if saved:
            row = {"Date": now_str(), "Customer": customer, "CallID": token, "Outcome": outcome,
                   "Notes": notes, "Customer status": status, "Contact person": contact, "Phone": phone,
                   "Next action": action, "Follow-up date": follow.isoformat() if follow else "",
                   "Assigned to": owner, "Recorded by": current_user() or "-",
                   "Reason": reason, "Follow-up state": follow_state, "Priority": priority, "Result": result,
                   "Platform": platform}
            try:
                _si_save_call(row)
            except Exception as e:
                st.error(f"Could not save call: {e}")
            else:
                st.session_state.pop(token_key, None)
                st.session_state["si_call_saved"] = customer
                st.session_state["flash"] = f"✅ Call saved for {customer}"
                st.rerun()
    else:
        st.info("Read-only access. An admin can enable Create, edit, and submit changes for your account.")
    if st.session_state.pop("si_call_saved", None) == customer:
        st.success("Call saved. Customer details and follow-up updated.")
    if not mine.empty:
        st.markdown("**Latest customer details**")
        st.write(f"Status: {value('Customer status')} · Contact: {value('Contact person', '—')} · Phone: {value('Phone', '—')}")
        st.markdown(f"**Call history ({len(mine)}) — newest first**")
        display = mine[CALL_COLS].drop(columns=["CallID", "Customer"]).iloc[::-1]
        st.dataframe(display, hide_index=True, use_container_width=True)
        if has_permission("reports"):
            st.download_button("Download this customer's call history", display.to_csv(index=False).encode("utf-8-sig"),
                               file_name="customer_call_history.csv", mime="text/csv", key=f"si_call_export_{where}")
    else:
        st.caption("No calls recorded for this customer yet.")


def _followup_export_frame():
    try:
        history = read_raw(CALLS_FILE, CALL_COLS)
        names, orders, available = _followup_sales_context()
        return _followup_review_data(history, orders, today_kh(), names, available)
    except Exception as error:
        return pd.DataFrame([{"Report unavailable": str(error)[:200]}])


def _lazy_excel_download(label, frames_fn, file_name, key):
    """Build the Excel file only when someone asks for it (building it on every click made pages slow)."""
    if not st.session_state.get(f"{key}_ready"):
        if st.button(f"📄 Prepare: {label}", key=f"{key}_prep"):
            st.session_state[f"{key}_ready"] = True
            st.rerun()
        return
    try:
        st.download_button(label, _report_excel_bytes(frames_fn()), file_name=file_name, mime=XLSX_MIME, key=key,
                           on_click=lambda: st.session_state.pop(f"{key}_ready", None))
    except Exception as e:
        st.warning(f"Could not build Excel file: {e}")


XLSX_MIME = "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"


def _report_excel_bytes(frames):
    """Export reports with the same Excel dependency used to read journals."""
    from openpyxl.utils import get_column_letter
    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine="openpyxl") as writer:
        for name, frame in frames.items():
            title = name[:31]
            frame.to_excel(writer, sheet_name=title, index=False)
            sheet = writer.sheets[title]
            sheet.freeze_panes = "A2"
            sheet.auto_filter.ref = sheet.dimensions
            for column in range(1, sheet.max_column + 1):
                sheet.column_dimensions[get_column_letter(column)].width = 22
            # Reports contain data, never executable spreadsheet formulas.
            for row in sheet.iter_rows():
                for cell in row:
                    if cell.data_type == "f":
                        cell.data_type = "s"
    return buf.getvalue()


def _si_download(frames_fn, filename):
    if not has_permission("reports"):
        return
    if not st.checkbox("Prepare Excel with all lists (takes a few seconds)", key="si_prep_xl"):
        return
    try:
        frames = frames_fn()
        buf = _report_excel_bytes({name: frame.drop(columns=[c for c in ("Key",) if c in frame.columns]) for name, frame in frames.items()})
        st.download_button("📥 Download all lists (Excel)", data=buf, file_name=filename,
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", key="si_dl")
    except Exception as e:
        st.warning(f"Could not build Excel file: {e}")


def _si_bar(frame, label_col, value_col):
    data = frame[[label_col, value_col]].copy()
    for kw in ({"x": label_col, "y": value_col, "sort": f"-{value_col}", "horizontal": True},
               {"x": label_col, "y": value_col}):
        try:
            st.bar_chart(data, **kw)
            return
        except Exception:
            continue
    st.bar_chart(data.set_index(label_col))


# ---------- 🧪 DATA CHECK: double-check what the app read from the journals ----------
SI_DC_SPECS = [
    # key, icon+title, severity, why it matters, how to fix
    ("skipped", "Rows skipped: date unreadable", "fix",
     "These rows have a customer and buns/invoice but the date cell could not be read, so the app does not count them at all.",
     "Type a real date in the កាលបរិច្ឆេទ cell of that Excel row (same format as the rows above)."),
    ("dup_line", "Same invoice entered twice", "fix",
     "The same customer, day and invoice appear on 2+ lines. If it is a copy, buns and riel are counted twice.",
     "Delete the copied line, or give the second line its own invoice number (e.g. NP…​.1)."),
    ("paid_no_riel", "Paid row with 0 riel", "fix",
     "Buns are written but the riel amount is empty / 0 and the row is not FOC. Sales ៛ are too low.",
     "Fill the price (or write FOC / 5+1 in ចំណាំ if the buns were free)."),
    ("invoice_shared", "One invoice number, different customers", "review",
     "Two different customers use the same invoice number. Usually a typing mistake; follow-ups and checks by invoice get mixed up.",
     "Correct the invoice number on the wrong line."),
    ("no_cases", "Buns but no cases (កេស)", "review",
     "Packing and delivery use the case count. Empty cases make 'left to send' and case totals wrong.",
     "Type the number of cases in កេស."),
    ("odd_cases", "Cases look wrong for the buns", "review",
     "Pieces per case is far from normal (under 15 or over 80). Often a typo in កេស or a bun column.",
     "Check the case count and the bun numbers on that line."),
    ("pay_code", "Unknown payment code", "review",
     "Payment is not AR / FOC (e.g. 'F0C' with a zero, lower case, empty). The app guesses, but reports by payment can be off.",
     "Write AR or FOC in ការទូទាត់."),
    ("not_master", "Customer not in Master List", "review",
     "The name in the journal is not in the Master List (new customer or spelling). Area, map and history may not match.",
     "Add the customer to the Master List, or fix the spelling to match it."),
    ("free_rows", "Free rows (FOC / bonus) — not counted as sales", "info",
     "These buns are free, so they are left out of paid pcs, ៛ and 'order days'. Check the list is right.",
     "If a row here was really paid, remove FOC / 5+1 from the remark or payment."),
    ("no_buns", "Riel without buns (fridge, umbrella, deposit…)", "info",
     "These lines have riel but no buns. They are kept out of bun sales and habits.",
     "Nothing to do if correct. If buns are missing, fill the N columns."),
    ("future", "Future-dated rows (pre-orders)", "info",
     "Rows dated after today are pre-orders. They are not counted until their day.",
     "Nothing to do unless the date is a typo."),
]
SI_DC_SEV = {"fix": ("❗", "Needs fixing"), "review": ("⚠️", "Please review"), "info": ("ℹ️", "For your information")}


_SI_SIG_MEMO = {}


def _si_frame_sig(frame):
    """Cheap fingerprint of a DataFrame, used to cache heavy calculations until the data really changes.
    The same (shared, unchanged) table object is fingerprinted only once."""
    if frame is None or len(frame) == 0:
        return "empty"
    hit = _SI_SIG_MEMO.get(id(frame))
    if hit is not None and hit[0] is frame:
        return hit[1]
    sig = _si_frame_sig_calc(frame)
    if len(_SI_SIG_MEMO) > 32:
        _SI_SIG_MEMO.clear()
    _SI_SIG_MEMO[id(frame)] = (frame, sig)
    return sig


def _si_frame_sig_calc(frame):
    try:
        return f"{len(frame)}-{int(pd.util.hash_pandas_object(frame, index=False).sum())}"
    except Exception:
        pass
    try:
        return f"{len(frame)}-{int(pd.util.hash_pandas_object(frame.astype(str), index=False).sum())}"
    except Exception:
        return f"{len(frame)}-{frame.shape}-{hash(tuple(map(str, frame.columns)))}"


@st.cache_data(show_spinner=False, max_entries=4)
def _si_data_check(sig, today, _combined, _codes, _master, _skipped):
    """(issues {key: DataFrame}, month totals DataFrame). sig + today decide the cache."""
    j = _combined.copy() if _combined is not None else pd.DataFrame()
    issues = {k: pd.DataFrame() for k, *_ in SI_DC_SPECS}
    if _skipped is not None and len(_skipped):
        issues["skipped"] = _skipped.copy()
    if j.empty:
        return issues, pd.DataFrame()
    codes = [c for c in _codes if c in j.columns]
    j["D"] = pd.to_datetime(j["Date"], errors="coerce")
    j["Bun pcs"] = j[codes].sum(axis=1) if codes else 0.0
    j["Riel"] = pd.to_numeric(j.get("SalesActual"), errors="coerce")
    j["Cases"] = pd.to_numeric(j.get("Cases"), errors="coerce")
    for c in ("Invoice", "Remark", "Pay", "FreeReason", "Source"):
        j[c] = j[c].fillna("").astype(str) if c in j else ""
    if "_site" in j:
        j.loc[j["_site"].fillna(False).astype(bool), "Source"] = "📝 Site order"
    j["Excel row"] = pd.to_numeric(j.get("ExcelRow"), errors="coerce").astype("Int64")
    j["Free"] = j["FreeReason"].ne("") & j["FreeReason"].ne("nan")
    j["Date"] = j["D"].dt.strftime("%Y-%m-%d")
    staff = j["Customer"].astype(str).str.strip().str.upper().isin(SI_IGNORE_NAMES)
    past = j["D"] <= pd.Timestamp(today)
    real = past & ~staff
    base = ["Date", "Customer", "Invoice", "Bun pcs", "Cases", "Riel", "Remark", "Pay", "Source", "Excel row"]

    def pick(mask, cols=base):
        return j.loc[mask, cols].sort_values(["Date", "Customer"]).reset_index(drop=True)

    inv = j["Invoice"].str.strip()
    real_inv = inv.str.match(r"^" + INVOICE_PREFIX + r"\d", case=False)
    d = j[real & real_inv & (j["Bun pcs"] > 0)]
    dup = d.duplicated(["Date", "Customer", "Invoice"], keep=False)
    issues["dup_line"] = pick(j.index.isin(d.index[dup]))
    issues["paid_no_riel"] = pick(real & ~j["Free"] & (j["Bun pcs"] > 0) & j["Riel"].fillna(0).eq(0) & ~j["Source"].eq("📝 Site order"))
    n_cust = j[real & real_inv].assign(_k=j["Customer"].map(norm_name)).groupby(inv)["_k"].nunique()
    shared = set(n_cust[n_cust > 1].index)
    if shared:
        x = pick(real & inv.isin(shared))
        issues["invoice_shared"] = x.sort_values(["Invoice", "Date"]).reset_index(drop=True)
    issues["no_cases"] = pick(real & ~j["Free"] & (j["Bun pcs"] > 0) & j["Cases"].fillna(0).le(0))
    ppc = j["Bun pcs"] / j["Cases"].where(j["Cases"] > 0)
    issues["odd_cases"] = pick(real & ~j["Free"] & ((ppc < 15) | (ppc > 80))).assign(**{"Pcs per case": lambda f: (f["Bun pcs"] / f["Cases"]).round(0)})
    pay = j["Pay"].str.strip()
    # Saved history has no payment column, so only workbooks read today are checked.
    issues["pay_code"] = pick(real & ~j["Source"].eq("📝 Site order") & ~j["Source"].str.startswith("Saved history")
                              & ~pay.isin(["AR", "FOC"]))
    if _master:
        mset = {norm_name(n) for n in _master}
        nm = j[real & (j["Bun pcs"] > 0) & ~j["Customer"].map(norm_name).isin(mset)]
        if len(nm):
            issues["not_master"] = (nm.groupby("Customer").agg(**{"Lines": ("Date", "size"), "First": ("Date", "min"),
                                    "Last": ("Date", "max"), "Bun pcs": ("Bun pcs", "sum")})
                                    .reset_index().sort_values("Bun pcs", ascending=False).reset_index(drop=True))
    issues["free_rows"] = pick(past & j["Free"], base + ["FreeReason"]).rename(columns={"FreeReason": "Why free"})
    issues["no_buns"] = pick(real & (j["Bun pcs"] <= 0) & j["Riel"].fillna(0).gt(0))
    issues["future"] = pick(~past & ~staff)

    # month totals to compare with the Excel totals row
    m = j[past].copy()
    m["Month"] = m["D"].dt.strftime("%Y-%m")
    m["Paid pcs"] = m["Bun pcs"].where(~m["Free"] & ~staff[past], 0)
    m["Free pcs"] = m["Bun pcs"].where(m["Free"], 0)
    m["Bun riel"] = m["Riel"].where(m["Bun pcs"] > 0, 0).fillna(0)
    m["Other riel"] = m["Riel"].where(m["Bun pcs"] <= 0, 0).fillna(0)
    m["No riel"] = (~m["Free"] & (m["Bun pcs"] > 0) & m["Riel"].isna()).astype(int)
    totals = m.groupby("Month").agg(**{
        "Source": ("Source", lambda s: " + ".join(sorted(set(x for x in s if x)))),
        "Lines": ("Customer", "size"), "Days": ("D", "nunique"), "Paid bun pcs": ("Paid pcs", "sum"),
        "Free pcs": ("Free pcs", "sum"), "Cases": ("Cases", "sum"), "Bun ៛ (journal)": ("Bun riel", "sum"),
        "Other items ៛": ("Other riel", "sum"), "Lines without ៛": ("No riel", "sum"), "Last day": ("Date", "max")}).reset_index()
    for c in ("Paid bun pcs", "Free pcs", "Cases", "Bun ៛ (journal)", "Other items ៛"):
        totals[c] = totals[c].round(0).astype("int64")

    def _gaps(month):
        have = set(m.loc[m["Month"] == month, "D"].dt.day)
        last = int(m.loc[m["Month"] == month, "D"].dt.day.max())
        miss = [d for d in range(1, last + 1) if d not in have]
        return ", ".join(map(str, miss)) if miss else "none"
    totals.insert(3, "Days with no rows", totals["Month"].map(_gaps))
    return issues, totals


def _si_dc_counts(issues):
    out = {"fix": 0, "review": 0, "info": 0}
    for key, _t, sev, *_ in SI_DC_SPECS:
        out[sev] += len(issues.get(key, ()))
    return out


def _si_open_data_check():
    st.session_state["si_tab"] = "🧪 Data check"


def _si_health_strip(coverage, counts):
    """One easy-to-read line: which months are loaded and how many data problems there are."""
    chips = []
    for r in (coverage.to_dict("records") if coverage is not None and len(coverage) else []):
        mname = pd.Timestamp(r["Month"] + "-01").strftime("%b %Y")
        status = str(r["Data status"])
        if status.startswith("Available"):
            upto = pd.to_datetime(status.split()[-1], errors="coerce")
            upto = upto.strftime("%d %b") if pd.notna(upto) else status.split()[-1]
            icon, txt = ("🟢", "live, to " + upto) if r["Source"] == "Live journal" else ("✅", "to " + upto)
        elif status.startswith("Not started"):
            icon, txt = "⚪", "not started"
        elif status.startswith("Future"):
            icon, txt = "⚪", "pre-orders only"
        else:
            icon, txt = "🔴", "missing"
        chips.append(f"<span class='hk-pill'>{icon} <b>{_e(mname)}</b> {_e(txt)}</span>")
    fix, rev = counts["fix"], counts["review"]
    chips.append(f"<span class='hk-pill' style='background:{'#FBEAE8' if fix else '#E5F4EA'}'>❗ <b>{fix}</b> to fix</span>")
    chips.append(f"<span class='hk-pill' style='background:{'#FFF4D6' if rev else '#E5F4EA'}'>⚠️ <b>{rev}</b> to review</span>")
    return "<div class='hk-kpis'>" + "".join(chips) + "</div>"


def _si_data_check_section(issues, totals, coverage):
    st.markdown("#### 🧪 Data check — compare with your Excel")
    st.caption("1) Compare the month totals below with the totals row of each journal. 2) Fix the red items in Excel "
               "(the Excel row number is shown), save, wait for Dropbox, then press 🔄 Refresh.")
    st.markdown("**📅 Months loaded**")
    if coverage is not None and len(coverage):
        _si_show(coverage)
    for message in st.session_state.get("si_journal_warnings", []):
        st.warning(message)
    st.markdown("**🧮 Month totals (up to today)**")
    if totals.empty:
        st.info("No journal rows yet.")
    else:
        _si_show(totals, money=("Paid bun pcs", "Free pcs", "Cases", "Bun ៛ (journal)", "Other items ៛"))
        st.caption("Paid bun pcs leaves out FOC / bonus rows and STAFF/GENERAL. Bun ៛ is the riel written in the journal; "
                   "Other items ៛ are lines with riel but no buns. Lines without ៛ use the price list instead.")
    st.markdown("**🔍 Problems found** — tap a card to see the rows")
    sel = st.session_state.get("si_dc_sel")
    cards = [(k, t, sev) for k, t, sev, *_ in SI_DC_SPECS]
    for i in range(0, len(cards), 3):
        for col, (k, t, sev) in zip(st.columns(3), cards[i:i + 3]):
            n = len(issues.get(k, ()))
            icon = SI_DC_SEV[sev][0] if n else "✅"
            col.button(f"{icon} {t} · {n}", key=f"si_dc_{k}", use_container_width=True,
                       type="primary" if sel == k else "secondary", disabled=(n == 0),
                       on_click=lambda k=k: st.session_state.update(si_dc_sel=None if st.session_state.get("si_dc_sel") == k else k))
    if sel and len(issues.get(sel, ())):
        _k, title, sev, why, fix = next(x for x in SI_DC_SPECS if x[0] == sel)
        frame = issues[sel]
        st.markdown(f"##### {SI_DC_SEV[sev][0]} {title} ({len(frame)})")
        st.markdown(f"**Why it matters:** {why}  \n**How to fix:** {fix}")
        q = st.text_input("🔎 Filter these rows (customer / invoice)", key=f"si_dc_q_{sel}", max_chars=60)
        if q.strip():
            hay = frame.astype(str).agg(" ".join, axis=1)
            frame = frame[hay.str.contains(q.strip(), case=False, regex=False)]
        _si_show(frame, money=("Bun pcs", "Riel"), height=min(520, 60 + 36 * max(len(frame), 1)))
    if has_permission("reports"):
        try:
            frames = {"Month totals": totals, "Months loaded": coverage if coverage is not None else pd.DataFrame()}
            for k, t, sev, *_ in SI_DC_SPECS:
                if len(issues.get(k, ())):
                    frames[t[:31]] = issues[k]
            _lazy_excel_download("📥 Download data check (Excel)", lambda: frames, f"Data_Check_{today_kh()}.xlsx", "si_dc_dl")
        except Exception as e:
            st.warning(f"Could not build the Excel file: {e}")


@st.cache_data(show_spinner=False, max_entries=6)
def _si_derived(sig, today, lookback, min_orders, factor, dormant_factor, _daily, _mon, _names, _areas):
    """The slow per-customer calculations, cached until the data or the settings change."""
    habits = _si_habits(_daily, today, min_orders, lookback, factor, dormant_factor, _names, _areas)
    avgs = _si_month_avgs(_mon, _daily, today)
    no_month = _si_no_order(_daily, _names, _areas, today.replace(day=1), today, today, avgs)
    return habits, avgs, no_month


@st.cache_data(show_spinner=False, max_entries=6)
def _si_care_cached(sig, today, measure, _daily, _df, _codes, _habits, _names, _areas, _avgs):
    return _si_care(_daily, _df, _codes, _habits, _names, _areas, today, today.replace(day=1), _avgs, measure)


# ---------- 🗺️ map of active customers (always the newest journal + shop pins) ----------
AMAP_COLORS = {"top": [212, 160, 23], "active": [46, 125, 79], "quiet": [150, 150, 150]}


def _si_active_table(daily, names, areas, days, top_n, today):
    """One row per customer that ordered in the last `days` days: pcs, ៛, order days, last order, rank."""
    start = pd.Timestamp(today) - pd.Timedelta(days=days - 1)
    d = daily[(daily["D"] >= start) & (daily["D"] <= pd.Timestamp(today))]
    if d.empty:
        return pd.DataFrame()
    g = d.groupby("Key").agg(Pcs=("Pcs", "sum"), Sales=("Sales", "sum"), Orders=("D", "nunique"), Last=("D", "max"))
    g = g[g["Pcs"] > 0].sort_values("Sales", ascending=False)
    g["Rank"] = range(1, len(g) + 1)
    g["Group"] = ["top" if r <= top_n else "active" for r in g["Rank"]]
    g["Customer"] = [names.get(k, k) for k in g.index]
    g["Area"] = [areas.get(k, "") for k in g.index]
    g["Days since"] = (pd.Timestamp(today) - g["Last"]).dt.days
    return g.reset_index()


def _si_active_map_section(daily, names, areas, today):
    st.markdown("#### 🗺️ ផែនទីអតិថិជនសកម្ម")
    st.caption("បង្ហាញអតិថិជនដែលបានបញ្ជាទិញក្នុងរយៈពេលដែលជ្រើស តាម Sale Journal ចុងក្រោយបំផុត។ "
               "🟡 = Top sale · 🟢 = Active · ទំហំចំណុច = ចំនួននំ។ ចុច 🔄 Refresh ដើម្បីយកទិន្នន័យថ្មី។")
    c1, c2, c3 = st.columns(3)
    days = c1.radio("រយៈពេល", [30, 60, 90], index=1, horizontal=True, key="amap_days", format_func=lambda v: f"{v} ថ្ងៃ")
    top_n = c2.select_slider("Top sale", [10, 20, 30, 50], value=20, key="amap_top")
    where = c3.radio("តំបន់", ["ទាំងអស់", "ភ្នំពេញ", "ខេត្ត"], horizontal=True, key="amap_area")
    t = _si_active_table(daily, names, areas, days, top_n, today)
    if t.empty:
        st.info("មិនទាន់មានការបញ្ជាទិញក្នុងរយៈពេលនេះទេ។")
        return
    registry, store = _visit_registry(), _visit_pin_store()
    try:
        auto = _visit_candidates_for({k: names.get(k, k) for k in t["Key"]}, registry)[1]
    except Exception:
        auto = {}
    pins = [_visit_pin(n, registry, store, auto) for n in t["Customer"]]
    t["Lat"] = [p[0] if p else None for p in pins]
    t["Lon"] = [p[1] if p else None for p in pins]
    if where != "ទាំងអស់":
        want = AREA_LABEL[PP] if where == "ភ្នំពេញ" else AREA_LABEL["Province"]
        t = t[t["Area"].eq(want)]
    only_top = st.toggle("🟡 បង្ហាញតែ Top sale", key="amap_only_top")
    show = t[t["Group"].eq("top")] if only_top else t
    with_pin = show.dropna(subset=["Lat", "Lon"])
    k1, k2, k3, k4 = st.columns(4)
    k1.metric("អតិថិជនសកម្ម", f"{len(t):,}", f"{days} ថ្ងៃចុងក្រោយ", delta_color="off")
    k2.metric("🟡 Top sale", f"{int(t['Group'].eq('top').sum())}", f"{t.loc[t['Group'].eq('top'), 'Sales'].sum() / max(1, t['Sales'].sum()) * 100:.0f}% នៃការលក់", delta_color="off")
    k3.metric("មានទីតាំងលើផែនទី", f"{len(t.dropna(subset=['Lat'])):,} / {len(t):,}")
    k4.metric("នំសរុប (pcs)", f"{int(t['Pcs'].sum()):,}")
    if with_pin.empty:
        st.warning("អតិថិជនទាំងនេះមិនទាន់មានទីតាំងលើផែនទីទេ។")
    else:
        m = with_pin.copy()
        m["color"] = m["Group"].map(AMAP_COLORS)
        mx = max(1.0, float(m["Pcs"].max()))
        m["radius"] = (60 + 340 * (m["Pcs"] / mx) ** 0.5).round(0)
        m["label"] = [f"{'🟡 #' + str(r) + ' ' if g == 'top' else ''}{c}" for r, g, c in zip(m["Rank"], m["Group"], m["Customer"])]
        m["info"] = [f"{int(p):,} pcs · ៛{int(s):,} · {o} ដង · ចុងក្រោយ {l:%d %b}"
                     for p, s, o, l in zip(m["Pcs"], m["Sales"], m["Orders"], m["Last"])]
        m["nav"] = [f"https://www.google.com/maps/dir/?api=1&destination={a},{b}" for a, b in zip(m["Lat"], m["Lon"])]
        try:
            import pydeck as pdk
            data = m[["Lat", "Lon", "color", "radius", "label", "info"]].to_dict("records")
            layer = pdk.Layer("ScatterplotLayer", data=data, get_position="[Lon, Lat]", get_radius="radius",
                              radius_min_pixels=4, radius_max_pixels=22, get_fill_color="color", get_line_color=[255, 255, 255],
                              stroked=True, line_width_min_pixels=1, pickable=True, opacity=0.85)
            top_layer = pdk.Layer("TextLayer", data=[x for x in data if x["label"].startswith("🟡")] if len(m) > 40 else data,
                                  get_position="[Lon, Lat]", get_text="label", get_size=11, get_color=[30, 35, 40],
                                  get_pixel_offset=[0, -16], character_set="auto")
            pp = m[(m["Lat"].between(11.4, 11.75)) & (m["Lon"].between(104.7, 105.05))]
            base = pp if (where != "ខេត្ត" and len(pp) >= len(m) * 0.5) else m
            view = pdk.ViewState(latitude=float(base["Lat"].median()), longitude=float(base["Lon"].median()),
                                 zoom=11 if base is pp else 6.5, pitch=0)
            deck = pdk.Deck(layers=[layer], map_provider="carto", map_style="light", initial_view_state=view,
                            tooltip={"text": "{label}\n{info}"})
            try:
                st.pydeck_chart(deck, use_container_width=True, height=560)
            except TypeError:
                st.pydeck_chart(deck)
        except Exception:
            st.map(m.rename(columns={"Lat": "lat", "Lon": "lon"}), latitude="lat", longitude="lon", color="color", size="radius")
        st.caption("🟡 Top sale  ·  🟢 Active  ·  ចុចលើចំណុចដើម្បីមើលព័ត៌មាន")
    tbl = show.assign(**{"ក្រុម": show["Group"].map({"top": "🟡 Top sale", "active": "🟢 Active"}),
                         "ចុងក្រោយ": show["Last"].dt.strftime("%d %b"),
                         "ទីតាំង": show["Lat"].notna().map({True: "📍", False: "❌ គ្មាន"}),
                         "ផ្លូវ": [f"https://www.google.com/maps/dir/?api=1&destination={a},{b}" if pd.notna(a) else ""
                                   for a, b in zip(show["Lat"], show["Lon"])]})
    tbl = tbl[["Rank", "ក្រុម", "Customer", "Area", "Pcs", "Sales", "Orders", "ចុងក្រោយ", "Days since", "ទីតាំង", "ផ្លូវ"]].rename(
        columns={"Rank": "លេខ", "Customer": "អតិថិជន", "Area": "តំបន់", "Pcs": "នំ (pcs)", "Sales": "លក់ ៛", "Orders": "ចំនួនដង",
                 "Days since": "ថ្ងៃមុន"})
    try:
        st.dataframe(tbl, hide_index=True, use_container_width=True, height=min(520, 60 + 35 * len(tbl)),
                     column_config={"លក់ ៛": st.column_config.NumberColumn(format="localized"),
                                    "នំ (pcs)": st.column_config.NumberColumn(format="localized"),
                                    "ផ្លូវ": st.column_config.LinkColumn("ផ្លូវ", display_text="🧭")})
    except Exception:
        st.dataframe(tbl, hide_index=True, use_container_width=True)
    nopin = show[show["Lat"].isna()]
    if len(nopin):
        st.caption(f"❌ {len(nopin)} អតិថិជនសកម្មមិនទាន់មានទីតាំង (top sale: {int(nopin['Group'].eq('top').sum())})។ "
                   "ដាក់ Label ក្នុង Google Maps ឬ Check-in នៅហាង ដើម្បីបន្ថែម។")


def _sales_insights_body():
    h1, h2 = st.columns([5, 1])
    h1.markdown("### 🎯 Sales Insights")
    if h2.button("🔄 Refresh", key="si_refresh_latest", use_container_width=True,
                 help="Read the newest journal and orders from Dropbox"):
        try:
            if USE_DROPBOX:
                _remote_listing_forget()
                pull(ORDERS_FILE, force=True)
                pull(CALLS_FILE, force=True)
            get_snapshot.clear()
        except Exception as error:
            st.warning("Latest data could not be refreshed: " + str(error)[:160])
    snap, _src, _path, err = current_snapshot()
    if not snap:
        st.warning(f"Excel problem: {err}")
        _si_call_panel({})
        return
    today = today_kh()
    if _src == "stale":
        st.warning("The journal could not be read. These figures use the last readable copy; today's orders may be missing.")
    with st.spinner("Reading journals…"):
        daily, df, codes = _si_prepare(snap)
    combined = st.session_state.get("si_combined", pd.DataFrame())
    coverage = st.session_state.get("si_journal_coverage", pd.DataFrame())
    skipped = st.session_state.get("si_skipped", pd.DataFrame())
    master = tuple(snap.get("customers", []))
    issues, totals = _si_data_check(f"{_si_frame_sig(combined)}|{_si_frame_sig(skipped)}|{len(master)}", today,
                                    combined, codes, master, skipped)
    counts = _si_dc_counts(issues)
    st.caption(f"Updated {now_kh():%d %b %Y, %I:%M %p} · Journal: {os.path.basename(_path or '')} · "
               "Save Excel and let Dropbox finish syncing before you refresh.")
    s1, s2 = st.columns([5, 1])
    s1.markdown(_si_health_strip(coverage, counts), unsafe_allow_html=True)
    s2.button("🧪 Data check", key="si_open_dc", on_click=_si_open_data_check, use_container_width=True,
              type="primary" if counts["fix"] else "secondary")
    if daily.empty:
        st.info("No paid orders found in the journal yet. Customer follow-ups remain available below.")
        _si_data_check_section(issues, totals, coverage)
        _si_call_panel({norm_name(n): n for n in snap.get("customers", [])})
        return
    names, areas = _si_names_areas(snap, daily)
    hist_monthly = _si_read_hist(SI_HIST_MONTHLY_FILE)
    mon = _si_monthly_table(hist_monthly, daily)
    if not hist_monthly.empty and "Zone" in hist_monthly.columns:
        for k, c, z in zip(hist_monthly["Customer"].map(norm_name), hist_monthly["Customer"], hist_monthly["Zone"]):
            names.setdefault(k, c)
            if areas.get(k, AREA_LABEL["Unknown"]) == AREA_LABEL["Unknown"]:
                areas[k] = AREA_LABEL[PP] if str(z).strip() == "ភ្នំពេញ" else AREA_LABEL["Province"]
    span = (daily["D"].max() - daily["D"].min()).days + 1

    with st.expander("⚙️ Settings for 'missing from habit'"):
        c1, c2, c3, c4 = st.columns(4)
        lookback = c1.slider("Look back (days)", 30, 365, min(180, max(30, span)), 15, key="si_lookback")
        min_orders = c2.slider("Min. order days to learn a habit", 2, 10, 4 if span >= 60 else 3, key="si_minord")
        factor = c3.slider("Late when silent × usual gap", 1.2, 3.0, 1.5, 0.1, key="si_factor")
        dormant_factor = c4.slider("Dormant after × usual gap", 2.0, 8.0, 4.0, 0.5, key="si_dormant")
        if span < 60:
            st.info("The journal covers less than 60 days, so habits are still rough. They get better as more days are added.")

    sig = _si_frame_sig(daily) + "|" + _si_frame_sig(mon)
    habits, avgs, no_month = _si_derived(sig, today, lookback, min_orders, factor, dormant_factor, daily, mon, names, areas)
    this_start = today.replace(day=1)
    d_mtd = daily[(daily["D"] >= pd.Timestamp(this_start)) & (daily["D"] <= pd.Timestamp(today))]
    last_end = this_start - timedelta(days=1)
    last_start = last_end.replace(day=1)
    same_end = min(last_start + timedelta(days=today.day - 1), last_end)
    d_prev = daily[(daily["D"] >= pd.Timestamp(last_start)) & (daily["D"] <= pd.Timestamp(same_end))]
    try:
        no_month, _dups_m, _n_same_m = _si_no_order_split(no_month, daily, names, today.replace(day=1), today)
    except Exception:
        pass
    lost_month = no_month[no_month["Group"] == "Ordered last month"] if not no_month.empty else no_month
    missing = habits[habits["Status"] == "Missing"] if not habits.empty else habits

    def _delta(now, prev):
        return f"{(now - prev) / prev * 100:+.0f}% vs same days last month" if prev > 0 else None

    s_now, s_prev = d_mtd["Sales"].sum(), d_prev["Sales"].sum()
    p_now, p_prev = d_mtd["Pcs"].sum(), d_prev["Pcs"].sum()
    st.markdown(f"**This month so far** · {this_start:%d %b} → {today:%d %b}")
    k1, k2, k3 = st.columns(3)
    k1.metric("Customers who ordered", f"{d_mtd['Key'].nunique():,}", _delta(d_mtd["Key"].nunique(), d_prev["Key"].nunique()))
    k2.metric("Paid bun pcs", f"{p_now:,.0f}", _delta(p_now, p_prev))
    k3.metric("Bun sales ៛", f"{s_now:,.0f}", _delta(s_now, s_prev))
    st.markdown("**Customers to watch**")
    k4, k5, k6 = st.columns(3)
    k4.metric("Late vs their habit", f"{len(missing):,}")
    k5.metric("Bought last month, not yet now", f"{len(lost_month):,}")
    k6.metric("Sales at risk ៛ (est.)", f"{int(missing['Lost sales ៛ (est.)'].sum()) if len(missing) else 0:,}")

    care_measure = "Sales" if str(st.session_state.get("si_care_measure", "")).startswith("💵") else "Pcs"
    care = _si_care_cached(sig + "|" + _si_frame_sig(habits), today, care_measure, daily, df, codes, habits, names, areas, avgs)
    care_unit = "pcs" if care_measure == "Pcs" else "៛"
    top = pd.DataFrame()
    # A sales risk can still appear in analytical reports, but not as a call recommendation.
    try:
        call_history = read_raw(CALLS_FILE, CALL_COLS)
        call_latest = _si_call_latest(call_history)
        excluded = set(call_latest.loc[call_latest["Customer status"].eq("Do not contact"), "Customer"].map(norm_name)) if not call_latest.empty else set()
        if not care.empty:
            care = care[~care["Customer"].map(norm_name).isin(excluded)]
        care = _si_contact_context(care, call_history, daily, today)
        missing = _si_contact_context(missing, call_history, daily, today)
    except Exception as call_error:
        st.warning("Call recommendations hidden because contact preferences could not be checked: " + str(call_error)[:120])
        care = care.iloc[0:0]

    _si_tabs = ["🗺️ ផែនទីអតិថិជន", "🏆 Top 20", "⏰ Missing from habit", "📭 No order this month",
                "💝 Customer care", "📆 Monthly history", "🔎 Customer detail", "🧪 Data check"]
    if st.session_state.get("si_tab") not in _si_tabs:
        st.session_state["si_tab"] = _si_tabs[0]
    _si_tab = st.radio("Insights section", _si_tabs, horizontal=True, key="si_tab", label_visibility="collapsed")
    t_top, t_miss, t_none, t_care, t_hist, t_det, t_dc = (_si_tab == name for name in _si_tabs[1:])   # only the chosen one is built
    if _si_tab == "🗺️ ផែនទីអតិថិជន":
        _si_active_map_section(daily, names, areas, today)
        return
    if t_dc:
        _si_data_check_section(issues, totals, coverage)

    if t_top:
        c1, c2 = st.columns([2, 2])
        period = c1.selectbox("Period", SI_PERIODS, key="si_period")
        metric_label = c2.radio("Rank by", list(SI_METRICS), horizontal=True, key="si_metric")
        metric = SI_METRICS[metric_label]
        if metric == "Sales" and not daily["Sales"].sum():
            st.info("No sell prices found in the journal header; ranking by Cases instead.")
            metric, metric_label = "Cases", "Cases"
        start, end = _si_period(period, today)
        top, total = _si_top(daily, start, end, metric, names, areas, 20, df, codes)
        if top.empty:
            st.info(f"No orders in this period ({start} → {end}).")
        else:
            st.caption(f"{start} → {end} · Top 20 hold {top['Share %'].sum():.0f}% of all {metric_label} in this period.")
            _si_bar(top, "Customer", metric_label if metric_label in top.columns else "Sales ៛")
            _si_show(top, money=("Sales ៛", "Avg order ៛", "Bun pcs"), pct=("Share %",), height=760)
            part = df[(df["D"] >= pd.Timestamp(start)) & (df["D"] <= pd.Timestamp(end))]
            if len(part) and codes:
                info = snap.get("buns", {}) or {}
                sell = info.get("sell", {}) or {}
                types = pd.DataFrame([{"Code": c, "Bun": (info.get("names", {}) or {}).get(c, ""),
                                       "Pieces": int(part[c].sum()), "Sales ៛": int(part[c].sum() * float(sell.get(c) or 0)),
                                       "Customers": int((part.groupby("Key")[c].sum() > 0).sum())} for c in codes])
                types = types[types["Pieces"] > 0].sort_values("Pieces", ascending=False)
                with st.expander("🥟 Pieces by bun type (all customers, this period)"):
                    _si_show(types, money=("Pieces", "Sales ៛"))

    if t_miss:
        st.markdown("Customers who normally order every X days but are **later than usual**. "
                    "Call the 🟢 Regular ones first — their habit is the most reliable.")
        only_regular = st.checkbox("Only regular buyers 🟢", value=False, key="si_regular")
        view = missing if not only_regular else missing[missing["Pattern"].str.contains("Regular")]
        if view.empty:
            st.success("Nobody is late compared with their usual habit. 🎉")
        else:
            view = view.sort_values(["Lost sales ៛ (est.)", "Days late"], ascending=False)
            _si_show(view.drop(columns=["Key", "Status"]), money=("Usual pcs", "Avg order ៛", "Lost pcs (est.)", "Lost sales ៛ (est.)"))
        dorm = habits[habits["Status"] == "Dormant"] if not habits.empty else habits
        if len(dorm):
            with st.expander(f"💤 Dormant ({len(dorm)}): silent far longer than their habit"):
                _si_show(dorm.sort_values("Avg order ៛", ascending=False).drop(columns=["Key", "Status"]),
                         money=("Usual pcs", "Avg order ៛", "Lost pcs (est.)", "Lost sales ៛ (est.)"))

    if t_none:
        mode = st.radio("Month", ["This month", "Last month"], horizontal=True, key="si_month")
        if mode == "This month":
            m_start, m_end = this_start, today
        else:
            m_start, m_end = last_start, last_end
        table = _si_no_order(daily, names, areas, m_start, m_end, today, avgs)
        try:
            table, dup_review, n_same = _si_no_order_split(table, daily, names, m_start, m_end)
        except Exception as dup_error:
            dup_review, n_same = pd.DataFrame(), 0
            st.caption("Duplicate-name check skipped: " + str(dup_error)[:120])
        try:
            hist_calls = read_raw(CALLS_FILE, CALL_COLS)
        except Exception:
            hist_calls = pd.DataFrame(columns=CALL_COLS)
        _si_dup_review(dup_review, all_names=list(names.values()))
        if table.empty:
            st.success("Every customer ordered in this month. 🎉")
        else:
            counts = table["Group"].value_counts()
            st.caption(f"{m_start} → {m_end} · {len(table)} customers without an order "
                       f"({counts.get('Ordered last month', 0)} ordered the month before, "
                       f"{counts.get('Ordered earlier', 0)} earlier, {counts.get('Never ordered', 0)} never)."
                       + (f" {n_same} hidden: they ordered under another spelling of the same name." if n_same else ""))
            if mode == "This month" and today.day <= 5:
                st.info("It is the start of the month, so many customers have not ordered yet. Check 'Missing from habit' for who is really late.")
            g1 = table[table["Group"] == "Ordered last month"]
            g2 = table[table["Group"] == "Ordered earlier"]
            g3 = table[table["Group"] == "Never ordered"]
            st.markdown(f"**📞 Ordered the month before but not this month ({len(g1)})**")
            st.caption("Tick ✅ when you have contacted the customer, check the Platform (picked automatically), then press 💾 Save.")
            _si_no_order_contact_table(g1.drop(columns="Group"), hist_calls, m_start, "si_no1", height=460)
            with st.expander(f"Ordered earlier, silent for more than a month ({len(g2)})"):
                _si_no_order_contact_table(g2.drop(columns="Group"), hist_calls, m_start, "si_no2")
            with st.expander(f"In the Master List but never ordered in the journal ({len(g3)})"):
                _si_no_order_contact_table(g3.drop(columns="Group"), hist_calls, m_start, "si_no3")

    if t_care:
        if care.empty:
            st.info("No customer-care actions found right now.")
        else:
            segs = list(care.drop_duplicates("Segment").sort_values("Priority")["Segment"])
            cnt = care["Segment"].value_counts()
            sel = st.session_state.get("si_seg_sel")
            if sel not in segs:
                sel = None
            st.radio("Measure customers by", ["🥟 Bun pcs", "💵 Sales ៛"], horizontal=True, key="si_care_measure")
            st.caption("👆 Click a card to filter the lists below. Click it again (or 📋 All) to clear.")
            cards = [(None, f"📋 All · {len(care)}")] + [(sg, f"{sg} · {cnt[sg]}") for sg in segs]
            for i in range(0, len(cards), 4):
                for col, (sg, lab) in zip(st.columns(4), cards[i:i + 4]):
                    col.button(lab, key=f"si_segbtn_{sg or 'all'}", type="primary" if sel == sg else "secondary",
                               use_container_width=True, on_click=_si_set_seg, args=(None if sel == sg else sg,))
            f1, f2 = st.columns([2, 3])
            area_pick = f1.multiselect("Area", sorted(care["Area"].unique()), key="si_care_area")
            q = f2.text_input("Search customer name", key="si_care_q")
            view = care.copy()
            if sel:
                view = view[view["Segment"] == sel]
            if area_pick:
                view = view[view["Area"].isin(area_pick)]
            if q.strip():
                view = view[view["Customer"].str.contains(q.strip(), case=False, regex=False)]
            _si_open_call_popup_if_asked()
            st.markdown("#### 📞 Call list (urgent first)")
            urgent = view[(view["Priority"] <= 2) & view["Call now"].eq(True)].head(10)
            st.caption("Calls recorded today, customers who ordered today, and future scheduled follow-ups stay in the table below but are excluded from this urgent sales-call queue. Due follow-ups remain in the follow-up review.")
            if urgent.empty:
                st.success("Nobody urgent in this selection.")
            else:
                for r in urgent.to_dict("records"):
                    st.markdown(f"**{r['Segment']} — {r['Customer']}** ({r['Area']})  \n"
                                f"{r['Why']}  \n👉 {r['Suggested action']}"
                                + (f"  \n💡 {r['Cross-sell idea']}" if r["Cross-sell idea"] else ""))
                    st.caption(f"{r['Contact status']} · Last order: {r['Last order']}")
                    if r['Last call']:
                        st.write(f"Last call: {r['Last call']} · {r['Call outcome']}")
                        st.write("Note: " + r['Last call note'])
                        st.write("Next action: " + (r['Next action'] or 'None recorded') + " · Follow-up: " + (r['Follow-up date'] or 'None'))
                    st.button("📝 Record call / update customer", key="si_open_call_" + hashlib.sha256(r["Customer"].encode()).hexdigest()[:20],
                              on_click=_si_choose_call, args=(r["Customer"],))
            st.markdown(f"#### Customer-care suggestions ({len(view)} of {len(care)})")
            _si_show(view.drop(columns=["Priority", "Call now"], errors="ignore"), money=(f"Avg {care_unit}/month", f"Last 30d {care_unit}", f"Prev 30d {care_unit}"), height=520)
            with st.expander("How these suggestions are made"):
                st.markdown(
                    "- 🔴 **VIP at risk**: top 20% (by the measure you picked, bun pieces or riel) over the last 90 days and late / silent.\n"
                    "- 🟠 **Missed usual order**: later than their own usual gap. 🟠 **Ordering less**: last 30 days at least 40% below the 30 days before.\n"
                    "- 🟡 **Win-back**: dormant, or silent 45–180 days.\n"
                    "- 🟢 **New customer**: first order in the last 30 days. 🟢 **Growing**: last 30 days at least 40% above the 30 days before.\n"
                    "- ⭐ **VIP – keep happy**: top 20% and ordering normally.\n"
                    "- 🥟 / 💵 **Measure**: choose bun pieces (default) or riel above the cards. Riel only exists for months with daily data (September onward).\n"
                    "- 📊 **Averages** are per month the customer actually bought (finished months only; months without a purchase are not counted). "
                    "The 'Avg based on' column says how many months. A customer with no finished month yet shows this month so far, based on order days.\n"
                    "- 💡 **Cross-sell**: top-3 best-selling bun types of the last 90 days that this customer did not buy.")
        _si_call_panel(names)
    if t_hist:
        summ = _si_month_summary(mon)
        if summ.empty:
            st.info("No monthly data yet.")
        else:
            st.caption("Bun pieces per month. Older months come from sales_history_monthly.csv; months with daily data use the daily rows. "
                       f"The newest month ({summ['Month'].iloc[-1]}) may still be running." +
                       ("" if not hist_monthly.empty else "  ⚠️ sales_history_monthly.csv was not found in the data folder."))
            st.bar_chart(summ.set_index("Month")["Bun pcs"])
            _si_show(summ, money=("Bun pcs",))
            month = st.selectbox("Month detail", list(summ["Month"])[::-1], key="si_hist_month")
            h_top, h_drop, h_new, prev_m = _si_month_detail(mon, month, names, areas)
            st.markdown(f"**🏆 Top 20 in {month}** (bun pcs)" + (f" — compared with {prev_m}" if prev_m else ""))
            _si_show(h_top, money=("Bun pcs", "Previous month pcs"), pct=("Share %",), height=760)
            if prev_m:
                with st.expander(f"📉 Ordered in {prev_m} but not in {month} ({len(h_drop)})"):
                    _si_show(h_drop, money=(f"Pcs in {prev_m}",), height=420)
                with st.expander(f"🆕 New or resumed in {month} ({len(h_new)})"):
                    _si_show(h_new, money=("Bun pcs",), height=420)
            tot = mon.groupby("Key")["Pcs"].sum().sort_values(ascending=False)
            pick = st.selectbox("Customer trend", list(tot.index), format_func=lambda k: names.get(k, k), key="si_hist_cust")
            series = mon[mon["Key"] == pick].set_index("Month")["Pcs"].reindex(summ["Month"]).fillna(0)
            st.line_chart(series.rename("Bun pcs"))
    if t_det:
        q = st.text_input("🔎 Search customer name (any part, Khmer or English)", key="si_det_q")
        order_keys = list(mon.groupby("Key")["Pcs"].sum().sort_values(ascending=False).index)
        keys = order_keys + [k for k in names if k not in set(order_keys)]
        if q.strip():
            ql = q.strip().casefold()
            keys = [k for k in keys if ql in names.get(k, k).casefold()]
        if not keys:
            st.info("No customer matches this search.")
        else:
            pick = st.selectbox(f"Customer ({len(keys)} found, biggest first)", keys, format_func=lambda k: names.get(k, k), key="si_det_pick")
            det = _si_customer_detail(pick, daily, df, codes, mon, today, snap, factor, dormant_factor)
            a_p, a_s, a_b = _si_avg_get(avgs, pick)
            st.markdown(f"### {names.get(pick, pick)}  \n{areas.get(pick, AREA_LABEL['Unknown'])}")
            c1, c2, c3, c4 = st.columns(4)
            kpi(c1, "Sum bun pcs (all months)", f"{det['sum_pcs']:,}")
            kpi(c2, "Avg pcs / month", f"{a_p:,.0f}" if pd.notna(a_p) else "-")
            kpi(c3, "Avg ៛ / month", f"{a_s:,.0f}" if pd.notna(a_s) else "-")
            kpi(c4, "Avg based on", a_b)
            c5, c6, c7, c8 = st.columns(4)
            kpi(c5, "Order days (daily data)", f"{det['orders_n']:,}")
            kpi(c6, "Avg pcs / order", f"{det['pcs_per_order']:,.0f}" if pd.notna(det["pcs_per_order"]) else "-")
            kpi(c7, "Sum ៛ (months with ៛)", f"{det['sum_sales']:,.0f}")
            kpi(c8, "Last order", f"{det['last']:%Y-%m-%d} ({(pd.Timestamp(today) - det['last']).days} d ago)" if det["last"] is not None else "-")

            st.markdown("#### ⏰ Habit")
            hb = det["habit"]
            if hb is None:
                st.info("Not enough orders yet to see a habit (needs at least 2 order days).")
            else:
                icon = {"On track": "✅ On track", "Missing": "⏰ Late — missing usual order", "Dormant": "💤 Dormant"}[hb["Status"]]
                st.markdown(f"**{icon}** · {hb['Pattern']} · orders every ~{hb['Usual gap (days)']:g} days"
                            + (f", usually on **{hb['Usual day']}**" if hb["Usual day"] != "-" else "")
                            + f" · usual order ≈ {hb['Usual cases']:g} cases / {hb['Usual pcs']:,} pcs · last order {hb['Last order']} ({hb['Days since']} days ago)"
                            + f" · next expected by {hb['Expected by']}"
                            + (f" · **{hb['Days late']} days late**" if hb["Status"] != "On track" else ""))
            mine = care[care["Customer"] == names.get(pick, pick)] if not care.empty else care
            if len(mine):
                r = mine.iloc[0]
                st.markdown(f"**💝 {r['Segment']}** — {r['Why']}  \n👉 {r['Suggested action']}"
                            + (f"  \n💡 {r['Cross-sell idea']}" if r["Cross-sell idea"] else ""))

            st.markdown("#### 🥟 Buns by type (N1–N43)")
            if det["buns"].empty:
                st.info("No bun-type detail for this customer yet: older months only have the monthly total. "
                        "Bun types are available from the daily data (September onward and the live journal).")
            else:
                st.caption("Total, share and averages come from the daily data. 'Avg per month' = months the customer bought that bun (finished months).")
                _si_show(det["buns"], money=("Price ៛", "Total pcs", "Sales ៛", "Avg per order", "Avg per month", "Last 30 days pcs"), pct=("Share %",), height=520)
            st.markdown("#### 📆 Month by month")
            if len(det["monthly"]):
                st.bar_chart(det["monthly"].set_index("Month")["Bun pcs"])
                _si_show(det["monthly"], money=("Bun pcs", "Sales ៛"))
            if len(det["orders"]):
                with st.expander(f"🧾 Recent orders ({len(det['orders'])})"):
                    _si_show(det["orders"], money=("Sales ៛",), height=420)
    _si_download(lambda: {"Monthly history": _si_month_summary(mon), "Top 20": (top if not top.empty else _si_top(daily, *_si_period("This month", today), "Sales", names, areas, 20, df, codes)[0]), "Missing from habit": missing,
                  "No order this month": no_month, "Customer care": care, "Follow-ups": _followup_export_frame(), "Journal sources": st.session_state.get("si_journal_coverage", pd.DataFrame())}, f"Sales_Insights_{today}.xlsx")


@st.fragment
def tab_sales_insights():
    safe_render(_sales_insights_body, "Sales insights")


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
st.markdown(POSTER_CSS, unsafe_allow_html=True)
_reset_prefix = st.session_state.pop("reset_form_prefix", None)
if _reset_prefix:
    for _key in list(st.session_state):
        if str(_key).startswith(_reset_prefix):
            st.session_state.pop(_key, None)

# ==========================================
# ---------- Khmer on screen (saved values stay English so reports and history keep working) ----------
KM = {
    # fridge / FIFO / sticker / sales / priority
    "Clean & cold": "ស្អាត និងត្រជាក់", "Dirty": "កខ្វក់", "Not cold": "មិនត្រជាក់", "Broken": "ខូច", "No fridge": "គ្មានទូទឹកកក",
    "Good": "ល្អ", "Needs fixing": "ត្រូវរៀបចំ", "Fixed today": "បានរៀបចំថ្ងៃនេះ",
    "Old / faded": "ចាស់ / ស្រអាប់", "Missing": "គ្មាន",
    "⬆️ Up": "⬆️ កើនឡើង", "➡️ Same": "➡️ ដដែល", "⬇️ Down": "⬇️ ធ្លាក់ចុះ",
    "Low": "ទាប", "Normal": "ធម្មតា", "Urgent": "បន្ទាន់",
    # reasons
    "Season / weather": "រដូវ / អាកាសធាតុ", "Competitor": "គូប្រជែង", "Price": "តម្លៃ", "Bun quality": "គុណភាពនំ",
    "Delivery late / missing": "ដឹកយឺត / ខ្វះ", "Fewer customers at the area": "ភ្ញៀវក្នុងតំបន់តិច",
    "Shop moved / renovating": "ហាងប្តូរទីតាំង / កំពុងជួសជុល", "New promotion worked": "ប្រូម៉ូសិនថ្មីមានប្រសិទ្ធភាព",
    "Good display / new fridge": "តាំងល្អ / ទូទឹកកកថ្មី", "Other": "ផ្សេងៗ",
    # who follows up
    "Admin": "Admin", "Sales": "ផ្នែកលក់ (Sales)", "Delivery": "ផ្នែកដឹកជញ្ជូន", "Production": "ផ្នែកផលិត",
    # problems (with and without emoji)
    "🧊 Fridge broken / not cold": "🧊 ទូទឹកកកខូច / មិនត្រជាក់", "🏷️ Sticker old / missing": "🏷️ ស្ទីគ័រចាស់ / គ្មាន",
    "🚚 Delivery late": "🚚 ដឹកយឺត", "🥟 Bun quality / taste": "🥟 គុណភាព / រសជាតិនំ", "📦 Wrong or short order": "📦 ដឹកខុស ឬខ្វះ",
    "💵 Price / payment": "💵 តម្លៃ / ការទូទាត់", "🆚 Competitor pushing": "🆚 គូប្រជែងប្រជែងខ្លាំង",
    "🗓️ Old buns not rotated (FIFO)": "🗓️ នំចាស់មិនបានរៀបមុន (FIFO)", "➕ Wants a new item": "➕ ចង់បានមុខទំនិញថ្មី", "❓ Other": "❓ ផ្សេងៗ",
    # checklist items
    "Buns visible at the counter": "នំដាក់មើលឃើញនៅបញ្ជរ", "Steamer / microwave working": "ឆ្នាំងចំហុយ / មីក្រូវ៉េវដំណើរការ",
    "Menu or poster shows our buns": "មានម៉ឺនុយ ឬផ្ទាំងរូបភាពនំយើង", "Shop staff know how to heat buns": "បុគ្គលិកហាងចេះកំដៅនំ",
    "Fridge at the front, easy to see": "ទូទឹកកកនៅខាងមុខ ងាយមើលឃើញ", "Price tag shown": "មានស្លាកតម្លៃ",
    "Our buns not hidden by competitors": "នំយើងមិនត្រូវគូប្រជែងបាំង", "Poster / sign outside": "មានផ្ទាំងរូបភាព / ស្លាកខាងក្រៅ",
    "Fridge / shelf full enough": "ទូ / ធ្នើមាននំគ្រប់គ្រាន់", "Fridge near the canteen": "ទូទឹកកកនៅជិតអាហារដ្ឋាន",
    "Enough stock for break time": "ស្តុកគ្រប់សម្រាប់ម៉ោងសម្រាក", "Price fits students": "តម្លៃសមរម្យសម្រាប់សិស្ស",
    "Buns kept away from sun / dust": "នំការពារពីកម្តៅថ្ងៃ / ធូលី", "Delivery time fits break time": "ម៉ោងដឹកត្រូវនឹងម៉ោងសម្រាក",
    "Display clean": "កន្លែងតាំងស្អាត", "Our buns placed well": "នំយើងតាំងបានល្អ",
    "Covered from sun / dust": "មានគម្របការពារកម្តៅថ្ងៃ / ធូលី", "Steamer working": "ឆ្នាំងចំហុយដំណើរការ", "Price sign shown": "មានស្លាកតម្លៃ",
    "Fridge installed & plugged in": "ទូទឹកកកបានដំឡើង និងដោតភ្លើង", "Stickers / poster put up": "បានបិទស្ទីគ័រ / ផ្ទាំងរូបភាព",
    "Owner knows prices & how to heat buns": "ម្ចាស់ហាងដឹងតម្លៃ និងរបៀបកំដៅនំ", "Owner has our phone / Telegram": "ម្ចាស់ហាងមានលេខទូរស័ព្ទ / Telegram យើង",
    # shop types and sizes
    "☕ Coffee shop": "☕ ហាងកាហ្វេ", "⛽ Gas station": "⛽ ស្ថានីយប្រេង", "🛒 Mart / shop": "🛒 ម៉ាត / ហាង",
    "🏫 School / canteen": "🏫 សាលា / អាហារដ្ឋាន", "🏛️ Office / ministry / hospital": "🏛️ ការិយាល័យ / ក្រសួង / មន្ទីរពេទ្យ",
    "🥖 Bakery / food shop": "🥖 ហាងនំបុ័ង / អាហារ", "🏪 Market stall": "🏪 តូបផ្សារ", "📦 Other": "📦 ផ្សេងៗ",
    "🟢 Big": "🟢 ធំ", "🟡 Medium": "🟡 មធ្យម", "⚪ Small": "⚪ តូច", "💤 No orders (28 d)": "💤 គ្មានការបញ្ជាទិញ (២៨ ថ្ងៃ)",
    # zones
    "1 · Center (Daun Penh · 7 Makara · BKK)": "1 · កណ្ដាលក្រុង (ដូនពេញ · ៧មករា · BKK)", "2 · Tuol Kouk": "2 · ទួលគោក",
    "3 · North (Russey Keo · Chroy Changvar · Prek Pnov)": "3 · ខាងជើង (ឫស្សីកែវ · ជ្រោយចង្វារ · ព្រែកព្នៅ)",
    "4 · West (Sen Sok · Phnom Penh Thmey)": "4 · ខាងលិច (សែនសុខ · ភ្នំពេញថ្មី)",
    "5 · South-west (Pou Senchey · Kamboul · Airport)": "5 · និរតី (ពោធិ៍សែនជ័យ · កំបូល · អាកាសយានដ្ឋាន)",
    "6 · South (Chamkarmon · Mean Chey · Dangkao)": "6 · ខាងត្បូង (ចំការមន · មានជ័យ · ដង្កោ)",
    "7 · East (Chbar Ampov · Boeng Snor · Prek Eng)": "7 · ខាងកើត (ច្បារអំពៅ · បឹងស្នោរ · ព្រែកឯង)",
    "8 · Takhmao edge": "8 · ជាយក្រុងតាខ្មៅ", "❓ Zone not set": "❓ មិនទាន់កំណត់តំបន់",
    "🚫 Outside Phnom Penh": "🚫 នៅក្រៅភ្នំពេញ",
    # what was fixed, status, review
    "Sticker changed": "បានប្តូរស្ទីគ័រ", "FIFO fixed": "បានរៀប FIFO", "Fridge/display cleaned": "បានសម្អាត / រៀបទូ",
    "Open": "មិនទាន់ដោះស្រាយ", "No problem": "គ្មានបញ្ហា", "Fixed": "បានដោះស្រាយ",
    "To review": "រង់ចាំពិនិត្យ", "Redo": "ត្រូវធ្វើឡើងវិញ", "Approved": "បានអនុម័ត", "All": "ទាំងអស់",
    # sections
    "📋 Today's plan": "📋 ផែនការថ្ងៃនេះ", "📝 New visit": "📝 ចុះហាងថ្មី", "🆕 New customers": "🆕 អតិថិជនថ្មី",
    "✅ Review visits": "✅ ពិនិត្យរបាយការណ៍", "📊 Visit report": "📊 របាយការណ៍ចុះហាង", "🔴 Open problems": "🔴 បញ្ហាមិនទាន់ដោះស្រាយ",
    "📈 Did it help?": "📈 មានប្រសិទ្ធភាពទេ?", "🏅 Scorecard": "🏅 តារាងពិន្ទុ", "⚙️ Shops & zones": "⚙️ ហាង និងតំបន់",
}
KM_PLAIN_PROBLEM = {p.split(" ", 1)[1]: KM[p].split(" ", 1)[1] for p in [
    "🧊 Fridge broken / not cold", "🏷️ Sticker old / missing", "🚚 Delivery late", "🥟 Bun quality / taste", "📦 Wrong or short order",
    "💵 Price / payment", "🆚 Competitor pushing", "🗓️ Old buns not rotated (FIFO)", "➕ Wants a new item", "❓ Other"]}


def _km(v):
    """Khmer text for a saved English value (unknown values are shown as they are)."""
    return KM.get(v, v) if isinstance(v, str) else v


def _km_list(text, sep="; "):
    """'Sticker old / missing; Delivery late' -> Khmer, part by part."""
    if str(text) in ("-", "", "nan"):
        return "-"
    return ", ".join(KM_PLAIN_PROBLEM.get(p, KM.get(p, p)) for p in str(text).split(sep))


def _km_loc(label):
    """Location check label in Khmer."""
    t = str(label)
    if t.startswith("✅"):
        return "✅ នៅហាង"
    if t.startswith("❓"):
        return "❓ គ្មាន GPS"
    if t.startswith("📍 GPS saved"):
        return "📍 រក្សាទុក GPS (ហាងមិនទាន់មានទីតាំងលើផែនទី)"
    m = re.match(r"⚠️ (.+) from shop", t)
    return f"⚠️ ឆ្ងាយពីហាង {m.group(1)}" if m else t


def _km_days(text):
    t = str(text)
    if t == "never":
        return "មិនធ្លាប់"
    return re.sub(r"(\d+) d ago", r"\1 ថ្ងៃមុន", t)


# 🏪 SHOP VISITS: staff visit customer shops (check-in GPS, photos, checklist, problems, report)
# ==========================================
VISIT_COLS = ["Date", "VisitID", "Staff", "Customer", "Check-in", "Minutes", "Lat", "Lon", "GPS accuracy m",
              "Distance m", "Location check", "Fridge", "Display FIFO", "Old/damaged pcs", "Sticker",
              "Stickers changed", "Customer says sales", "Sales reason", "Competitor", "App trend %",
              "Problems", "Priority", "Follow-up by", "Notes", "Customer request", "Satisfaction",
              "Photos", "Status", "Fixed by", "Fixed at", "Fix note", "Zone",
              "Shop type", "Checks", "Check score %", "Size", "Fix done",
              "Review", "Reviewed by", "Reviewed at", "Review note"]
VISIT_AREA = AREA_LABEL[PP]       # only Phnom Penh customers are visited
VISIT_AT_SHOP_M = 200            # check-in within this distance of the map pin = "At shop"
VISIT_GPS_MAX_AGE_S = 900        # a check-in older than 15 minutes must be done again
VISIT_PHOTO_DIR = "visit_photos"
VISIT_PROBLEMS = ["🧊 Fridge broken / not cold", "🏷️ Sticker old / missing", "🚚 Delivery late", "🥟 Bun quality / taste",
                  "📦 Wrong or short order", "💵 Price / payment", "🆚 Competitor pushing", "🗓️ Old buns not rotated (FIFO)",
                  "➕ Wants a new item", "❓ Other"]
VISIT_REASONS = ["-", "Season / weather", "Competitor", "Price", "Bun quality", "Delivery late / missing",
                 "Fewer customers at the area", "Shop moved / renovating", "New promotion worked", "Good display / new fridge", "Other"]
VISIT_FOLLOWUP = ["-", "Admin", "Sales", "Delivery", "Production"]


# ---------- Phnom Penh visit zones ----------
VISIT_DAILY_TARGET = 3            # visits each staff should do per day
VISIT_ZONE_NOT_SET = "❓ Zone not set"
# zone -> words found in the customer name (Khmer + English). First guess only: Admin corrects in 🗺️ Zones.
VISIT_ZONES = {
    "1 · Center (Daun Penh · 7 Makara · BKK)": [
        "ផ្សារថ្មី", "វិមានឯករាជ្យ", "ស៊ីសុវត្", "ក្រោយវាំង", "វត្តភ្នំ", "វត្ដភ្នំ", "បឹងកេងកង", "អូឬស្សី", "អូរឬស្សី",
        "អូឡាំព", "អូរឡាំពិក", "ចតុមុខ", "យុគន្ធ", "MART វិមានភ្នំពេញ", "ផ្សារកណ្ដាល", "ផ្សារកណ្តាល", "កោះពេជ្រ",
        "DAUN PENH", "DOUN PENH", "PSAR THMEI", "ទួលស្វាយព្រៃ", "TOUL SVAY PREY", "TUOL SVAY PREY",
        "CHAKTUMUK", "CHAKTOMUK", "KENG KANG", "BENG KANG", "TONLE BASSAC", "ទន្លេបាសាក់", "បុរីកីឡា", "កាល់ម៉ែត្រ", "CALMETTE", "CENTRAL MARKET", "7 MAKARA", "7MAKARA", "៧មករា", "7 មករា", "7មករា",
        "ក្រសួងសេដ្ឋកិច្ច", "ក្រសួងការងារ", "BKK", "OLYMPI", "OLYMAPIC", "DIAMOND ISLAND", "RIVERSIDE"],
    "2 · Tuol Kouk": [
        "ទួលគោក", "ទូលគោក", "បឹងកក់", "ទឹកល្អក់", "ដីហ៊ុយ", "ដីហុយ", "ដេប៉ូ", "បឹងសាឡាង", "ពេទ្យរុស្សី",
        "មន្ទីរពេទ្យកុមារជាតិ", "TOUL KOK", "TUOLKORK", "BOENG KAK", "BOEUNG KAK", "BEONG KAK", "DEPO", "កម្ពុជាក្រោម", "កម្ពជាក្រោម", "TUOL KORK", "TOUL KORK", "TK STORE", "TK AVENUE"],
    "3 · North (Russey Keo · Chroy Changvar · Prek Pnov)": [
        "ឫស្សីកែវ", "ឬស្សីកែវ", "ជ្រោយចង្វា", "ព្រែកព្នៅ", "ព្រែកលាប", "ទួលសង្កែ", "ព្រែកតាទែន", "ព្រែកអញ្ចាញ",
        "គីឡូ", "ផ្លូវលេខ6A", "6A", "OCIC", "RUSSEY KEO", "CHROY CHANGVAR", "PREK PNOV", "PREK LEAP",
        "TUOL SANGKAE", "TOUL SANGKE", "KILO", "REOUSSEY KEO", "CHROY CHONG VA", "CHROY CHANG VA",
        "ព្រែកលាភ", "598"],
    "4 · West (Sen Sok · Phnom Penh Thmey)": [
        "សែនសុខ", "ភ្នំពេញថ្មី", "ទឹកថ្លា", "ក្រាំងធ្នង់", "ក្រាំងធ្នុង", "ឈូកមាស", "អ៊ីអន2", "អ៊ីអន ២", "ពិភពថ្មី",
        "បៀលប្រាយ", "បុរីវិមានភ្នំពេញថ្មី", "សំរោងអណ្ដែត", "សំរោងអណ្តែត",
        "PHNOM PENH THMEY", "PP THMEY", "TEUK THLA", "TUEK THLA", "CHUK MEAS", "SEN SOK",
        "GRAND PHNOM PENH", "ផ្លូវ 2004", "ផ្លូវ2004", "2004", "2002", "ផ្សារត្រពាំងឈួក", "SENSOK", "AEON 2", "AEON2"],
    "5 · South-west (Pou Senchey · Kamboul · Airport)": [
        "ពោធិ៍សែនជ័យ", "ពោធិសែនជ័យ", "ចោមចៅ", "កប់ស្រូវ", "កំបូល", "វេងស្រេង", "ពោធិចិនតុង", "ពោធិ៍ចិនតុង",
        "ត្រពាំងថ្លឹង", "ព្រៃទា", "កាំកូ", "ទួលពង្រ", "តាំងក្រសាំង", "ក្រសួងការពារជាតិ", "ចម្រើនផល",
        "ព្រៃជីសាក់", "គួរស្រូវ", "ឈូកវ៉ា", "បែកចាន", "ជម្ពូវ័ន្ត", "ជម្ពូវន្ត", "ជម្ពូវ័ន", "អង្គតាមិញ", "CHOMPOU VORN", "បុរីសន្តិភាព", "បុរីសន្ដិភាព", "CAMCO", "POCHENTONG", "AIRPORT",
        "POR SEN CHEY", "POU SENCHEY", "PORSENCHEY", "CHOM CHAO", "CHOMCHAO", "KAMBOUL", "KAKAB", "VENG SRENG", "KOB SROV",
        "KORK KLEANG"],
    "6 · South (Chamkarmon · Mean Chey · Dangkao)": [
        "ចំការដូង", "ចំកាដូង", "ស្ទឹងមានជ័យ", "ចាក់អង្រែ", "បឹងទំពុន", "ទួលទំពូង", "ក្បាលថ្នល់", "ដង្កោ",
        "ផ្សាររុស្សី", "បឹងត្របែក",  "ផ្លូវសឡា", 
        "271", "CHIP MONG 271", "MEAN CHEY", "CHAMKARMON", "TOUL TOM POUNG", "CHAK ANGRE", "CHAKANGRE",
        "STEUNG MEANCHEY", "STUNG MEANCHEY", "TUOL TOMPOUNG", "TOUL TUMPUNG", "RUSSIAN MARKET", "DANGKAO", "BOENG TUMPUN",
        "CHAMKAR DOUNG", "CHAMKA DOUNG", "PHSAR DEUM THKOV", "DEUM THKOV", "ដើមថ្កូវ", "TOUL TOMPUNG",
        "ព្រៃស", "PREY SAR", "CHERNG EK", "CHOEUNG EK", "ជើងឯក", "ត្នោតជ្រុំ", "អ៊ីអន 3", "អ៊ីអន3", "AEON 3", "AEON3", "AEON MEAN CHEY",
        "បុរីសូនី", "បូរីសូនី", "ពោធិញាណ", "ពោធិ៍ញ្ញាណ", "ពោធិ៍ញាណ"],
    "7 · East (Chbar Ampov · Boeng Snor · Prek Eng)": [
        "ច្បារអំពៅ", "ច្បាអំពៅ", "បឹងស្នោរ", "ព្រែកឯក", "ជាសុផារ៉ា", "និរោធ", "ព្រែកប្រា", "កោះនរា", "វាលស្បូវ",
        "CHBAR AMPOV", "CHBA AMPOV", "PREK ENG", "NIROTH", "KOH NORA", "VEAL SBOV", "BOENG SNOR",
        "ជាសុផារា", "កៀនស្វាយ", "KIEN SVAY"],
    "8 · Takhmao edge": ["តាខ្មៅ", "ព្រែកហូរ", "ព្រែកសំរោង", "ផ្សារសិត្បូ", "TAKHMAO", "TA KHMAO"],
}
VISIT_ZONE_NAMES = list(VISIT_ZONES) + [VISIT_ZONE_NOT_SET, "🚫 Outside Phnom Penh"]
_VISIT_ZONE_WORDS = sorted(((w.upper().replace(" ", ""), z) for z, ws in VISIT_ZONES.items() for w in ws),
                           key=lambda x: -len(x[0]))          # longest words first ("CHIP MONG 271" before "271")


def _visit_zone_auto(name):
    return _visit_zone_auto_info(name)[0]


VISIT_ZONE_OUTSIDE = "🚫 Outside Phnom Penh"
VISIT_OUTSIDE_WORDS = ["ឧត្ដមានជ័យ", "ឧត្តរមានជ័យ", "ODDAR MEANCHEY"]


def _visit_zone_auto_info(name):
    """-> (zone, note). note = "" when clear, or why a person should check it (two zones / another province).
    Number words (street 2004, 598…) must stand alone; other words may be part of the name."""
    raw = unicodedata.normalize("NFC", str(name)).replace("\u200b", "")
    t = raw.upper().replace(" ", "")
    tokens = set(re.split(r"[\s(),.]+", raw.upper()))
    try:
        prov, how = detect_province(raw, allow_pp=False)
        if how != "province name":          # town / market names repeat across provinces ("ផ្សារឈូក" is also in Kampot)
            prov = None
    except Exception:
        prov = None
    if (prov and prov != "Kandal") or any(w.upper().replace(" ", "") in t for w in VISIT_OUTSIDE_WORDS):
        return VISIT_ZONE_OUTSIDE, f"name says {prov or 'Oddar Meanchey'}"
    hits = []
    for w, z in _VISIT_ZONE_WORDS:
        if (w in tokens) if w.isdigit() else (w in t):
            hits.append((len(w), z))
    if not hits:
        return VISIT_ZONE_NOT_SET, ""
    zones = []
    for _l, z in sorted(hits, reverse=True):
        if z not in zones:
            zones.append(z)
    return zones[0], ("name has 2 zones: " + " / ".join(z.split(" (")[0] for z in zones[:2])) if len(zones) > 1 else ""


def _visit_shop_settings():
    try:
        return read_raw(VISIT_ZONE_FILE, VISIT_SET_COLS, max_age=300)
    except Exception:
        return pd.DataFrame(columns=VISIT_SET_COLS)


def _visit_zone_overrides():
    """{normalised customer: zone} set by Admin."""
    df = _visit_shop_settings()
    return {norm_name(c): z for c, z in zip(df["Customer"], df["Zone"]) if z in VISIT_ZONE_NAMES}


def _visit_type_map(names):
    """{key: shop type}: Admin's choice first, then the guess from the name."""
    df = _visit_shop_settings()
    over = {norm_name(c): t for c, t in zip(df["Customer"], df["Type"]) if t in VISIT_TYPE_NAMES}
    return {k: over.get(k) or _visit_type_auto(n) for k, n in names.items()}


# Khan centres (Khmer name, lat, lon, zone): only a rough middle point per khan. Zones come from the real borders below.
_Z = list(VISIT_ZONES)
VISIT_KHANS = [
    ("ដូនពេញ", 11.5750, 104.9200, _Z[0]), ("៧មករា", 11.5650, 104.9100, _Z[0]), ("បឹងកេងកង", 11.5520, 104.9220, _Z[0]),
    ("កោះពេជ្រ", 11.5530, 104.9420, _Z[0]),
    ("ទួលគោក", 11.5800, 104.8930, _Z[1]),
    ("ឫស្សីកែវ", 11.6250, 104.9120, _Z[2]), ("ជ្រោយចង្វារ", 11.6100, 104.9450, _Z[2]), ("ព្រែកព្នៅ", 11.6800, 104.8400, _Z[2]),
    ("សែនសុខ", 11.6050, 104.8620, _Z[3]),
    ("ពោធិ៍សែនជ័យ", 11.5300, 104.8000, _Z[4]), ("កំបូល", 11.5450, 104.7350, _Z[4]), ("ពោធិ៍ចិនតុង", 11.5480, 104.8450, _Z[4]),
    ("ចំការមន", 11.5380, 104.9250, _Z[5]), ("មានជ័យ", 11.5150, 104.9150, _Z[5]), ("ដង្កោ", 11.4700, 104.8650, _Z[5]),
    ("ច្បារអំពៅ", 11.5300, 104.9550, _Z[6]),
    ("តាខ្មៅ", 11.4800, 104.9480, _Z[7]),
]
VISIT_KHAN_EDGE_M = 1500         # a pin just outside the border (river bank, map drift) still gets the nearest khan
# Real khan borders (lat,lon), simplified to ~25 m. Source: Open Development Cambodia, administrative boundaries 2014,
# via geoBoundaries (CC BY 4.0). 2014 borders: Boeng Keng Kang is still inside Chamkar Mon and Kamboul inside Pou Senchey,
# so those two are split below by Mao Tse Tung Blvd and by longitude.
_VISIT_KHAN_SHAPES_RAW = {
    "Doun Penh": (
        "11.56197,104.94662;11.56201,104.94174;11.56622,104.93542;11.56813,104.93370;11.57305,104.93131;"
        "11.57530,104.92941;11.58774,104.92140;11.58889,104.92119;11.58783,104.91441;11.58506,104.91443;"
        "11.58334,104.90783;11.57920,104.90527;11.57500,104.90442;11.57430,104.90386;11.57026,104.90496;"
        "11.57158,104.91843;11.56727,104.91850;11.55590,104.92046;11.55605,104.92457;11.55701,104.93078;"
        "11.55673,104.93401;11.55771,104.95251;11.56003,104.94861;11.56197,104.94662"),
    "Prampir Meakkakra": (
        "11.55590,104.92046;11.56727,104.91850;11.57158,104.91843;11.57054,104.90629;11.55775,104.90813;"
        "11.55590,104.91042;11.55569,104.91127;11.55590,104.92046"),
    "Chamkar Mon": (
        "11.55590,104.92046;11.55569,104.91127;11.55590,104.91042;11.55775,104.90813;11.54835,104.89842;"
        "11.54597,104.89921;11.54460,104.90084;11.54311,104.90648;11.54221,104.90782;11.52824,104.91579;"
        "11.52670,104.91861;11.52670,104.92180;11.53132,104.93282;11.53618,104.93144;11.53824,104.93184;"
        "11.53991,104.93327;11.54121,104.93523;11.54229,104.93833;11.54382,104.94098;11.54626,104.94397;"
        "11.55771,104.95251;11.55673,104.93401;11.55701,104.93078;11.55605,104.92457;11.55590,104.92046"),
    "Tuol Kouk": (
        "11.55775,104.90813;11.57054,104.90629;11.57026,104.90496;11.57430,104.90386;11.57500,104.90442;"
        "11.57920,104.90527;11.58334,104.90783;11.58577,104.90071;11.59093,104.89749;11.58492,104.88840;"
        "11.58365,104.88741;11.56571,104.88856;11.56151,104.89055;11.55831,104.88749;11.55638,104.88676;"
        "11.55332,104.88720;11.55099,104.88868;11.54974,104.89071;11.54968,104.89561;11.54811,104.89707;"
        "11.54865,104.89763;11.54835,104.89842;11.55775,104.90813"),
    "Dangkao": (
        "11.42880,104.92259;11.45162,104.92276;11.46658,104.91822;11.48450,104.92138;11.48236,104.91362;"
        "11.50217,104.91351;11.50502,104.91378;11.51899,104.91332;11.52011,104.90739;11.52302,104.89670;"
        "11.52179,104.89394;11.52254,104.88851;11.52198,104.88374;11.52188,104.87548;11.51795,104.87810;"
        "11.51636,104.87818;11.51460,104.87705;11.51142,104.87256;11.51010,104.86558;11.50666,104.86069;"
        "11.50563,104.85716;11.50637,104.84484;11.50601,104.84009;11.50501,104.83865;11.50373,104.83785;"
        "11.50134,104.83844;11.49964,104.83843;11.50034,104.83587;11.50056,104.82917;11.50015,104.82088;"
        "11.50079,104.81851;11.49541,104.81771;11.49248,104.81993;11.49109,104.82011;11.48999,104.81759;"
        "11.48146,104.81521;11.48075,104.80327;11.47876,104.79899;11.47673,104.79069;11.47623,104.78629;"
        "11.45600,104.78098;11.45609,104.78354;11.45545,104.78451;11.45429,104.78514;11.45297,104.78458;"
        "11.45028,104.78227;11.44925,104.78231;11.44758,104.78361;11.44687,104.78576;11.44532,104.78845;"
        "11.44535,104.78919;11.44722,104.79146;11.44718,104.79323;11.44634,104.79371;11.44430,104.79301;"
        "11.44349,104.79316;11.44350,104.79491;11.44491,104.79712;11.44514,104.79859;11.44483,104.79935;"
        "11.44305,104.79912;11.44190,104.79769;11.44029,104.79758;11.43632,104.80099;11.43400,104.80146;"
        "11.43159,104.80484;11.43000,104.81062;11.43081,104.81602;11.43128,104.81672;11.43240,104.81799;"
        "11.43333,104.81842;11.43587,104.81935;11.43678,104.81925;11.43739,104.81889;11.43800,104.81553;"
        "11.43883,104.81512;11.43937,104.81542;11.44076,104.81802;11.44356,104.82039;11.44407,104.82214;"
        "11.44277,104.82365;11.43971,104.82557;11.43908,104.82679;11.43764,104.82680;11.43606,104.82748;"
        "11.43091,104.83080;11.43035,104.85217;11.42866,104.85298;11.42817,104.85453;11.42533,104.85542;"
        "11.42438,104.85623;11.42382,104.85756;11.42368,104.85852;11.42451,104.86222;11.42625,104.86442;"
        "11.42249,104.87344;11.43621,104.88066;11.43589,104.88277;11.43426,104.88517;11.43263,104.88638;"
        "11.43050,104.88725;11.43020,104.88861;11.43549,104.89658;11.43499,104.90145;11.43573,104.90569;"
        "11.43535,104.90792;11.43310,104.91208;11.43239,104.91309;11.43109,104.91256;11.43026,104.91352;"
        "11.43003,104.91670;11.42889,104.91758;11.42880,104.92259"),
    "Mean Chey": (
        "11.49386,104.94677;11.49951,104.94373;11.50415,104.94262;11.52583,104.93510;11.53132,104.93282;"
        "11.52670,104.92180;11.52670,104.91861;11.52718,104.91733;11.52923,104.91497;11.54221,104.90782;"
        "11.54311,104.90648;11.54460,104.90084;11.54597,104.89921;11.54835,104.89842;11.54865,104.89763;"
        "11.54811,104.89707;11.54968,104.89561;11.54974,104.89071;11.54908,104.88932;11.54861,104.88671;"
        "11.54720,104.87221;11.54514,104.86151;11.52186,104.86292;11.52198,104.88374;11.52254,104.88851;"
        "11.52179,104.89394;11.52302,104.89670;11.52011,104.90739;11.51899,104.91332;11.50502,104.91378;"
        "11.50217,104.91351;11.48236,104.91362;11.48450,104.92138;11.49386,104.94677"),
    "Russey Keo": (
        "11.58889,104.92119;11.60243,104.92113;11.60941,104.92055;11.61557,104.91935;11.62134,104.91652;"
        "11.62636,104.91235;11.63187,104.90658;11.63299,104.90530;11.63541,104.90077;11.64067,104.88733;"
        "11.64276,104.88255;11.64488,104.87898;11.65146,104.87317;11.65857,104.86843;11.64976,104.85613;"
        "11.64838,104.85776;11.64850,104.86109;11.64347,104.86333;11.64320,104.86765;11.64245,104.86981;"
        "11.64075,104.87161;11.63660,104.87385;11.63479,104.87432;11.63271,104.87387;11.62979,104.87183;"
        "11.62753,104.87159;11.62440,104.87205;11.62369,104.87295;11.62459,104.87496;11.62453,104.87729;"
        "11.62106,104.87805;11.62052,104.87889;11.61480,104.88219;11.61263,104.88496;11.61113,104.88556;"
        "11.60756,104.88556;11.59039,104.89626;11.59093,104.89749;11.58577,104.90071;11.58334,104.90783;"
        "11.58506,104.91443;11.58783,104.91441;11.58889,104.92119"),
    "Saensokh": (
        "11.59039,104.89626;11.60756,104.88556;11.61113,104.88556;11.61263,104.88496;11.61480,104.88219;"
        "11.62052,104.87889;11.62106,104.87805;11.62453,104.87729;11.62459,104.87496;11.62369,104.87295;"
        "11.62440,104.87205;11.62753,104.87159;11.62979,104.87183;11.63271,104.87387;11.63479,104.87432;"
        "11.63660,104.87385;11.64075,104.87161;11.64245,104.86981;11.64320,104.86765;11.64347,104.86333;"
        "11.64850,104.86109;11.64838,104.85776;11.64976,104.85613;11.63481,104.83614;11.62054,104.83875;"
        "11.61949,104.83763;11.61881,104.83592;11.61211,104.83283;11.60568,104.83289;11.60241,104.83241;"
        "11.59594,104.83301;11.59091,104.83214;11.58867,104.83151;11.58614,104.83000;11.57945,104.82337;"
        "11.56861,104.82364;11.56916,104.82493;11.56828,104.83340;11.56800,104.83478;11.56655,104.83478;"
        "11.56642,104.85332;11.56765,104.86429;11.56065,104.86291;11.55481,104.86276;11.54514,104.86151;"
        "11.54720,104.87221;11.54781,104.88028;11.54908,104.88932;11.54974,104.89071;11.55178,104.88799;"
        "11.55523,104.88679;11.55638,104.88676;11.55831,104.88749;11.56151,104.89055;11.56571,104.88856;"
        "11.58365,104.88741;11.58492,104.88840;11.59039,104.89626"),
    "Pur SenChey": (
        "11.45600,104.78098;11.47623,104.78629;11.47673,104.79069;11.47876,104.79899;11.48075,104.80327;"
        "11.48146,104.81521;11.48999,104.81759;11.49109,104.82011;11.49248,104.81993;11.49541,104.81771;"
        "11.50079,104.81851;11.50015,104.82088;11.50056,104.82917;11.50034,104.83587;11.49964,104.83843;"
        "11.50134,104.83844;11.50373,104.83785;11.50501,104.83865;11.50601,104.84009;11.50637,104.84484;"
        "11.50563,104.85716;11.50666,104.86069;11.51010,104.86558;11.51142,104.87256;11.51460,104.87705;"
        "11.51693,104.87826;11.51930,104.87747;11.52188,104.87548;11.52186,104.86292;11.54455,104.86140;"
        "11.55481,104.86276;11.56065,104.86291;11.56765,104.86429;11.56642,104.85332;11.56655,104.83478;"
        "11.56800,104.83478;11.56828,104.83340;11.56916,104.82493;11.56861,104.82364;11.57945,104.82337;"
        "11.57993,104.80913;11.58194,104.80709;11.58325,104.80479;11.58457,104.80412;11.58552,104.80207;"
        "11.58655,104.80094;11.59128,104.79981;11.60149,104.79827;11.60396,104.79701;11.60838,104.78986;"
        "11.61035,104.78611;11.61052,104.78499;11.61000,104.78435;11.60887,104.78419;11.60585,104.78220;"
        "11.60527,104.78166;11.60519,104.77971;11.60401,104.77898;11.60267,104.77824;11.59927,104.77829;"
        "11.59850,104.77759;11.59849,104.77597;11.59394,104.77182;11.59288,104.76811;11.59186,104.76043;"
        "11.59084,104.75908;11.59091,104.75567;11.59186,104.75475;11.59095,104.75419;11.59145,104.75324;"
        "11.59029,104.75176;11.59128,104.75060;11.59041,104.74706;11.59063,104.74599;11.58977,104.74528;"
        "11.58954,104.74214;11.58748,104.74094;11.58338,104.73994;11.58306,104.73635;11.58190,104.73545;"
        "11.58119,104.73299;11.57843,104.73187;11.57448,104.72842;11.57595,104.72505;11.57497,104.72415;"
        "11.57459,104.72264;11.57500,104.72056;11.57581,104.71924;11.57594,104.71427;11.57545,104.71296;"
        "11.57403,104.71266;11.57289,104.71320;11.57222,104.71415;11.57216,104.72142;11.56845,104.72131;"
        "11.56731,104.72304;11.56662,104.72341;11.56486,104.72299;11.56386,104.72215;11.56239,104.71936;"
        "11.56081,104.72062;11.55937,104.72314;11.55795,104.72456;11.55633,104.72541;11.55050,104.72736;"
        "11.54406,104.72791;11.54427,104.73048;11.54367,104.73539;11.54585,104.73855;11.54577,104.73976;"
        "11.54294,104.74258;11.54106,104.74345;11.53825,104.74365;11.53629,104.74269;11.53378,104.74379;"
        "11.52981,104.74436;11.52912,104.74501;11.52760,104.74873;11.53074,104.75475;11.53091,104.75599;"
        "11.52730,104.75773;11.52347,104.76111;11.52055,104.76465;11.51861,104.76818;11.51013,104.76861;"
        "11.50211,104.76810;11.50042,104.76596;11.49608,104.76308;11.49173,104.76269;11.49147,104.75889;"
        "11.48899,104.75845;11.48915,104.74983;11.48643,104.74973;11.48632,104.74854;11.48454,104.74837;"
        "11.48375,104.74630;11.47897,104.74627;11.47803,104.74490;11.45957,104.74474;11.45459,104.74430;"
        "11.45489,104.74556;11.45467,104.74798;11.45659,104.75163;11.45645,104.75283;11.45575,104.75408;"
        "11.45277,104.75390;11.45117,104.75516;11.45046,104.75784;11.45055,104.75938;11.45139,104.76025;"
        "11.45262,104.76024;11.45379,104.75936;11.45651,104.75574;11.45785,104.75564;11.45891,104.75688;"
        "11.45895,104.75833;11.45727,104.76031;11.45714,104.76293;11.45753,104.76410;11.45961,104.76551;"
        "11.46273,104.76362;11.46354,104.76435;11.46385,104.76572;11.46355,104.76687;11.46196,104.76919;"
        "11.46187,104.77138;11.46296,104.77320;11.46467,104.77412;11.46673,104.77639;11.46695,104.77733;"
        "11.46633,104.77845;11.46539,104.77899;11.46452,104.77883;11.46348,104.77578;11.46215,104.77468;"
        "11.45893,104.77393;11.45774,104.77425;11.45734,104.77504;11.45780,104.77781;11.45620,104.77869;"
        "11.45580,104.77967;11.45600,104.78098"),
    "Chraoy Chongvar": (
        "11.71099,104.96837;11.71134,104.96003;11.71506,104.95901;11.72210,104.95214;11.72593,104.94922;"
        "11.73195,104.94773;11.73320,104.94712;11.73447,104.94548;11.73579,104.93983;11.73632,104.91745;"
        "11.72573,104.91760;11.71779,104.91655;11.71559,104.91528;11.71227,104.91256;11.71000,104.91146;"
        "11.69934,104.90885;11.69689,104.90682;11.69145,104.90044;11.68840,104.89984;11.68699,104.89853;"
        "11.68528,104.89783;11.68386,104.89972;11.67242,104.89965;11.67264,104.86267;11.66923,104.86063;"
        "11.65146,104.87317;11.64488,104.87898;11.64276,104.88255;11.63671,104.89777;11.63299,104.90530;"
        "11.62636,104.91235;11.62134,104.91652;11.61557,104.91935;11.60941,104.92055;11.60243,104.92113;"
        "11.58774,104.92140;11.57530,104.92941;11.57305,104.93131;11.56813,104.93370;11.56482,104.93710;"
        "11.56201,104.94174;11.56197,104.94662;11.56336,104.94593;11.58070,104.94471;11.58539,104.94402;"
        "11.59230,104.94257;11.60592,104.93748;11.62235,104.93228;11.62417,104.93327;11.62754,104.93341;"
        "11.63392,104.93459;11.63907,104.93613;11.64235,104.93756;11.65434,104.94594;11.65516,104.94725;"
        "11.66588,104.95069;11.67499,104.95449;11.67852,104.95716;11.67865,104.95878;11.68986,104.96216;"
        "11.69517,104.96317;11.70342,104.96547;11.71099,104.96837"),
    "Praek Pnov": (
        "11.67659,104.85519;11.68137,104.85224;11.68362,104.85147;11.69245,104.84644;11.71309,104.84035;"
        "11.71561,104.84004;11.71575,104.82684;11.71541,104.82292;11.71359,104.82120;11.71228,104.82300;"
        "11.70873,104.82414;11.70799,104.82313;11.70883,104.82210;11.70819,104.82018;11.70876,104.81928;"
        "11.70844,104.81821;11.70690,104.81766;11.70566,104.81624;11.70380,104.81528;11.69962,104.81588;"
        "11.69796,104.81526;11.69139,104.81455;11.68932,104.81709;11.68830,104.81696;11.68150,104.81120;"
        "11.67855,104.80994;11.67713,104.81016;11.67564,104.81122;11.67395,104.81373;11.67322,104.81199;"
        "11.67261,104.80053;11.67182,104.79893;11.67151,104.79705;11.67240,104.79424;11.67138,104.78096;"
        "11.66999,104.77973;11.66794,104.76957;11.66658,104.76677;11.66605,104.75312;11.66495,104.74989;"
        "11.66394,104.74852;11.65989,104.74733;11.65679,104.74814;11.65532,104.74779;11.65330,104.74696;"
        "11.65318,104.74618;11.64801,104.74249;11.63934,104.74388;11.62118,104.74019;11.60680,104.73443;"
        "11.60464,104.73450;11.60084,104.73609;11.59930,104.73601;11.59642,104.73466;11.59190,104.73159;"
        "11.58951,104.73172;11.58340,104.73434;11.58151,104.73468;11.58306,104.73635;11.58338,104.73994;"
        "11.58748,104.74094;11.58954,104.74214;11.58977,104.74528;11.59063,104.74599;11.59041,104.74706;"
        "11.59128,104.75060;11.59029,104.75176;11.59145,104.75324;11.59095,104.75419;11.59186,104.75475;"
        "11.59091,104.75567;11.59084,104.75908;11.59186,104.76043;11.59288,104.76811;11.59394,104.77182;"
        "11.59849,104.77597;11.59850,104.77759;11.59927,104.77829;11.60267,104.77824;11.60401,104.77898;"
        "11.60519,104.77971;11.60527,104.78166;11.60585,104.78220;11.60887,104.78419;11.61000,104.78435;"
        "11.61052,104.78499;11.61035,104.78611;11.60838,104.78986;11.60396,104.79701;11.60149,104.79827;"
        "11.59128,104.79981;11.58655,104.80094;11.58552,104.80207;11.58457,104.80412;11.58325,104.80479;"
        "11.58194,104.80709;11.57993,104.80913;11.57935,104.82230;11.58001,104.82425;11.58614,104.83000;"
        "11.58867,104.83151;11.59594,104.83301;11.60241,104.83241;11.60568,104.83289;11.61211,104.83283;"
        "11.61881,104.83592;11.61949,104.83763;11.62054,104.83875;11.63481,104.83614;11.64885,104.85464;"
        "11.65857,104.86843;11.67134,104.85907;11.67230,104.85775;11.67659,104.85519"),
    "Chbar Ampov": (
        "11.53904,105.04178;11.54154,105.03268;11.54352,105.01952;11.54389,105.01483;11.54369,105.00209;"
        "11.54301,104.99429;11.54609,104.97602;11.54922,104.96739;11.55148,104.96456;11.55375,104.95945;"
        "11.55771,104.95251;11.54626,104.94397;11.54382,104.94098;11.54229,104.93833;11.54121,104.93523;"
        "11.53991,104.93327;11.53824,104.93184;11.53618,104.93144;11.53230,104.93241;11.52583,104.93510;"
        "11.50415,104.94262;11.49951,104.94373;11.47770,104.95524;11.46708,104.96199;11.46410,104.96693;"
        "11.46316,104.96997;11.46239,104.97563;11.46299,104.98752;11.46465,104.99415;11.46587,105.00362;"
        "11.46613,105.01368;11.46542,105.02882;11.46621,105.02836;11.46920,105.02881;11.47214,105.03107;"
        "11.47511,105.03440;11.47768,105.03830;11.47961,105.04228;11.48090,105.04743;11.48240,105.05038;"
        "11.48304,105.04952;11.48353,105.02931;11.49123,105.02903;11.49440,105.02815;11.50356,105.02817;"
        "11.51567,105.02628;11.51874,105.02710;11.52213,105.02896;11.52794,105.03504;11.53120,105.03723;"
        "11.53805,105.04067;11.53904,105.04178"),
    "Ta Khmau": (
        "11.41932,104.94942;11.42118,104.95176;11.42231,104.95229;11.42492,104.95157;11.42450,104.95289;"
        "11.42322,104.95299;11.42310,104.95353;11.42475,104.95418;11.42423,104.95577;11.42502,104.95913;"
        "11.43257,104.95950;11.43239,104.97252;11.45529,104.96003;11.46268,104.97358;11.46316,104.96997;"
        "11.46410,104.96693;11.46708,104.96199;11.46879,104.96062;11.47083,104.95981;11.48109,104.95323;"
        "11.49386,104.94677;11.48450,104.92138;11.46658,104.91822;11.45162,104.92276;11.42880,104.92259;"
        "11.42830,104.92289;11.42848,104.94104;11.41924,104.94115;11.41932,104.94942"),
}
_VISIT_KHAN_INFO = {      # border name -> (Khmer khan name, zone)
    "Doun Penh": ("ដូនពេញ", _Z[0]), "Prampir Meakkakra": ("៧មករា", _Z[0]), "Chamkar Mon": ("ចំការមន", _Z[5]),
    "Tuol Kouk": ("ទួលគោក", _Z[1]), "Russey Keo": ("ឫស្សីកែវ", _Z[2]), "Chraoy Chongvar": ("ជ្រោយចង្វារ", _Z[2]),
    "Praek Pnov": ("ព្រែកព្នៅ", _Z[2]), "Saensokh": ("សែនសុខ", _Z[3]), "Pur SenChey": ("ពោធិ៍សែនជ័យ", _Z[4]),
    "Mean Chey": ("មានជ័យ", _Z[5]), "Dangkao": ("ដង្កោ", _Z[5]), "Chbar Ampov": ("ច្បារអំពៅ", _Z[6]),
    "Ta Khmau": ("តាខ្មៅ", _Z[7]),
}
VISIT_BKK_SOUTH_LAT = 11.5460     # Mao Tse Tung Blvd: north of it Chamkar Mon (2014) = BKK / Tonle Bassac / Koh Pich = Center
VISIT_KAMBOUL_LON = 104.755       # west of this, Pou Senchey (2014) = today's Kamboul
_VISIT_KHAN_SHAPES = {n: [tuple(float(x) for x in pt.split(",")) for pt in "".join(v).split(";") if pt]
                      for n, v in _VISIT_KHAN_SHAPES_RAW.items()}


def _visit_in_ring(lat, lon, ring):
    inside = False
    for i in range(len(ring)):
        y1, x1 = ring[i]
        y2, x2 = ring[i - 1]
        if (y1 > lat) != (y2 > lat) and lon < (x2 - x1) * (lat - y1) / (y2 - y1) + x1:
            inside = not inside
    return inside


def _visit_ring_dist_m(lat, lon, ring):
    """Shortest distance (m) from a point to a border line."""
    kx, ky = 111320.0 * math.cos(math.radians(lat)), 110540.0
    px, py = lon * kx, lat * ky
    best = float("inf")
    for i in range(len(ring)):
        y1, x1 = ring[i - 1]
        y2, x2 = ring[i]
        ax, ay, bx, by = x1 * kx, y1 * ky, x2 * kx, y2 * ky
        dx, dy = bx - ax, by - ay
        t = 0.0 if dx == dy == 0 else max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)))
        best = min(best, math.hypot(px - ax - t * dx, py - ay - t * dy))
    return best


def _visit_khan_of(lat, lon):
    """-> (border name, metres outside it: 0 when inside) or (None, None) when far from Phnom Penh."""
    if not (11.3 <= lat <= 11.85 and 104.6 <= lon <= 105.15):
        return None, None
    for n, ring in _VISIT_KHAN_SHAPES.items():
        if _visit_in_ring(lat, lon, ring):
            return n, 0.0
    d, n = min((_visit_ring_dist_m(lat, lon, ring), n) for n, ring in _VISIT_KHAN_SHAPES.items())
    return (n, d) if d <= VISIT_KHAN_EDGE_M else (None, None)


def _visit_zone_from_gps(lat, lon):
    """-> (zone, khan name) from a real location using the real khan borders, or (None, None) outside Phnom Penh."""
    try:
        lat, lon = float(lat), float(lon)
    except (TypeError, ValueError):
        return None, None
    n, _d = _visit_khan_of(lat, lon)
    if not n:
        return None, None
    khan, zone = _VISIT_KHAN_INFO[n]
    if n == "Chamkar Mon" and lat >= VISIT_BKK_SOUTH_LAT:
        khan, zone = ("កោះពេជ្រ" if lon >= 104.935 and lat <= 11.556 else "បឹងកេងកង"), _Z[0]
    elif n == "Pur SenChey" and lon < VISIT_KAMBOUL_LON:
        khan = "កំបូល"
    return zone, khan


def _visit_zone_info(names):
    """{key: (zone, where it came from)} — Admin's choice, else the real location, else the name. Reused for 2 minutes."""
    try:
        sig = (len(names), hash(tuple(sorted(names))), os.path.getmtime(VISIT_PIN_FILE) if os.path.exists(VISIT_PIN_FILE) else 0,
               os.path.getmtime(VISIT_ZONE_FILE) if os.path.exists(VISIT_ZONE_FILE) else 0, int(time.time() // 120),
               len(st.session_state.get("_visit_new", {}) or {}))
    except Exception:
        sig = None
    hit = st.session_state.get("_visit_zone_cache")
    if sig is not None and hit and hit[0] == sig:
        return hit[1]
    over = _visit_zone_overrides()
    registry, store = _visit_registry(), _visit_pin_store()
    try:
        auto = _visit_candidates_for(names, registry)[1]
    except Exception:
        auto = {}
    out = {}
    for k, n in names.items():
        if over.get(k):
            out[k] = (over[k], "👤 Admin")
            continue
        pin = _visit_pin(n, registry, store, auto)
        if pin:
            z, khan = _visit_zone_from_gps(*pin)
            if z:
                out[k] = (z, f"📍 ខណ្ឌ{khan} (GPS)")
                continue
            out[k] = (VISIT_ZONE_OUTSIDE, "🚫 ទីតាំងនៅក្រៅភ្នំពេញ (GPS) — ពិនិត្យ Master List")
            continue
        z, note = _visit_zone_auto_info(n)
        if z == VISIT_ZONE_OUTSIDE:
            out[k] = (z, "🚫 ឈ្មោះមានខេត្តផ្សេង — ពិនិត្យ Master List")
        elif note:
            out[k] = (z, "🔤⚠️ ឈ្មោះមាន 2 តំបន់ — សូមពិនិត្យ")
        else:
            out[k] = (z, "🔤 តាមឈ្មោះ")
    st.session_state["_visit_zone_cache"] = (sig, out)
    return out


def _visit_zone_map(names):
    """{key: zone} for every Phnom Penh customer: Admin's choice, then the real location, then the name."""
    return {k: v[0] for k, v in _visit_zone_info(names).items()}


def _visit_today_count(visits, user):
    if visits.empty:
        return 0
    v = visits[(visits["_dt"].dt.date == today_kh()) & (visits["Staff"] == user)]
    return int(v["Customer"].map(norm_name).nunique())


def _visit_progress(visits, user):
    done = _visit_today_count(visits, user)
    left = max(0, VISIT_DAILY_TARGET - done)
    st.progress(min(1.0, done / VISIT_DAILY_TARGET),
                text=f"ថ្ងៃនេះ: បានចុះ {done} / {VISIT_DAILY_TARGET} ហាង" + (" 🎉 ដល់គោលដៅហើយ" if not left else f" · នៅសល់ {left}"))


def _visit_zone_picker(zone_map, key, due=None):
    """Zone selector, remembered for the day so staff pick it once. due = Counter(zone -> shops due now)."""
    counts = Counter(zone_map.values())
    due = due or Counter()
    options = [z for z in VISIT_ZONE_NAMES if counts.get(z) and not z.startswith("🚫")]
    if not options:
        return None
    mem = st.session_state.get("visit_zone_today")
    if st.session_state.get(key) not in options:
        st.session_state[key] = mem if mem in options else options[0]
    zone = st.selectbox("🗺️ តំបន់របស់ខ្ញុំថ្ងៃនេះ", options, key=key, format_func=lambda z: f"{_km(z)}  ({counts.get(z, 0)} ហាង" + (f" · ត្រូវចុះ {due[z]}" if due.get(z) else "") + ")")
    st.session_state["visit_zone_today"] = zone
    return zone


def _visit_map_link(customer, registry, store=None, auto=None):
    pin = _visit_pin(customer, registry, store, auto if auto is not None else {})
    if pin:
        return f"https://www.google.com/maps/dir/?api=1&destination={pin[0]},{pin[1]}&travelmode=driving", True
    return "https://www.google.com/maps/search/?api=1&query=" + urllib.parse.quote(f"{customer} Phnom Penh"), False


def _visit_zone_evidence(n, registry, store, auto):
    """What the shop's location / name say, ignoring Admin: (zone, why)."""
    pin = _visit_pin(n, registry, store, auto)
    if pin:
        z, khan = _visit_zone_from_gps(*pin)
        return (z or VISIT_ZONE_OUTSIDE), (f"location: ខណ្ឌ{khan}" if z else "location outside Phnom Penh")
    z, note = _visit_zone_auto_info(n)
    return z, ("name" + (f" ({note})" if note else ""))


def _visit_override_audit(names):
    """Admin zones that disagree with the shop's own location or name (e.g. saved by mistake)."""
    df = _visit_shop_settings()
    if df.empty:
        return pd.DataFrame()
    registry, store = _visit_registry(), _visit_pin_store()
    try:
        auto = _visit_candidates_for(names, registry)[1]
    except Exception:
        auto = {}
    latest = df.sort_values("_dt").groupby(df["Customer"].map(norm_name)).tail(1)
    rows = []
    for _, r in latest.iterrows():
        k = norm_name(r["Customer"])
        if k not in names or r["Zone"] not in VISIT_ZONE_NAMES:
            continue
        ez, why = _visit_zone_evidence(names[k], registry, store, auto)
        if ez.startswith("❓") or ez == r["Zone"]:
            continue
        rows.append({"Remove": True, "Customer": names[k], "Admin zone": _km(r["Zone"]), "Shop says": _km(ez),
                     "Because of": why, "Saved": str(r["Date"])[:16], "By": r["By"]})
    return pd.DataFrame(rows)


def _visit_override_cleanup(names):
    bad = _visit_override_audit(names)
    if bad.empty:
        return
    with st.expander(f"🧹 {len(bad)} Admin zones disagree with the shop's own location / name — check them", expanded=True):
        st.caption("Admin's choice always wins, so a zone saved by mistake sends staff to the wrong area. Ticked rows are "
                   "removed: the shop then uses its location or name again. Untick any Admin zone that is really correct.")
        ver = st.session_state.get("_vz_ver", 0)
        ed = st.data_editor(bad, hide_index=True, use_container_width=True, key=f"vz_clean_{ver}",
                            disabled=[c for c in bad.columns if c != "Remove"],
                            column_config={"Remove": st.column_config.CheckboxColumn("Remove")})
        pick = set(ed.loc[ed["Remove"].fillna(False).astype(bool), "Customer"].map(norm_name))
        if st.button(f"🧹 Remove {len(pick)} Admin zone(s)", type="primary", disabled=not pick, key="vz_clean_btn"):
            def _drop(df, pick=pick):
                return df[~df["Customer"].map(norm_name).isin(pick)].drop(columns=[c for c in ("_dt",) if c in df])
            try:
                modify_csv(VISIT_ZONE_FILE, VISIT_SET_COLS, _drop)
                audit("visit zones cleaned", f"{len(pick)} removed")
                st.session_state["flash"] = f"Removed {len(pick)} Admin zone(s)"
                st.session_state["_vz_ver"] = ver + 1
                st.session_state.pop("_visit_zone_cache", None)
                _frag_rerun()
            except Exception as e:
                st.error("មិនអាចរក្សាទុកបានទេ: " + str(e)[:150])


def _visit_zones_admin(names, visits):
    st.markdown("#### 🗺️ Zones & shop types")
    _visit_override_cleanup(names)
    st.caption("Zone comes from the shop's real location (📍 nearest khan) when it has one, otherwise from its name (🔤). "
               "Change the **Zone** or **Type** cell for any shop "
               "that is wrong or ❓ not set, then press Save. Your choice always wins over the guess.")
    over = _visit_zone_overrides()
    last = {}
    if not visits.empty:
        v = visits.assign(Key=visits["Customer"].map(norm_name))
        last = v.groupby("Key")["_dt"].max().to_dict()
    tmap = _visit_type_map(names)
    info = _visit_zone_info(names)
    rows = [{"Customer": n, "Guess": info.get(k, (None, ""))[1] + " → " + str(_km(info.get(k, (_visit_zone_auto(n), ""))[0])),
             "Zone": over.get(k) or info.get(k, (_visit_zone_auto(n), ""))[0],
             "Type": tmap.get(k, VISIT_TYPE_OTHER), "Set by admin": k in over,
             "Last visit": f"{last[k]:%d %b}" if k in last else "never"} for k, n in names.items()]
    frame = pd.DataFrame(rows).sort_values(["Zone", "Customer"]).reset_index(drop=True)
    summary = frame.groupby("Zone").agg(Shops=("Customer", "size"),
                                         **{"Visited ever": ("Last visit", lambda s: int((s != "never").sum()))}).reset_index()
    summary["Days to visit all (3/day)"] = (summary["Shops"] / VISIT_DAILY_TARGET).apply(math.ceil)
    _si_show(summary)
    f1, f2 = st.columns([2, 1])
    q = f1.text_input("🔎 Find shop", key="vz_q", max_chars=60)
    only = f2.selectbox("Show", ["All zones"] + VISIT_ZONE_NAMES, key="vz_only")
    view = frame
    if only != "All zones":
        view = view[view["Zone"].eq(only)]
    if q.strip():
        view = view[view["Customer"].str.contains(q.strip(), case=False, regex=False)]
    ver = st.session_state.get("_vz_ver", 0)               # new editor after each save / filter change: old edits never
    ekey = f"vz_editor_{ver}_{abs(hash((only, q.strip()))) % 10**8}"   # move onto other rows
    edited = st.data_editor(view, hide_index=True, use_container_width=True, key=ekey,
                            disabled=["Customer", "Guess", "Set by admin", "Last visit"],
                            column_config={"Zone": st.column_config.SelectboxColumn("Zone", options=VISIT_ZONE_NAMES, required=True),
                                           "Type": st.column_config.SelectboxColumn("Type", options=VISIT_TYPE_NAMES, required=True)},
                            height=min(520, 60 + 35 * max(1, len(view))))
    before = view.set_index("Customer")
    after = edited.set_index("Customer")
    diff = [(c, before.at[c, "Zone"], after.at[c, "Zone"], before.at[c, "Type"], after.at[c, "Type"])
            for c in after.index if c in before.index and
            (after.at[c, "Zone"] != before.at[c, "Zone"] or after.at[c, "Type"] != before.at[c, "Type"])]
    changed = pd.DataFrame([{"Customer": c, "Zone": z1, "Type": t1} for c, _z0, z1, _t0, t1 in diff])
    if diff:
        st.markdown("**You are about to save:**")
        st.markdown("\n".join(f"- **{c}**: {_km(z0)} → **{_km(z1)}**" + (f" · {_km(t0)} → **{_km(t1)}**" if t0 != t1 else "")
                               for c, z0, z1, t0, t1 in diff))
    if st.button(f"💾 Save {len(changed)} change(s)", type="primary", disabled=changed.empty, key="vz_save"):
        who, at = current_user() or "-", now_str()

        def _apply(df):
            df = df[df["Customer"].map(norm_name).isin(set(changed["Customer"].map(norm_name))) == False].copy()
            add = pd.DataFrame({"Date": at, "Customer": changed["Customer"], "Zone": changed["Zone"], "By": who,
                                "Type": changed["Type"]})
            return pd.concat([df.drop(columns=[c for c in ("_dt",) if c in df]), add], ignore_index=True)
        try:
            modify_csv(VISIT_ZONE_FILE, VISIT_SET_COLS, _apply)
            audit("visit zones", f"{len(changed)} changed")
            st.session_state["flash"] = f"Saved {len(changed)} zone change(s)"
            st.session_state["_vz_ver"] = ver + 1
            st.session_state.pop("_visit_zone_cache", None)
            _frag_rerun()
        except Exception as e:
            st.error("មិនអាចរក្សាទុកបានទេ: " + str(e)[:150])


# ---------- shop types, size & visit frequency ----------
VISIT_SETTINGS_FILE = os.path.join(DATA_DIR, "visit_settings.json")
VISIT_WORK_DAYS = 26                      # working days per month, for the capacity check
VISIT_SETTINGS_DEFAULT = {"big_pcs": 1000, "medium_pcs": 400, "big_days": 30, "medium_days": 90, "small_days": 180,
                          "staff": 1}
VISIT_TYPES = {     # type -> (words in the name, extra checks for that type)
    "☕ Coffee shop": (["COFFEE", "CAFE", "CAFÉ", "COFF", "កាហ្វេ", "TEA", "តែ"],
                      ["Buns visible at the counter", "Steamer / microwave working", "Menu or poster shows our buns",
                       "Shop staff know how to heat buns"]),
    "⛽ Gas station": (["TOTAL", "CALTEX", "PTT", "TELA", "តេលា", "SOKIMEX", "STATION"],
                      ["Fridge at the front, easy to see", "Price tag shown", "Our buns not hidden by competitors",
                       "Poster / sign outside"]),
    "🛒 Mart / shop": (["MART", "ម៉ាត", "STORE", "SHOP", "MALL", "MINI", "ផ្សារទំនើប", "TOYS", "AEON", "MAXVALU",
                      "SUPERMARKET", "LUCKY", "CHIP MONG", "RETAIL", "7-ELEVEN", "7 ELEVEN", "CIRCLE K", "STAR MART"],
                     ["Fridge at the front, easy to see", "Price tag shown", "Our buns not hidden by competitors",
                      "Fridge / shelf full enough"]),
    "🏫 School / canteen": (["សាលា", "វិទ្យាល័យ", "SCHOOL", "កង់ទីន", "CANTEEN", "សាកលវិទ្យាល័យ", "UNIVERSITY"],
                          ["Fridge near the canteen", "Enough stock for break time", "Price fits students",
                           "Buns kept away from sun / dust"]),
    "🏛️ Office / ministry / hospital": (["ក្រសួង", "មន្ទីរ", "អគ្គ", "ពេទ្យ", "HOSPITAL", "OFFICE"],
                                       ["Delivery time fits break time", "Steamer / microwave working",
                                        "Display clean"]),
    "🥖 Bakery / food shop": (["នំបុ័ង", "BAKERY", "RESTAURANT", "ភោជនីយ", "នំបញ្ចុក", "នំបញ្ខុក", "អាហារ", "ចុងភៅ"],
                             ["Display clean", "Price tag shown", "Our buns placed well"]),
    "🏪 Market stall": (["ផ្សារ", "MARKET"],
                       ["Covered from sun / dust", "Steamer working", "Price sign shown"]),
}
VISIT_TYPE_OTHER = "📦 Other"
VISIT_TYPE_NAMES = list(VISIT_TYPES) + [VISIT_TYPE_OTHER]
VISIT_TYPE_CHECKS = {**{t: c for t, (_w, c) in VISIT_TYPES.items()}, VISIT_TYPE_OTHER: ["Display clean", "Price tag shown"]}
VISIT_SET_COLS = ["Date", "Customer", "Zone", "By", "Type"]
VISIT_PHOTO_MAX_AGE_H = 0                 # 0 = no limit: photos may come from the gallery (check-in is the proof)


def _visit_settings():
    out = dict(VISIT_SETTINGS_DEFAULT)
    try:
        if USE_DROPBOX:
            pull(VISIT_SETTINGS_FILE, max_age=300)
        if os.path.exists(VISIT_SETTINGS_FILE):
            with open(VISIT_SETTINGS_FILE, encoding="utf-8") as f:
                saved = json.load(f)
            out.update({k: int(v) for k, v in saved.items() if k in out})
    except Exception:
        pass
    return out


def _visit_settings_save(values):
    with _sync_state()["lock"], file_lock(VISIT_SETTINGS_FILE):
        if USE_DROPBOX:
            try:
                pull(VISIT_SETTINGS_FILE, force=True)
            except Exception:
                pass
        _write_atomic(VISIT_SETTINGS_FILE, json.dumps(values, indent=2).encode("utf-8"))
        if USE_DROPBOX:
            push(VISIT_SETTINGS_FILE)


def _visit_type_auto(name):
    t = unicodedata.normalize("NFC", str(name)).upper().replace("​", "")
    for typ, (words, _c) in VISIT_TYPES.items():
        if any(w.upper() in t for w in words):
            return typ
    return VISIT_TYPE_OTHER


def _visit_size(pcs28, cfg):
    """-> (size label, visit every N days)."""
    if pcs28 is None or pd.isna(pcs28) or pcs28 <= 0:
        return "💤 No orders (28 d)", None
    if pcs28 >= cfg["big_pcs"]:
        return "🟢 Big", cfg["big_days"]
    if pcs28 >= cfg["medium_pcs"]:
        return "🟡 Medium", cfg["medium_days"]
    return "⚪ Small", cfg["small_days"]


def _visit_photo_taken_at(data):
    """When the phone camera took the photo (EXIF), or None when the photo carries no date."""
    try:
        from PIL import Image
        exif = Image.open(io.BytesIO(data)).getexif()
        raw = exif.get_ifd(0x8769).get(36867) or exif.get(306)
        return datetime.strptime(str(raw).strip()[:19], "%Y:%m:%d %H:%M:%S") if raw else None
    except Exception:
        return None


def _visit_test_mode():
    return current_role() == "admin" and bool(st.session_state.get("visit_test_mode"))


def _visits_path():
    """Real visit log, or the practice log while Admin has 🧪 Test mode on."""
    return VISITS_TEST_FILE if _visit_test_mode() else VISITS_FILE


def _visit_read():
    try:
        return read_raw(_visits_path(), VISIT_COLS, max_age=60)
    except Exception as e:
        st.warning("Visit log could not be read: " + str(e)[:150])
        return pd.DataFrame(columns=VISIT_COLS + ["_dt"])


def _haversine_m(lat1, lon1, lat2, lon2):
    r = 6371000.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = p2 - p1, math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(min(1.0, math.sqrt(a)))


# ---------- shop map pins saved by staff (used when Customer Map has no pin, or the pin was wrong) ----------
VISIT_PIN_COLS = ["Date", "Customer", "Lat", "Lon", "Accuracy m", "Source", "By", "Status", "Note"]
VISIT_PIN_MAX_ACC = 80            # metres: a GPS fix worse than this is not good enough to save as a shop location


def _visit_registry():
    """Customer Map registry, reused for 5 minutes inside Shop Visits (it is big and rarely changes)."""
    hit = st.session_state.get("_visit_registry_cache")
    if hit and time.time() - hit[0] < 300:
        return hit[1]
    try:
        reg = load_map_registry()
    except Exception:
        reg = {"records": {}, "bindings": {}}
    st.session_state["_visit_registry_cache"] = (time.time(), reg)
    return reg


def _visit_pin_store():
    """{key: {...}} newest active pin saved by staff per shop."""
    try:
        df = read_raw(VISIT_PIN_FILE, VISIT_PIN_COLS, max_age=120)
    except Exception:
        return {}
    out = {}
    for _, r in df[df["Status"].eq("Active")].sort_values("_dt").iterrows():
        k = norm_name(r["Customer"])
        try:
            out[k] = {"lat": float(r["Lat"]), "lon": float(r["Lon"]), "acc": r["Accuracy m"], "source": r["Source"],
                      "by": r["By"], "date": r["Date"]}
        except Exception:
            continue
    return out


def _visit_match_key(s):
    """Name key that ignores spacing, punctuation, zero-width marks and the ្ដ / ្ត spelling difference."""
    t = unicodedata.normalize("NFC", str(s)).lower()
    t = re.sub(r"[​‌‍﻿]", "", t).replace("្ដ", "្ត")
    return re.sub(r"[\s.,()\-_/'\"]+", "", t)


def _visit_registry_pins(registry):
    """Every usable Customer Map pin: list of (location id, map name, lat, lon, province)."""
    out = []
    for rec in registry.get("records", {}).values():
        a = map_record_analysis(rec)
        if a.get("Map status") == "Ready pin":
            out.append((rec["id"], rec["customer"], float(a["Latitude"]), float(a["Longitude"]), rec.get("province", "")))
    return out


def _grams(key):
    k = f"  {key} "
    return {k[i:i + 3] for i in range(len(k) - 2)}


def _gram_index(keys):
    """3-letter piece -> set of positions. Lets fuzzy matching skip names that share almost nothing."""
    idx = {}
    for i, k in enumerate(keys):
        for g in _grams(k):
            idx.setdefault(g, set()).add(i)
    return idx


def _gram_shortlist(key, idx, min_share=0.3):
    """Positions sharing at least min_share of key's 3-letter pieces (the only ones worth a full comparison)."""
    gs = _grams(key)
    if not gs:
        return []
    hits = Counter()
    for g in gs:
        for i in idx.get(g, ()):
            hits[i] += 1
    need = max(1, int(len(gs) * min_share))
    return [i for i, c in hits.items() if c >= need]


@st.cache_data(show_spinner=False, max_entries=8)
def _visit_pin_candidates(name_items, pin_items):
    """{key: [(score, location id, map name, lat, lon), ...best 3]} and {key: candidate} for the safe automatic links.
    Safe = same name after cleaning, or ≥ 90% alike and clearly better than the next pin."""
    import difflib
    pins = [(pid, pname, lat, lon, _visit_match_key(pname)) for pid, pname, lat, lon, _p in pin_items]
    gidx = _gram_index([p[4] for p in pins])
    cands, auto, claimed = {}, {}, Counter()
    for k, name in name_items:
        nk = _visit_match_key(name)
        if len(nk) < 3:
            continue
        scored = []
        for j in _gram_shortlist(nk, gidx, 0.25):
            pid, pname, lat, lon, pk = pins[j]
            sm = difflib.SequenceMatcher(None, nk, pk)
            if sm.real_quick_ratio() < 0.5 or sm.quick_ratio() < 0.5:
                continue
            r = sm.ratio()
            if len(pk) >= 4 and (nk.startswith(pk) or pk.startswith(nk)):
                r = max(r, 0.86)                      # "LY MEY" vs "LY MEY បឹងស្នោរ"
            if pk == nk:
                r = 1.0
            if r >= 0.6:
                scored.append((round(r, 3), pid, pname, lat, lon))
        scored.sort(reverse=True)
        if scored:
            cands[k] = scored[:3]
            best = scored[0][0]
            second = scored[1][0] if len(scored) > 1 else 0
            if best == 1.0 or (best >= 0.9 and best - second >= 0.08):
                auto[k] = scored[0]
                claimed[scored[0][1]] += 1
    auto = {k: c for k, c in auto.items() if claimed[c[1]] == 1}      # one pin can't belong to two shops
    return cands, auto


def _visit_candidates_for(names, registry):
    """Fuzzy pin suggestions. Remembered on the registry object, so repeated clicks cost nothing."""
    items = tuple(sorted(names.items()))
    memo = registry.setdefault("_cand_memo", {}) if isinstance(registry, dict) else {}
    key = (hash(items), len(registry.get("records", {})) if isinstance(registry, dict) else 0)
    if key in memo:
        return memo[key]
    pins = registry.get("_pins_tuple") if isinstance(registry, dict) else None
    if pins is None:
        pins = tuple(_visit_registry_pins(registry))
        if isinstance(registry, dict):
            registry["_pins_tuple"] = pins
    out = _visit_pin_candidates(items, pins)
    if len(memo) > 16:
        memo.clear()
    memo[key] = out
    return out


def _visit_pin_info(customer, registry=None, store=None, auto=None):
    """(lat, lon, where it came from) or None. A pin saved at the shop by staff is newer than the Customer Map, so it wins."""
    store = _visit_pin_store() if store is None else store
    k = norm_name(customer)
    if k in store:
        p = store[k]
        src = str(p["source"])
        where = ("saved at the shop" if src.startswith("GPS") else
                 "from 📍 Customer Map, confirmed" if src.startswith("Customer Map") else "saved from a Google Maps link")
        return p["lat"], p["lon"], f"{where} by {p['by']} on {str(p['date'])[:10]}" + (" (pin moved)" if "moved" in str(p["source"]) else "")
    try:
        registry = registry if registry is not None else _visit_registry()
        m = customer_map_match(customer, registry)
        lat, lon = m.get("Latitude"), m.get("Longitude")
        if lat is not None and lon is not None and math.isfinite(float(lat)) and math.isfinite(float(lon)):
            return float(lat), float(lon), "from 📍 Customer Map"
        nv = (st.session_state.get("_visit_new", {}) or {}).get(k)
        if nv and nv.get("lat") is not None:
            return nv["lat"], nv["lon"], f"from the leads report map link (sold {nv['date']:%d %b})"
        if auto is None:
            auto = _visit_candidates_for({k: customer}, registry)[1]
        if k in auto:
            c = auto[k]
            return c[3], c[4], f"from 📍 Customer Map (spelled “{c[2]}” there)"
    except Exception:
        pass
    return None


def _visit_pin_save(customer, lat, lon, acc, source, note="-"):
    if not (10 <= lat <= 15 and 102 <= lon <= 108):
        raise ValueError("this location is outside Cambodia")
    append_row(VISIT_PIN_FILE, {"Date": now_str(), "Customer": customer, "Lat": f"{lat:.6f}", "Lon": f"{lon:.6f}",
                                "Accuracy m": "-" if acc in (None, "") else f"{float(acc):.0f}", "Source": source,
                                "By": current_user() or "-", "Status": "Active", "Note": note or "-"})
    audit("shop pin saved", f"{customer} | {lat:.5f},{lon:.5f} | {source}")


def _visit_pin(customer, registry=None, store=None, auto=None):
    """(lat, lon) of the shop, or None."""
    info = _visit_pin_info(customer, registry, store, auto)
    return (info[0], info[1]) if info else None


def _visit_location_check(gps, pin):
    """-> (label, distance m or None)."""
    if not gps:
        return "❓ No GPS", None
    if not pin:
        return "📍 GPS saved (shop has no map pin)", None
    d = _haversine_m(gps["lat"], gps["lon"], pin[0], pin[1])
    slack = min(float(gps.get("acc") or 0), 300.0)
    if d <= VISIT_AT_SHOP_M + slack:
        return "✅ At shop", d
    return f"⚠️ {d / 1000:.1f} km from shop" if d >= 1000 else f"⚠️ {d:.0f} m from shop", d


def _visit_apply_gps(lat, lon, acc, ms, mode, cust, navigate=True):
    """Use one phone location: check in, or save / move the shop pin. navigate=True only before any widget is drawn."""
    age = time.time() - ms / 1000.0
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        raise ValueError("bad coordinates")
    if age > VISIT_GPS_MAX_AGE_S or age < -120:
        st.session_state["visit_gps_error"] = "Check-in ចាស់ពេក។ សូមចុច 📍 Check-in ម្តងទៀតនៅហាង។"
    elif mode in ("pin", "move") and acc > VISIT_PIN_MAX_ACC:
        st.session_state["visit_gps_error"] = (f"GPS មិនទាន់ច្បាស់គ្រប់គ្រាន់ (±{acc:.0f} m ត្រូវការ ±{VISIT_PIN_MAX_ACC} m ឬតិចជាងនេះ)។ "
                                               "សូមឈរនៅមុខទ្វារហាង រង់ចាំ 20 វិនាទី ហើយចុចម្តងទៀត។")
    else:
        if mode in ("pin", "move") and cust:
            note = "first location of this shop" if mode == "pin" else "staff moved the pin: old pin was wrong"
            _visit_pin_save(cust, lat, lon, acc, "GPS at shop" if mode == "pin" else "GPS at shop (moved)", note)
            st.session_state["flash"] = "📍 បានរក្សាទុកទីតាំងហាង"
            st.session_state.pop("_visit_registry_cache", None)
        st.session_state["visit_gps"] = {"lat": lat, "lon": lon, "acc": acc, "at": now_str(), "customer": cust}
    if navigate:
        st.session_state["main_section"] = "🏪 Shop Visits"
        st.session_state["visit_view"] = "📝 New visit"
        if cust:
            st.session_state["visit_customer"] = cust
            st.session_state["visit_zone_force"] = True


def _visit_read_gps_params():
    """Backup path: the check-in button reloads the page with ?vgps=lat,lon,acc,ms&vcust=...; keep it, then clean the URL."""
    try:
        qp = st.query_params
        raw = qp.get("vgps")
        if not raw:
            return
        lat, lon, acc, ms = (float(x) for x in str(raw).split(","))
        _visit_apply_gps(lat, lon, acc, ms, str(qp.get("vmode") or "checkin"), str(qp.get("vcust") or ""), navigate=True)
    except Exception:
        st.session_state["visit_gps_error"] = "មិនអាចអានទីតាំងបានទេ។ សូមចុច 📍 Check-in ម្តងទៀត។"
    finally:
        for k in ("vgps", "vcust", "vgpserr", "vmode"):
            try:
                if k in st.query_params:
                    del st.query_params[k]
            except Exception:
                pass


VISIT_GPS_BRIDGE = "vgps_bridge"


def _visit_gps_bridge():
    """Hidden box the check-in button writes the phone location into: Shop Visits redraws, no page reload."""
    n = st.session_state.get("_vgps_n", 0)
    st.markdown(f"""<style>div[data-testid="stTextInput"]:has(input[aria-label="{VISIT_GPS_BRIDGE}"])
        {{position:absolute;left:-9999px;top:0;width:1px;height:1px;overflow:hidden;opacity:0}}</style>""", unsafe_allow_html=True)
    raw = st.text_input(VISIT_GPS_BRIDGE, key=f"vgps_bridge_{n}", label_visibility="collapsed")
    if not raw:
        return
    st.session_state["_vgps_n"] = n + 1                    # next time a fresh, empty box
    try:
        v = json.loads(raw)
        _visit_apply_gps(float(v["lat"]), float(v["lon"]), float(v["acc"]), float(v["ms"]), str(v.get("mode", "checkin")),
                         str(v.get("cust", "")), navigate=False)
        if v.get("cust"):
            st.session_state["visit_customer"] = str(v["cust"])
    except Exception:
        st.session_state["visit_gps_error"] = "មិនអាចអានទីតាំងបានទេ។ សូមចុច 📍 Check-in ម្តងទៀត។"
    _frag_rerun()


def _visit_checkin_button(customer, mode="checkin", text="📍 Check-in នៅហាងនេះ", color="#B3261E"):
    """Asks the phone for its location, takes the first one that is good enough (or the best within 8 s),
    then hands it to the app without reloading the page. mode: checkin | pin | move."""
    cust = json.dumps(customer)
    text = html.escape(text)
    good = 60 if mode == "checkin" else VISIT_PIN_MAX_ACC
    st.components.v1.html(f"""
<style>
button{{width:100%;padding:13px 14px;border-radius:12px;border:0;background:{color};color:#fff;font:600 16px Inter,system-ui,sans-serif;cursor:pointer}}
button:disabled{{opacity:.7}} #m{{font:13px system-ui,sans-serif;color:#6B7280;margin-top:6px}}
</style>
<button id="b">{text}</button><div id="m">សូមអនុញ្ញាតទីតាំង (Location) ពេលទូរស័ព្ទសួរ។</div>
<script>
const b=document.getElementById('b'), m=document.getElementById('m');
const GOOD={good}, MAXWAIT=8000, CUST={cust}, MODE='{mode}';
function deliver(p){{
  const v={{lat:+p.coords.latitude.toFixed(6), lon:+p.coords.longitude.toFixed(6), acc:Math.round(p.coords.accuracy),
           ms:Date.now(), mode:MODE, cust:CUST}};
  m.textContent='✅ រកឃើញទីតាំង (±'+v.acc+' m)។ កំពុងរក្សាទុក…';
  try {{
    const doc=window.parent.document;
    const el=doc.querySelector('input[aria-label="{VISIT_GPS_BRIDGE}"]');
    if(!el) throw 'no box';
    const set=Object.getOwnPropertyDescriptor(window.parent.HTMLInputElement.prototype,'value').set;
    set.call(el, JSON.stringify(v));
    el.dispatchEvent(new Event('input',{{bubbles:true}}));
    ['keydown','keypress','keyup'].forEach(t=>el.dispatchEvent(new KeyboardEvent(t,{{key:'Enter',code:'Enter',keyCode:13,which:13,bubbles:true}})));
    el.dispatchEvent(new Event('blur',{{bubbles:true}})); el.dispatchEvent(new FocusEvent('focusout',{{bubbles:true}}));
  }} catch(e) {{                                   // backup: reload the page with the location in the address
    const u=new URL(window.parent.location.href);
    u.searchParams.set('vgps',[v.lat,v.lon,v.acc,v.ms].join(','));
    u.searchParams.set('vcust',CUST); u.searchParams.set('vmode',MODE);
    window.parent.location.href=u.toString();
  }}
}}
b.onclick=function(){{
  const nav=(window.parent&&window.parent.navigator&&window.parent.navigator.geolocation)?window.parent.navigator.geolocation:navigator.geolocation;
  if(!nav){{m.textContent='ទូរស័ព្ទ / browser នេះគ្មាន GPS។';return;}}
  b.disabled=true; m.textContent='កំពុងរកទីតាំង…';
  let best=null, done=false, id=null;
  const finish=function(){{ if(done) return; done=true; if(id!==null) nav.clearWatch(id);
      if(best) deliver(best); else {{ b.disabled=false; m.textContent='មិនទាន់មានសញ្ញា GPS។ សូមចេញមកខាងក្រៅ ហើយចុចម្តងទៀត។'; }} }};
  id=nav.watchPosition(function(p){{
      if(!best || p.coords.accuracy < best.coords.accuracy) best=p;
      m.textContent='កំពុងរកទីតាំង… ±'+Math.round(best.coords.accuracy)+' m';
      if(best.coords.accuracy <= GOOD) finish();
  }}, function(e){{ if(e.code===1){{ done=true; b.disabled=false; m.textContent='ទីតាំងត្រូវបានបិទ។ សូមបើក Location សម្រាប់គេហទំព័រនេះក្នុង Settings របស់ browser។'; }} }},
  {{enableHighAccuracy:true, maximumAge:20000, timeout:MAXWAIT}});
  setTimeout(finish, MAXWAIT);
}};
</script>""", height=86)


def _visit_photo_prepare(data, stamp_lines):
    """Smaller JPEG (max 1280 px) with a time/staff/GPS stamp, so photos are light on mobile data and hard to reuse."""
    from PIL import Image, ImageDraw, ImageOps
    img = Image.open(io.BytesIO(data))
    img = ImageOps.exif_transpose(img).convert("RGB")
    img.thumbnail((1280, 1280))
    draw = ImageDraw.Draw(img)
    text = "\n".join(stamp_lines)
    try:
        from PIL import ImageFont
        font = ImageFont.load_default(size=max(14, img.width // 45))
    except Exception:
        font = None
    box = draw.multiline_textbbox((0, 0), text, font=font)
    w, h = box[2] - box[0], box[3] - box[1]
    draw.rectangle([0, img.height - h - 16, w + 20, img.height], fill=(0, 0, 0))
    draw.multiline_text((10, img.height - h - 9), text, fill=(255, 255, 255), font=font)
    out = io.BytesIO()
    img.save(out, "JPEG", quality=72, optimize=True)
    return out.getvalue()


def _visit_photo_path(name):
    if name.startswith("T"):                                 # practice photos from 🧪 Test mode
        return f"{VISIT_PHOTO_DIR}/TEST/{name}"
    month = name[1:7] if name.startswith("V") else "misc"     # V202610…
    return f"{VISIT_PHOTO_DIR}/{month[:4]}-{month[4:6]}/{name}"


def _visit_photo_save(name, data):
    rel = _visit_photo_path(name)
    if USE_DROPBOX:
        import dropbox
        _dbx().files_upload(data, f"{DROPBOX_FOLDER}/{rel}", mode=dropbox.files.WriteMode.overwrite, mute=True)
    else:
        full = os.path.join(DATA_DIR, rel)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        _write_atomic(full, data)


@st.cache_data(show_spinner=False, max_entries=80, ttl=3600)
def _visit_photo_load(name):
    rel = _visit_photo_path(name)
    if USE_DROPBOX:
        _md, res = _dbx().files_download(f"{DROPBOX_FOLDER}/{rel}")
        return res.content
    with open(os.path.join(DATA_DIR, rel), "rb") as f:
        return f.read()


def _visit_customer_stats():
    """Cached wrapper: the sales calculation is heavy, so it is reused for 3 minutes or until a file changes."""
    def _mt(path):
        try:
            return os.stat(path).st_mtime_ns
        except Exception:
            return 0
    try:
        _snap, _src, path, _err = current_snapshot()
    except Exception:
        path = None
    sig = (str(path), _mt(path) if path else 0, _mt(LEADS_FILE), str(today_kh()), int(time.time() // 180))
    hit = st.session_state.get("_visit_stats_cache")
    if hit and hit[0] == sig:
        st.session_state["_visit_daily"], st.session_state["_visit_new"] = hit[2], hit[3]
        return hit[1]
    out = _visit_customer_stats_compute()
    st.session_state["_visit_stats_cache"] = (sig, out, st.session_state.get("_visit_daily", pd.DataFrame()),
                                              st.session_state.get("_visit_new", {}))
    return out


def _visit_customer_stats_compute():
    """Per customer: last order, pcs last 28 days vs the 28 before, usual gap. Uses the same data as Sales Insights."""
    try:
        snap, _src, _path, _err = current_snapshot()
        if not snap:
            return pd.DataFrame(), {}, {}
        daily, _df, _codes = _si_prepare(snap)
        if daily.empty:
            names = {norm_name(n): n for n in snap.get("customers", [])}
            amap = areas_lookup(snap)
            areas = {k: AREA_LABEL.get(amap.get(k, "Unknown"), AREA_LABEL["Unknown"]) for k in names}
        else:
            names, areas = _si_names_areas(snap, daily)
    except Exception:
        return pd.DataFrame(), {}, {}
    # Shop visits are for Phnom Penh shops only.
    names = {k: n for k, n in names.items()
             if areas.get(k) == VISIT_AREA and str(n).strip().upper() not in SI_IGNORE_NAMES}
    areas = {k: a for k, a in areas.items() if k in names}
    try:                                   # new customers from the leads report (even before they are in the Master List)
        new = {k: v for k, v in _lead_active(_lead_read(), _lead_master_index(snap)).items() if v["pp"]}
    except Exception:
        new = {}
    st.session_state["_visit_new"] = new
    for k, v in new.items():
        if k not in names:
            names[k], areas[k] = v["name"], VISIT_AREA
    if daily.empty:
        st.session_state["_visit_daily"] = pd.DataFrame()
        return pd.DataFrame(), names, areas
    daily = daily[daily["Key"].isin(names)]
    st.session_state["_visit_daily"] = daily[["Key", "D", "Pcs", "Sales"]]
    today = pd.Timestamp(today_kh())
    d = daily[daily["D"] <= today]
    last28 = d[d["D"] > today - pd.Timedelta(days=28)].groupby("Key")["Pcs"].sum()
    prev28 = d[(d["D"] <= today - pd.Timedelta(days=28)) & (d["D"] > today - pd.Timedelta(days=56))].groupby("Key")["Pcs"].sum()
    g = d.sort_values("D").groupby("Key")
    stats = pd.DataFrame({"Last order": g["D"].max(), "Order days": g["D"].nunique(),
                          "Usual gap": g["D"].apply(lambda s: s.diff().dt.days.median())})
    stats["Pcs 28d"] = last28.reindex(stats.index).fillna(0)
    stats["Pcs prev 28d"] = prev28.reindex(stats.index).fillna(0)
    stats["Trend %"] = ((stats["Pcs 28d"] - stats["Pcs prev 28d"]) / stats["Pcs prev 28d"].where(stats["Pcs prev 28d"] > 0) * 100).round(0)
    stats["Days since order"] = (today - stats["Last order"]).dt.days
    return stats, names, areas


def _visit_trend_text(pct):
    if pct is None or pd.isna(pct):
        return "ថ្មី / ទិន្នន័យមិនទាន់គ្រប់"
    return f"{'⬆️' if pct >= 10 else ('⬇️' if pct <= -10 else '➡️')} {pct:+.0f}% (២៨ ថ្ងៃចុងក្រោយ ធៀបនឹង ២៨ ថ្ងៃមុន)"


def _visit_route(visits, stats, names, areas, zone_map=None, zone=None, cfg=None):
    """Shops of the zone, most important first. Each shop is due again after N days, N set by its size."""
    cfg = cfg or _visit_settings()
    today = pd.Timestamp(today_kh())
    last_visit = {}
    open_prob = Counter()
    if not visits.empty:
        v = visits.copy()
        v["Key"] = v["Customer"].map(norm_name)
        last_visit = v.groupby("Key")["_dt"].max().to_dict()
        open_prob = Counter(v.loc[v["Status"].eq("Open"), "Key"])
    keys = {k for k in names if not str((zone_map or {}).get(k, "")).startswith("🚫")}     # shops outside Phnom Penh are not visited
    if zone:
        keys = {k for k in keys if (zone_map or {}).get(k) == zone}
    new = st.session_state.get("_visit_new", {}) or {}
    rows = []
    for k in keys:
        s = stats.loc[k] if (not stats.empty and k in stats.index) else None
        pcs28 = float(s["Pcs 28d"]) if s is not None and pd.notna(s["Pcs 28d"]) else 0.0
        size, every = _visit_size(pcs28, cfg)
        score, why = 0, []
        lv = last_visit.get(k)
        days_v = (today - pd.Timestamp(lv).normalize()).days if lv is not None and pd.notna(lv) else None
        if open_prob.get(k):
            score += 6; why.append(f"🔴 បញ្ហាមិនទាន់ដោះស្រាយ {open_prob[k]}")
        nv = new.get(k)
        first_visit = bool(nv) and not (lv is not None and pd.notna(lv) and pd.Timestamp(lv) >= nv["date"])
        if first_visit:
            age = (today - nv["date"]).days
            score += 8 + (3 if age > LEAD_FIRST_VISIT_DAYS else 0) + min(age // 7, 3)
            why.append(f"🆕 អតិថិជនថ្មី លក់ថ្ងៃ {nv['date']:%d %b} — ចុះលើកដំបូង" + (f" ({age} ថ្ងៃ យឺត)" if age > LEAD_FIRST_VISIT_DAYS else ""))
        if every is None:
            due_in = 0 if first_visit else None
            if not open_prob.get(k) and not first_visit:
                continue                                   # no orders and no problem: not on the visit plan
        elif days_v is None:
            due_in = 0
            score += 3; why.append("🆕 មិនធ្លាប់ចុះ")
        else:
            due_in = every - days_v
            if due_in <= 0:
                score += 3 + min(-due_in // 7, 3)
                why.append(f"📅 ដល់ពេលចុះ (រៀងរាល់ {every} ថ្ងៃ)" + (f" · យឺត {-due_in} ថ្ងៃ" if due_in < 0 else ""))
            else:
                score -= 6
        if s is not None:
            if pd.notna(s["Trend %"]) and s["Trend %"] <= -20:
                score += 3; why.append(f"⬇️ ការលក់ {s['Trend %']:+.0f}%")
            gap = s["Usual gap"]
            if pd.notna(gap) and gap > 0 and s["Days since order"] > 2 * gap and s["Order days"] >= 3:
                score += 2; why.append(f"⏰ មិនបញ្ជាទិញ {int(s['Days since order'])} ថ្ងៃ (ធម្មតា {gap:.0f})")
        if size.startswith("🟢"):
            score += 1
        if due_in is not None and due_in > 0 and not why:
            why.append(f"ចុះលើកក្រោយក្នុង {due_in} ថ្ងៃ")
        rows.append({"Priority": score, "Customer": names.get(k, k), "Area": (zone_map or {}).get(k, areas.get(k, "")),
                     "Size": size, "Every (days)": every, "Due in (days)": due_in,
                     "Why visit": " · ".join(why),
                     "Last visit": "never" if days_v is None else f"{days_v} d ago",
                     "Pcs 28 days": int(pcs28), "Trend %": s["Trend %"] if s is not None else None})
    out = pd.DataFrame(rows)
    if out.empty:
        return out
    return out.sort_values(["Priority", "Pcs 28 days"], ascending=False).reset_index(drop=True)


def _visit_is_due(route):
    """Rows that need a visit now: due/late, never visited, or with an open problem."""
    if route.empty:
        return route.iloc[0:0]
    return route[route["Due in (days)"].fillna(0).le(0) | route["Why visit"].str.contains("🔴")]


def _visit_new_form(visits, stats, names):
    user = current_user() or "-"
    _visit_gps_bridge()
    fast = st.session_state.get("visit_ctx")
    if (_visit_phone_mode() and fast and fast.get("customer") == st.session_state.get("visit_customer")
            and fast["key"] in st.session_state.get("visit_draft", {}) and st.session_state.get("visit_gps")
            and int(st.session_state["visit_draft"][fast["key"]].get("_step", 0)) > 0):
        _vf_phone_wizard(fast)        # only the current step is drawn: no shop list, map or Dropbox checks
        return
    _visit_progress(visits, user)
    zone_map = _visit_zone_map(names)
    pre = st.session_state.get("visit_customer")
    if st.session_state.pop("visit_zone_force", False) and pre and norm_name(pre) in zone_map:
        st.session_state["visit_zone_form"] = zone_map[norm_name(pre)]       # "Start ▶" opens the shop's own zone (once)
    zone = _visit_zone_picker(zone_map, "visit_zone_form")
    pool = {k: n for k, n in names.items() if zone is None or zone_map.get(k) == zone}
    customers = sorted(set(pool.values()), key=lambda x: str(x).upper())
    if not customers:
        st.info("រកមិនឃើញអតិថិជននៅភ្នំពេញទេ។ សូមពិនិត្យតំបន់ក្នុង Master List ឬកំណត់ខេត្តក្នុង 📍 Customer Map។")
        return
    err = st.session_state.pop("visit_gps_error", None)
    if err:
        st.error(err)
    pre = st.session_state.get("visit_customer")
    idx = customers.index(pre) if pre in customers else None
    customer = st.selectbox("1️⃣ តើអ្នកកំពុងចុះហាងណា? (ភ្នំពេញ)", customers, index=idx, key="visit_customer_box",
                            placeholder="វាយឈ្មោះហាង…")
    if not customer:
        st.caption("គន្លឹះ: បើក **📋 ផែនការថ្ងៃនេះ** ដើម្បីមើលហាងសំខាន់ៗ 3 ក្នុងតំបន់របស់អ្នក។")
        return
    st.session_state["visit_customer"] = customer
    key = norm_name(customer)
    registry = _visit_registry()
    try:
        cands, auto = _visit_candidates_for(names, registry or {"records": {}, "bindings": {}})
    except Exception:
        cands, auto = {}, {}
    pin_info = _visit_pin_info(customer, registry, None, auto)
    pin = (pin_info[0], pin_info[1]) if pin_info else None

    # ---- shop card
    s = stats.loc[key] if (not stats.empty and key in stats.index) else None
    past = visits[visits["Customer"].map(norm_name) == key].sort_values("_dt", ascending=False) if not visits.empty else visits
    with st.container(border=True):
        c1, c2, c3 = st.columns(3)
        c1.metric("បញ្ជាទិញចុងក្រោយ", f"{s['Last order']:%d %b}" if s is not None else "—",
                  f"{int(s['Days since order'])} ថ្ងៃមុន" if s is not None else None, delta_color="off")
        c2.metric("ចំនួននំ ២៨ ថ្ងៃចុងក្រោយ", f"{int(s['Pcs 28d']):,}" if s is not None else "—",
                  f"{s['Trend %']:+.0f}%" if s is not None and pd.notna(s["Trend %"]) else None)
        c3.metric("ចុះហាងចុងក្រោយ", f"{past.iloc[0]['_dt']:%d %b}" if len(past) else "មិនធ្លាប់",
                  past.iloc[0]["Staff"] if len(past) else None, delta_color="off")
        open_p = past[past["Status"].eq("Open")] if len(past) else past
        for _, r in open_p.head(3).iterrows():
            st.warning(f"បញ្ហាមិនទាន់ដោះស្រាយ ថ្ងៃ {r['_dt']:%d %b} ({r['Staff']}): {_km_list(r['Problems'])} — {r['Notes']}")
        if len(past) and str(past.iloc[0]["Notes"]) not in ("-", ""):
            st.caption(f"កំណត់ចំណាំពេលចុះហាងចុងក្រោយ: {past.iloc[0]['Notes']}")

    # ---- 2. shop location (must be real) + check-in
    gps = st.session_state.get("visit_gps")
    if gps and norm_name(gps.get("customer", "")) != key:
        gps = None
    test = _visit_test_mode()
    if test:
        st.markdown("**2️⃣ Check-in** · 🧪 Test mode")
        if not pin:
            st.caption("បុគ្គលិកពិតត្រូវរក្សាទុកទីតាំងហាងនេះជាមុនសិន។ ក្នុង Test mode ប្រើទីតាំងសាកល្បង។")
            pin = (11.5564, 104.9282)
            pin_info = (pin[0], pin[1], "🧪 ទីតាំងសាកល្បង (Test mode)")
        if not gps:
            t1, t2 = st.columns(2)
            if t1.button("🧪 សាកល្បង៖ ខ្ញុំនៅហាង", key="visit_test_here", use_container_width=True, type="primary"):
                st.session_state["visit_gps"] = {"lat": pin[0] + 0.0002, "lon": pin[1] + 0.0002, "acc": 12,
                                                 "at": (now_kh() - timedelta(minutes=12)).strftime("%Y-%m-%d %H:%M:%S"), "customer": customer}
                _frag_rerun()
            if t2.button("🧪 សាកល្បង៖ ខ្ញុំនៅឆ្ងាយ 3 km", key="visit_test_far", use_container_width=True):
                st.session_state["visit_gps"] = {"lat": pin[0] + 0.027, "lon": pin[1], "acc": 15,
                                                 "at": (now_kh() - timedelta(minutes=2)).strftime("%Y-%m-%d %H:%M:%S"), "customer": customer}
                _frag_rerun()
            st.caption("ឬប្រើប៊ូតុង Check-in ពិតខាងក្រោម ដើម្បីសាកល្បង GPS ទូរស័ព្ទ។")
            _visit_checkin_button(customer)
            return
    if not test and not pin:
        st.markdown("**2️⃣ រក្សាទុកទីតាំងហាងនេះជាមុនសិន**")
        st.error("📍 ហាងនេះមិនទាន់មានទីតាំងលើផែនទី។ ត្រូវរក្សាទុកទីតាំងជាមុនសិន ទើបអាចចាប់ផ្តើមចុះហាងបាន។")
        options = cands.get(key, [])
        if options:
            st.markdown("**តើហាងនេះជាទីតាំងមួយក្នុងចំណោមទីតាំងទាំងនេះពី 📍 Customer Map ឬទេ?** (ឈ្មោះនៅទីនោះសរសេរខុសគ្នាបន្តិច)")
            for i, (score, pid, pname, lat, lon) in enumerate(options):
                with st.container(border=True):
                    o1, o2, o3 = st.columns([3, 1, 1])
                    o1.markdown(f"**{pname}**  \n<span style='color:#6B7280'>{score * 100:.0f}% ឈ្មោះដូចគ្នា</span>", unsafe_allow_html=True)
                    o2.link_button("🗺️ មើល", f"https://www.google.com/maps?q={lat},{lon}", use_container_width=True)
                    if o3.button("✅ គឺហាងនេះ", key=f"visit_cand_{i}", use_container_width=True):
                        try:
                            _visit_pin_save(customer, lat, lon, None, "Customer Map pin (confirmed)", f"map name: {pname}"[:150])
                            st.session_state["flash"] = "📍 បានភ្ជាប់ទីតាំងផែនទីទៅហាងនេះ"
                            _frag_rerun()
                        except Exception as e:
                            st.error("មិនអាចរក្សាទុកបានទេ: " + str(e)[:150])
            st.markdown("**មិនមែនទាំងអស់នេះទេ? រក្សាទុកទីតាំងពិត:**")
        _visit_checkin_button(customer, "pin", "📍 ខ្ញុំនៅហាង — រក្សាទុក GPS ជាទីតាំងហាង", "#2E7D4F")
        st.caption(f"សូមឈរនៅមុខទ្វារហាង។ GPS ទូរស័ព្ទត្រូវច្បាស់ក្នុង ±{VISIT_PIN_MAX_ACC} m។ វានឹង Check-in ឱ្យអ្នកផងដែរ។")
        with st.expander("…ឬបិទភ្ជាប់ Google Maps link របស់ហាង"):
            link = st.text_input("Google Maps link (បើកហាងក្នុង Google Maps → Share → Copy link)", key="visit_pin_link",
                                 max_chars=600, placeholder="https://maps.app.goo.gl/…")
            if st.button("💾 រក្សាទុកទីតាំងពី link", key="visit_pin_link_save", disabled=not link.strip()):
                try:
                    with st.spinner("កំពុងបើក link…"):
                        final = resolve_map_link(link.strip())
                    info = analyse_map_link(final)
                    if info.get("Map status") != "Ready pin":
                        raise ValueError("link នេះគ្មានទីតាំងច្បាស់ទេ។ សូមដាក់ pin លើហាង ហើយ Share វា")
                    _visit_pin_save(customer, float(info["Latitude"]), float(info["Longitude"]), None, "Google Maps link", link.strip()[:150])
                    st.session_state["flash"] = "📍 បានរក្សាទុកទីតាំងហាងពី link"
                    _frag_rerun()
                except Exception as e:
                    if "no usable destination" in str(e):
                        st.error("link នេះមិនមានទីតាំងហាងទេ។ នៅក្នុង Google Maps ចុចឱ្យជាប់លើហាង (ដាក់ pin ក្រហម) → Share → Copy link "
                                 "ហើយបិទភ្ជាប់ម្តងទៀត — ឬឈរនៅមុខហាង ហើយចុច 📍 ខ្ញុំនៅហាង។")
                    else:
                        st.error("មិនអាចប្រើ link នេះបានទេ: " + str(e)[:160])
        return
    if test:
        gps = st.session_state.get("visit_gps")
    directions = f"https://www.google.com/maps/dir/?api=1&destination={pin[0]},{pin[1]}&travelmode=driving"
    m1, m2 = st.columns([3, 1])
    m1.caption(f"📍 ទីតាំងហាង {pin_info[2]}")
    m2.link_button("🧭 ផ្លូវទៅហាង", directions, use_container_width=True)
    if not test:
        st.markdown("**2️⃣ Check-in ពេលមកដល់ហាង**")
    if not gps:
        _visit_checkin_button(customer)
        st.caption("ទម្រង់ចុះហាងនឹងបើកបន្ទាប់ពី Check-in។")
        return
    label, dist = _visit_location_check(gps, pin)
    (st.success if label.startswith("✅") else st.warning)(
        f"{_km_loc(label)} · Check-in ម៉ោង {gps['at'][11:16]} · GPS ±{gps['acc']:.0f} m")
    b1, b2 = st.columns(2)
    if b1.button("↻ Check-in ម្តងទៀត", key="visit_recheck", use_container_width=True):
        st.session_state.pop("visit_gps", None)
        _frag_rerun()
    if not label.startswith("✅") and not test:
        with b2:
            with st.popover("📌 ទីតាំងលើផែនទីខុស", use_container_width=True):
                st.caption("ប្រើតែពេលអ្នកកំពុងឈរនៅហាងពិត ហើយទីតាំងដែលបានរក្សាទុកចង្អុលទៅកន្លែងផ្សេង។ "
                           "Admin នឹងឃើញថាអ្នកបានផ្លាស់ទីតាំង។")
                _visit_checkin_button(customer, "move", "📌 ផ្លាស់ទីតាំងហាងមកកន្លែងខ្ញុំឈរ", "#B3261E")

    # ---- 3. the visit form (desktop: one page · phone: step by step)
    shop_type = _visit_type_map({key: customer}).get(key, VISIT_TYPE_OTHER)
    nv = (st.session_state.get("_visit_new", {}) or {}).get(key)
    is_first_visit = bool(nv) and not (len(past) and past.iloc[0]["_dt"] >= nv["date"])
    _visit_redo_notice(visits, user, customer)
    if is_first_visit:
        st.info(f"🆕 **ចុះហាងលើកដំបូងក្រោយលក់ថ្ងៃ {nv['date']:%d %b}។** ពិនិត្យថាទូទឹកកកបានដំឡើង បិទស្ទីគ័ររួច "
                "ហើយម្ចាស់ហាងដឹងពីរបៀបលក់ និងកំដៅនំ។" + ("" if nv["in_master"] else
                " ⚠️ ហាងនេះមិនទាន់មានក្នុង Master List — សូមប្រាប់ Admin ឱ្យបន្ថែម។"))
    cfg = _visit_settings()
    size, _every = _visit_size(float(s["Pcs 28d"]) if s is not None else 0, cfg)
    type_checks = list(VISIT_TYPE_CHECKS.get(shop_type, VISIT_TYPE_CHECKS[VISIT_TYPE_OTHER]))
    if is_first_visit:
        type_checks = LEAD_FIRST_VISIT_CHECKS + type_checks
    app_pct = s["Trend %"] if s is not None else None
    ctx = {"customer": customer, "key": key, "pin": pin, "user": user, "zone": zone_map.get(key, VISIT_ZONE_NOT_SET),
           "shop_type": shop_type, "size": size, "app_pct": app_pct, "type_checks": type_checks}
    st.session_state["visit_ctx"] = ctx
    if not _visit_phone_mode():
        st.caption(f"ប្រភេទហាង: **{_km(shop_type)}** · ទំហំ: **{_km(size)}**" + (" — Admin អាចប្តូរប្រភេទក្នុង ⚙️ ហាង និងតំបន់។" if current_role() == "admin" else ""))
        with st.form("visit_form", clear_on_submit=False):
            a = {}
            st.markdown("**3️⃣ រូបថត** — ត្រូវមានរូបមុខហាង")
            a.update(_vf_photos_arrive({}, False))
            a.update(_vf_photos_after({}, False))
            st.markdown(f"**4️⃣ ពិនិត្យហាង** · {_km(shop_type)}")
            a.update(_vf_check({}, ctx, False))
            st.markdown("**5️⃣ ការលក់**")
            a.update(_vf_sales({}, ctx, False))
            st.markdown("**6️⃣ បញ្ហា និងសំណើ**")
            a.update(_vf_problems({}, False))
            submitted = st.form_submit_button("✅ រក្សាទុករបាយការណ៍", type="primary", use_container_width=True)
        if submitted:
            err = _vf_validate(a)
            if err:
                st.error(err)
            else:
                _vf_save(a, ctx)
        return
    _vf_phone_wizard(ctx)


# ---------- visit form sections (shared by desktop and phone) ----------
class _Shot:
    """A photo kept in memory between phone steps: shrunk once (≈1280 px), with a small thumbnail for the screen
    and the time the camera took it (shown in reports)."""
    def __init__(self, data, name="photo.jpg", thumb=None, taken=None):
        self.data, self.name, self.thumb, self.taken = data, name, thumb, taken

    def getvalue(self):
        return self.data


def _vf_keep(f):
    if f is None:
        return None
    raw = f.getvalue()
    taken = _visit_photo_taken_at(raw)
    try:
        from PIL import Image, ImageOps
        img = ImageOps.exif_transpose(Image.open(io.BytesIO(raw))).convert("RGB")
        img.thumbnail((1280, 1280))
        big = io.BytesIO()
        img.save(big, "JPEG", quality=80, optimize=True)
        img.thumbnail((240, 240))
        small = io.BytesIO()
        img.save(small, "JPEG", quality=70)
        return _Shot(big.getvalue(), getattr(f, "name", "photo.jpg"), small.getvalue(), taken)
    except Exception:
        return _Shot(raw, getattr(f, "name", "photo.jpg"), None, taken)


def _vf_thumb(shot):
    return shot.thumb if getattr(shot, "thumb", None) else shot.getvalue()


def _vf_thumb_row(items):
    """Small thumbnails side by side (stays in one row on a phone)."""
    import base64
    cells = "".join(
        f"<figure style='margin:0;text-align:center'><img src='data:image/jpeg;base64,{base64.b64encode(_vf_thumb(f)).decode()}' "
        f"style='height:84px;border-radius:10px;border:1px solid #E6E0D6'><figcaption style='font-size:12px;color:#6B7280'>{_e(lab)}</figcaption></figure>"
        for lab, f in items)
    st.markdown(f"<div style='display:flex;gap:8px;flex-wrap:wrap;margin:4px 0 8px'>{cells}</div>", unsafe_allow_html=True)


def _frag_rerun():
    """Redraw only Shop Visits when possible (much faster than the whole app)."""
    if _in_fragment():
        st.rerun(scope="fragment")
    st.rerun()  # keep


def _vf_idx(options, value, default=0):
    return options.index(value) if value in options else default


VF_FRIDGE = ["Clean & cold", "Dirty", "Not cold", "Broken", "No fridge"]
VF_FIFO = ["Good", "Needs fixing", "Fixed today"]
VF_STICKER = ["Good", "Old / faded", "Missing"]
VF_SAYS = ["⬆️ Up", "➡️ Same", "⬇️ Down"]
VF_PRIORITY = ["Low", "Normal", "Urgent"]
VF_SAT = ["😠 1", "🙁 2", "😐 3", "🙂 4", "😍 5"]
VF_IMG = ["jpg", "jpeg", "png", "webp"]


VF_PHOTO_LABEL = {"front": "📸 មុខហាង", "before": "🅱️ BEFORE", "after": "🅰️ AFTER"}


def _vf_photo_slot(d, k, label, wkey, help_=None):
    """Phone: show the photo already taken, or a big upload box for it. Updates the draft directly."""
    if d.get(k) is not None:
        _vf_thumb_row([(f"{VF_PHOTO_LABEL.get(k, label)} ✅", d[k])])
        st.button("↻ ថតម្តងទៀត", key=f"{wkey}_redo", on_click=lambda: d.__setitem__(k, None))
        return
    f = st.file_uploader(label, type=VF_IMG, key=wkey, help=help_ or "ចុច → ថតរូប ឬជ្រើសពី Gallery")
    if f is not None:
        d[k] = _vf_keep(f)
        st.caption(f"✅ បានរក្សាទុក {VF_PHOTO_LABEL.get(k, label)}")


def _vf_photo_status(d):
    need = ["front"] + (["before", "after"] if (_vf_fixes(d) or d.get("before") is not None or d.get("after") is not None) else [])
    return " · ".join(f"{VF_PHOTO_LABEL[k]} {'✅' if d.get(k) is not None else '❌'}" for k in need)


def _vf_photos_arrive(d, phone):
    if phone:
        st.caption("បន្ថែមរូប 2: ថតដោយកាមេរ៉ា ឬជ្រើសពី Gallery។")
        st.markdown("**1 · 📸 រូបមុខហាង** (ចាំបាច់)")
        _vf_photo_slot(d, "front", "📸 រូបមុខហាង", "vf_front_up", "ចុច → ថតរូប ឬជ្រើសពី Gallery")
        st.markdown("**2 · 🅱️ BEFORE: ទូទឹកកក / កន្លែងតាំង ពេលមកដល់** (ត្រូវការ បើអ្នកនឹងជួសជុលអ្វីមួយ)")
        _vf_photo_slot(d, "before", "🅱️ រូប BEFORE", "vf_before")
        return {}
    front = st.file_uploader("📸 រូបមុខហាង (ចាំបាច់)", type=VF_IMG, key="visit_cam",
                             help="ថតដោយកាមេរ៉ា ឬជ្រើសពី Gallery។")
    before = st.file_uploader("🅱️ BEFORE: ទូទឹកកក / កន្លែងតាំង ពេលមកដល់", type=VF_IMG, key="visit_before",
                              help="ត្រូវការ ពេលអ្នកជួសជុលអ្វីមួយ។")
    return {"front": front, "before": before}


def _vf_photos_after(d, phone):
    if phone:
        if d.get("before") is None and (_vf_fixes(d) or d.get("after") is not None):
            st.markdown("**🅱️ ខ្វះរូប BEFORE** — បន្ថែមនៅទីនេះ")
            _vf_photo_slot(d, "before", "🅱️ រូប BEFORE", "vf_before2")
        st.markdown("**🅰️ AFTER: កន្លែងដដែលក្រោយជួសជុល** (មុំដូច BEFORE)")
        _vf_photo_slot(d, "after", "🅰️ រូប AFTER", "vf_after")
        extra = st.file_uploader("រូបផ្សេងទៀត (មិនចាំបាច់ អតិបរមា 2)", type=VF_IMG, accept_multiple_files=True, key="vf_extra")
        if extra:
            ids = tuple(getattr(f, "file_id", f.name) for f in extra)
            if ids != d.get("_extra_ids"):
                d["extra"], d["_extra_ids"] = [_vf_keep(f) for f in extra], ids
        elif d.get("extra"):
            _vf_thumb_row([("ផ្សេងៗ", f) for f in d["extra"]])
        return {}
    after = st.file_uploader("🅰️ AFTER: កន្លែងដដែលក្រោយជួសជុល", type=VF_IMG, key="visit_after",
                             help="មុំដូច BEFORE ដើម្បីងាយមើលការផ្លាស់ប្តូរ។")
    extra = st.file_uploader("រូបផ្សេងទៀត (អតិបរមា 2)", type=VF_IMG, accept_multiple_files=True, key="visit_files")
    return {"after": after, "extra": extra or []}


def _vf_check(d, ctx, phone):
    cols = (st, st, st, st, st) if phone else (*st.columns(2), *st.columns(3))
    fridge = cols[0].radio("🧊 ទូទឹកកក", VF_FRIDGE, format_func=_km, index=_vf_idx(VF_FRIDGE, d.get("fridge")), horizontal=True, key="vf_fridge")
    fifo = cols[1].radio("🥟 ការតាំង / នំចាស់នៅខាងមុខ (FIFO)", VF_FIFO, format_func=_km, index=_vf_idx(VF_FIFO, d.get("fifo")), horizontal=True, key="vf_fifo")
    old_pcs = cols[2].number_input("នំចាស់ / ខូច ដែលរកឃើញ (pcs)", 0, 5000, int(d.get("old_pcs", 0)), 1, key="vf_old")
    sticker = cols[3].radio("🏷️ ស្ទីគ័រ", VF_STICKER, format_func=_km, index=_vf_idx(VF_STICKER, d.get("sticker")), horizontal=True, key="vf_sticker")
    changed = cols[4].number_input("ស្ទីគ័របានប្តូរថ្ងៃនេះ", 0, 100, int(d.get("changed", 0)), 1, key="vf_changed")
    fridge_fixed = st.checkbox("🧽 ខ្ញុំបានសម្អាត / រៀបទូទឹកកក ឬកន្លែងតាំងថ្ងៃនេះ", value=bool(d.get("fridge_fixed")), key="vf_ffix")
    st.caption(f"គូសធីកអ្វីដែលល្អនៅ {_km(ctx['shop_type'])}:")
    prev = d.get("checks", {})
    grid = [st] if phone else st.columns(2)
    checks = {c: grid[i % len(grid)].checkbox(_km(c), value=bool(prev.get(c)), key=f"vf_chk_{i}") for i, c in enumerate(ctx["type_checks"])}
    return {"fridge": fridge, "fifo": fifo, "old_pcs": old_pcs, "sticker": sticker, "changed": changed,
            "fridge_fixed": fridge_fixed, "checks": checks}


def _vf_sales(d, ctx, phone):
    st.caption("តាម Sale Journal: " + _visit_trend_text(ctx["app_pct"]))
    cols = (st, st, st) if phone else st.columns(3)
    says = cols[0].radio("ម្ចាស់ហាងថាការលក់", VF_SAYS, format_func=_km, index=_vf_idx(VF_SAYS, d.get("says"), 1), horizontal=True, key="vf_says")
    reason = cols[1].selectbox("មូលហេតុចម្បង", VISIT_REASONS, format_func=_km, index=_vf_idx(VISIT_REASONS, d.get("reason")), key="vf_reason")
    competitor = cols[2].text_input("ម៉ាកគូប្រជែងដែលឃើញ (បើមាន)", value=d.get("competitor", ""), max_chars=60, key="vf_comp")
    return {"says": says, "reason": reason, "competitor": competitor}


def _vf_problems(d, phone):
    problems = st.multiselect("បញ្ហាដែលរកឃើញ", VISIT_PROBLEMS, format_func=_km, default=[p for p in d.get("problems", []) if p in VISIT_PROBLEMS],
                              placeholder="គ្មាន — ទុកទទេ បើគ្រប់យ៉ាងល្អ", key="vf_probs")
    cols = (st, st, st) if phone else st.columns(3)
    priority = cols[0].radio("អាទិភាព", VF_PRIORITY, format_func=_km, index=_vf_idx(VF_PRIORITY, d.get("priority"), 1), horizontal=True, key="vf_prio")
    follow = cols[1].selectbox("អ្នកទទួលបន្ត", VISIT_FOLLOWUP, format_func=_km, index=_vf_idx(VISIT_FOLLOWUP, d.get("follow")), key="vf_follow")
    sat = cols[2].select_slider("ការពេញចិត្តរបស់ហាង", VF_SAT, value=d.get("sat", "🙂 4"), key="vf_sat")
    notes = st.text_area("កំណត់ចំណាំ (អ្វីដែលឃើញ អ្វីដែលបានធ្វើ)", value=d.get("notes", ""), max_chars=200, height=80, key="vf_notes")
    request = st.text_input("សំណើរបស់អតិថិជន (ចង់បាននំប្រភេទណាបន្ថែម ការបញ្ជាទិញបន្ទាប់ ប្រូម៉ូសិន…)", value=d.get("request", ""),
                            max_chars=150, key="vf_req")
    return {"problems": problems, "priority": priority, "follow": follow, "sat": sat, "notes": notes, "request": request}


def _vf_fixes(a):
    return [x for x, on in (("Sticker changed", (a.get("changed") or 0) > 0), ("FIFO fixed", a.get("fifo") == "Fixed today"),
                            ("Fridge/display cleaned", bool(a.get("fridge_fixed")))) if on]


def _vf_validate(a):
    """Error text, or None when the visit can be saved."""
    skipped = [n for n, k in (("🔍 ពិនិត្យ", "fridge"), ("📈 ការលក់", "says"), ("⚠️ បញ្ហា", "priority")) if k not in a]
    if skipped:
        return "សូមបើក និងបំពេញជំហានទាំងនេះជាមុនសិន: " + ", ".join(skipped) + "។"
    if a.get("front") is None:
        return "សូមបន្ថែមរូបមុខហាងជាមុនសិន។"
    if len(a.get("extra") or []) > 2:
        return "ជ្រើសរូបផ្សេងទៀតបានច្រើនបំផុត 2។"
    fixes = _vf_fixes(a)
    if fixes and (a.get("before") is None or a.get("after") is None):
        return "អ្នកបានជួសជុល (" + ", ".join(_km(x) for x in fixes) + ")។ សូមបន្ថែមទាំងរូប 🅱️ BEFORE និង 🅰️ AFTER។"
    if (a.get("before") is None) != (a.get("after") is None):
        return "សូមបន្ថែមទាំងរូប BEFORE និង AFTER ឬកុំបន្ថែមទាំងពីរ។"
    if a.get("problems") and a.get("follow") in ("-", None):
        return "អ្នកបានរាយការណ៍បញ្ហា: សូមជ្រើសអ្នកទទួលបន្ត។"
    return None                       # photos may come from the gallery: the GPS check-in proves the visit


def _vf_save(a, ctx):
    customer, key, pin, user = ctx["customer"], ctx["key"], ctx["pin"], ctx["user"]
    gps = st.session_state.get("visit_gps")
    if gps and norm_name(gps.get("customer", "")) != key:
        gps = None
    label, dist = _visit_location_check(gps, pin)
    now = now_kh()
    vid = f"{'T' if _visit_test_mode() else 'V'}{now:%Y%m%d-%H%M%S}-{pysecrets.token_hex(2)}"
    stamp = [f"{now:%Y-%m-%d %H:%M}  {user}", (f"GPS {gps['lat']:.5f},{gps['lon']:.5f} ±{gps['acc']:.0f}m" if gps else "No GPS"),
             f"{vid}  {label.encode('ascii', 'ignore').decode().strip()}"]
    names_saved = []
    with st.spinner("កំពុងរក្សាទុករូបថត…"):
        try:
            shots = [("front", a["front"])] + ([("before", a["before"]), ("after", a["after"])] if a.get("before") is not None else []) \
                + [(f"x{i}", f) for i, f in enumerate(a.get("extra") or [], start=1)]
            for role, f in shots:
                data = _visit_photo_prepare(f.getvalue(), stamp + [role.upper()])
                name = f"{vid}_{role}.jpg"
                _visit_photo_save(name, data)
                names_saved.append(name)
        except Exception as e:
            st.error("មិនអាចរក្សាទុករូបថតបានទេ: " + str(e)[:150] + "។ មិនទាន់កត់ត្រាអ្វីទេ សូមព្យាយាមម្តងទៀត។")
            return
    minutes = ""
    if gps:
        try:
            minutes = max(0, round((now.replace(tzinfo=None) - datetime.strptime(gps["at"], "%Y-%m-%d %H:%M:%S")).total_seconds() / 60))
        except Exception:
            minutes = ""
    fixes, checks, app_pct = _vf_fixes(a), a.get("checks", {}), ctx["app_pct"]
    problems = a.get("problems") or []
    row = {"Date": now_str(), "VisitID": vid, "Staff": user, "Customer": customer,
           "Check-in": gps["at"] if gps else "-", "Minutes": minutes,
           "Lat": f"{gps['lat']:.6f}" if gps else "-", "Lon": f"{gps['lon']:.6f}" if gps else "-",
           "GPS accuracy m": f"{gps['acc']:.0f}" if gps else "-", "Distance m": f"{dist:.0f}" if dist is not None else "-",
           "Location check": label, "Fridge": a["fridge"], "Display FIFO": a["fifo"], "Old/damaged pcs": int(a["old_pcs"]),
           "Sticker": a["sticker"], "Stickers changed": int(a["changed"]), "Customer says sales": a["says"], "Sales reason": a["reason"],
           "Competitor": a.get("competitor") or "-", "App trend %": "-" if app_pct is None or pd.isna(app_pct) else f"{app_pct:.0f}",
           "Problems": "; ".join(p.split(" ", 1)[1] for p in problems) or "-", "Priority": a["priority"],
           "Follow-up by": a["follow"], "Notes": a.get("notes") or "-", "Customer request": a.get("request") or "-",
           "Satisfaction": a["sat"].split()[-1], "Photos": ";".join(names_saved), "Status": "Open" if problems else "No problem",
           "Fixed by": "-", "Fixed at": "-", "Fix note": "-", "Zone": ctx["zone"],
           "Shop type": ctx["shop_type"], "Checks": "; ".join(f"{c}: {'OK' if ok else 'NO'}" for c, ok in checks.items()),
           "Check score %": round(100 * sum(checks.values()) / max(1, len(checks))), "Size": ctx["size"],
           "Fix done": "; ".join(fixes) or "-", "Review": "-", "Reviewed by": "-", "Reviewed at": "-", "Review note": "-"}
    try:
        append_row(_visits_path(), row)
    except Exception as e:
        st.error("មិនអាចរក្សាទុករបាយការណ៍បានទេ: " + str(e)[:160] + "។ ចម្លើយរបស់អ្នកនៅដដែល សូមចុចរក្សាទុកម្តងទៀត។")
        return
    audit("shop visit" + (" (TEST)" if _visit_test_mode() else ""), f"{customer} | {label} | {row['Problems']}")
    _vf_draft_delete()
    for k in [k for k in list(st.session_state) if str(k).startswith(("visit_gps", "visit_customer", "visit_cam", "visit_files",
                                                                     "visit_before", "visit_after", "vf_", "visit_draft", "visit_ctx"))]:
        st.session_state.pop(k, None)
    st.session_state["flash"] = f"បានរក្សាទុករបាយការណ៍: {customer}"
    _frag_rerun()


VF_STEPS = ["📸 មកដល់", "🔍 ពិនិត្យ", "🛠️ ក្រោយជួសជុល", "📈 ការលក់", "⚠️ បញ្ហា", "✅ រក្សាទុក"]


def _vf_phone_wizard(ctx):
    """One block of questions per screen, big buttons, answers kept when going back."""
    drafts = st.session_state.setdefault("visit_draft", {})
    d = drafts.setdefault(ctx["key"], {"_step": 0})
    step = int(d.get("_step", 0))
    st.progress((step + 1) / len(VF_STEPS), text=f"ជំហាន {step + 1} នៃ {len(VF_STEPS)} · {VF_STEPS[step]} · {ctx['customer']}")
    with st.container(border=True):
        if step == 0:
            ans = _vf_photos_arrive(d, True)
        elif step == 1:
            st.caption(f"{_km(ctx['shop_type'])} · {_km(ctx['size'])}")
            ans = _vf_check(d, ctx, True)
        elif step == 2:
            fixes = _vf_fixes(d)
            if fixes:
                st.info("អ្នកបានជួសជុល: **" + ", ".join(_km(x) for x in fixes) + "** → ថតរូប 🅰️ AFTER មុំដូច BEFORE។")
            else:
                st.caption("មិនបានជួសជុលអ្វីទេ? អាចរំលងរូប AFTER បាន (ត្រូវការតែពេលមានរូប BEFORE)។")
            ans = _vf_photos_after(d, True)
        elif step == 3:
            ans = _vf_sales(d, ctx, True)
        elif step == 4:
            ans = _vf_problems(d, True)
        else:
            ans = {}
            _vf_summary(d, ctx)
    d.update(ans)
    err_here = None
    if step == 0 and d.get("front") is None:
        err_here = "សូមបន្ថែមរូបមុខហាងដើម្បីបន្ត។"
    if step == 2 and _vf_fixes(d) and (d.get("before") is None or d.get("after") is None):
        err_here = "ដោយសារអ្នកបានជួសជុល សូមបន្ថែមរូប BEFORE (ជំហាន 1) និង AFTER។"
    if step == 4 and d.get("problems") and d.get("follow") in ("-", None):
        err_here = "សូមជ្រើសអ្នកទទួលបន្តបញ្ហានេះ។"
    last = step == len(VF_STEPS) - 1
    if not last:
        if st.button(f"បន្ទាប់: {VF_STEPS[step + 1]} ➡️", key=f"vf_next_{step}", type="primary", use_container_width=True):
            if err_here:
                st.error(err_here)
            else:
                d["_step"] = step + 1
                _vf_draft_save()
                _frag_rerun()
    elif st.button("✅ រក្សាទុករបាយការណ៍", key="vf_save", type="primary", use_container_width=True):
        err = _vf_validate(d)
        if err:
            st.error(err)
        else:
            _vf_save(d, ctx)
    if step > 0 and st.button(f"⬅️ ថយក្រោយ: {VF_STEPS[step - 1]}", key=f"vf_back_{step}", use_container_width=True):
        d["_step"] = step - 1
        _frag_rerun()
    with st.expander("លោតទៅជំហាន / បោះបង់ការចុះហាងនេះ"):
        go = st.radio("Step", VF_STEPS, index=step, horizontal=True, key=f"vf_jump_{step}", label_visibility="collapsed")
        if go != VF_STEPS[step]:
            d["_step"] = VF_STEPS.index(go)
            _frag_rerun()
        if st.button("✖ បោះបង់ការចុះហាងនេះ (ចម្លើយនឹងត្រូវលុប)", key=f"vf_cancel_{step}"):
            st.session_state.get("visit_draft", {}).pop(ctx["key"], None)
            for k in ("visit_gps", "visit_customer", "visit_customer_box", "visit_ctx"):
                st.session_state.pop(k, None)
            _vf_draft_delete()
            _frag_rerun()
    _vf_draft_save()


VF_DRAFT_KEEP_H = 8          # an unfinished visit is kept this many hours


def _vf_draft_path(user):
    safe = re.sub(r"[^a-z0-9._-]", "_", str(user or "-").lower())[:40]
    return os.path.join(CACHE_DIR, "visit_drafts", safe + ".pkl")


def _vf_plain(v):
    """Draft -> plain Python (no app classes), so it can be read back after the app restarts."""
    if isinstance(v, _Shot):
        return {"__shot__": True, "data": v.data, "name": v.name, "thumb": v.thumb, "taken": v.taken}
    if isinstance(v, dict):
        return {k: _vf_plain(x) for k, x in v.items()}
    if isinstance(v, (list, tuple)):
        return type(v)(_vf_plain(x) for x in v)
    return v


def _vf_unplain(v):
    if isinstance(v, dict) and v.get("__shot__"):
        return _Shot(v["data"], v.get("name", "photo.jpg"), v.get("thumb"), v.get("taken"))
    if isinstance(v, dict):
        return {k: _vf_unplain(x) for k, x in v.items()}
    if isinstance(v, (list, tuple)):
        return type(v)(_vf_unplain(x) for x in v)
    return v


def _vf_draft_save():
    """Keep the unfinished visit on the server, so a phone that slept or reconnected gets it back."""
    user = current_user()
    if not user or not st.session_state.get("visit_draft"):
        return
    try:
        path = _vf_draft_path(user)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        blob = pickle.dumps({"saved": time.time(), "draft": _vf_plain(st.session_state.get("visit_draft")),
                             "ctx": _vf_plain(st.session_state.get("visit_ctx")), "customer": st.session_state.get("visit_customer"),
                             "gps": st.session_state.get("visit_gps"), "test": bool(st.session_state.get("visit_test_mode"))})
        _write_atomic(path, blob)
    except Exception:
        pass


def _vf_draft_restore():
    """Bring back an unfinished visit after the phone reconnected. Returns True when something was restored."""
    user = current_user()
    if not user or st.session_state.get("visit_draft"):
        return False
    path = _vf_draft_path(user)
    try:
        if not os.path.exists(path) or time.time() - os.path.getmtime(path) > VF_DRAFT_KEEP_H * 3600:
            return False
        with open(path, "rb") as f:
            data = pickle.load(f)
        if data.get("test") and current_role() != "admin":
            return False
        st.session_state["visit_draft"] = _vf_unplain(data.get("draft") or {})
        if data.get("ctx"):
            st.session_state["visit_ctx"] = _vf_unplain(data["ctx"])
        for k, sk in (("customer", "visit_customer"), ("gps", "visit_gps")):
            if data.get(k):
                st.session_state[sk] = data[k]
        if data.get("test"):
            st.session_state["visit_test_mode"] = True
        return bool(st.session_state["visit_draft"])
    except Exception:
        return False


def _vf_draft_delete():
    try:
        os.remove(_vf_draft_path(current_user()))
    except Exception:
        pass


def _vf_summary(d, ctx):
    fixes = _vf_fixes(d)
    checks = d.get("checks", {})
    photos = [n for n, k in (("front", "front"), ("before", "before"), ("after", "after")) if d.get(k) is not None]
    st.markdown(f"**{ctx['customer']}**")
    thumbs = [(VF_PHOTO_LABEL[k], d[k]) for k in ("front", "before", "after") if d.get(k) is not None] + \
             [("ផ្សេងៗ", f) for f in (d.get("extra") or [])]
    if thumbs:
        _vf_thumb_row(thumbs)
    st.markdown(f"- 📸 រូបថត: **{_vf_photo_status(d)}**" + (f" + ផ្សេងទៀត {len(d.get('extra') or [])}" if d.get("extra") else "") + "\n"
                f"- 🧊 ទូទឹកកក **{_km(d.get('fridge', '-'))}** · 🥟 FIFO **{_km(d.get('fifo', '-'))}** · នំចាស់ **{d.get('old_pcs', 0)}**\n"
                f"- 🏷️ ស្ទីគ័រ **{_km(d.get('sticker', '-'))}** · បានប្តូរ **{d.get('changed', 0)}**\n"
                f"- 🛠️ បានជួសជុល: **{', '.join(_km(x) for x in fixes) or 'គ្មាន'}**\n"
                f"- 📋 បញ្ជីពិនិត្យ: **ល្អ {sum(checks.values())} / {len(checks)}**\n"
                f"- 📈 ម្ចាស់ហាងថា **{_km(d.get('says', '-'))}** · {_km(d.get('reason', '-'))}\n"
                f"- ⚠️ បញ្ហា: **{', '.join(_km(p) for p in d.get('problems', [])) or 'គ្មាន'}**"
                + (f" · អ្នកទទួលបន្ត {_km(d.get('follow'))}" if d.get("problems") else "") + "\n"
                f"- 😊 ការពេញចិត្ត **{d.get('sat', '-')}** · 📝 {d.get('notes') or 'គ្មានកំណត់ចំណាំ'}")
    missing = [k for k in ("front", "before", "after") if d.get(k) is None and
               (k == "front" or _vf_fixes(d) or d.get("before") is not None or d.get("after") is not None)]
    for k in missing:
        st.warning(f"ខ្វះ {VF_PHOTO_LABEL[k]} — បន្ថែមនៅទីនេះ:")
        _vf_photo_slot(d, k, f"{VF_PHOTO_LABEL[k]}", f"vf_{k}_sum")
    err = _vf_validate(d)
    if err and not missing:
        st.error(err)
    elif not err:
        st.success("បំពេញគ្រប់ហើយ។ សូមចុច **✅ រក្សាទុករបាយការណ៍**។")


def _in_fragment():
    try:
        from streamlit.runtime.scriptrunner import get_script_run_ctx
        ctx = get_script_run_ctx()
        return bool(ctx and getattr(ctx, "current_fragment_id", None))
    except Exception:
        return False


def _visit_phone_mode():
    if "visit_phone" not in st.session_state:
        st.session_state["visit_phone"] = is_mobile()
    return bool(st.session_state.get("visit_phone"))


VISIT_PHONE_CSS = """<style>
.stButton > button, .stDownloadButton > button, .stLinkButton > a {min-height: 50px; font-size: 1.02rem; border-radius: 12px;}
div[data-testid="stCameraInput"] button {min-height: 50px;}
[data-baseweb="input"], [data-baseweb="select"] > div, [data-baseweb="textarea"] {min-height: 46px; font-size: 1rem;}
label[data-baseweb="radio"] {padding: 9px 14px; margin: 4px 6px 4px 0;}
label[data-baseweb="checkbox"] {padding: 6px 0;}
[data-testid="stProgress"] p {font-weight: 700;}
</style>"""


def _visit_report_frame(visits, start, end, staff):
    v = visits[(visits["_dt"].dt.date >= start) & (visits["_dt"].dt.date <= end)].copy()
    if staff:
        v = v[v["Staff"].isin(staff)]
    for c in ("Minutes", "Distance m", "Old/damaged pcs", "Stickers changed", "Satisfaction", "Lat", "Lon"):
        v[c] = pd.to_numeric(v[c], errors="coerce")
    return v.sort_values("_dt", ascending=False)


def _visit_report_body(visits):
    today = today_kh()
    c1, c2, c3 = st.columns([1, 1, 2])
    start = c1.date_input("ពីថ្ងៃ", today, key="vr_from")
    end = c2.date_input("ដល់ថ្ងៃ", today, key="vr_to")
    staff_all = sorted(visits["Staff"].unique()) if not visits.empty else []
    staff = c3.multiselect("Staff", staff_all, key="vr_staff", placeholder="All staff")
    v = _visit_report_frame(visits, start, end, staff)
    if v.empty:
        st.info("No visits in this period yet.")
        return
    at_shop = v["Location check"].str.startswith("✅")
    k1, k2, k3, k4 = st.columns(4)
    k1.metric("Visits", f"{len(v):,}", f"{v['Customer'].nunique()} shops", delta_color="off")
    k2.metric("Confirmed at shop", f"{at_shop.mean() * 100:.0f}%", f"{int((~at_shop).sum())} not confirmed", delta_color="off")
    k3.metric("Stickers changed", f"{int(v['Stickers changed'].fillna(0).sum()):,}")
    k4.metric("Problems still open", f"{int(v['Status'].eq('Open').sum()):,}")

    st.markdown("**👥 Staff today / in this period**")
    per = v.groupby("Staff").agg(**{"Visits": ("VisitID", "size"), "Shops": ("Customer", "nunique"),
                                   "At shop %": ("Location check", lambda s: round(s.str.startswith("✅").mean() * 100)),
                                   "Avg minutes": ("Minutes", "mean"), "First visit": ("_dt", "min"), "Last visit": ("_dt", "max"),
                                   "Stickers": ("Stickers changed", "sum"), "Problems": ("Status", lambda s: int(s.eq("Open").sum()))}).reset_index()
    per["Avg minutes"] = per["Avg minutes"].round(0)
    days = v.assign(Day=v["_dt"].dt.date, Key=v["Customer"].map(norm_name)).groupby(["Staff", "Day"])["Key"].nunique()
    per[f"Days with {VISIT_DAILY_TARGET}+ shops"] = per["Staff"].map(lambda u: f"{int((days.get(u, pd.Series(dtype=int)) >= VISIT_DAILY_TARGET).sum())} / {len(days.get(u, []))}")
    per["Zones"] = per["Staff"].map(v.groupby("Staff")["Zone"].agg(lambda s: ", ".join(sorted({str(z).split(' (')[0] for z in s if str(z) not in ('-', '')}))))
    per["First visit"] = per["First visit"].dt.strftime("%d %b %H:%M")
    per["Last visit"] = per["Last visit"].dt.strftime("%d %b %H:%M")
    _si_show(per.sort_values("Visits", ascending=False))

    pts = v.dropna(subset=["Lat", "Lon"])
    if len(pts):
        st.markdown("**🗺️ Where the check-ins were** (red = not at shop)")
        pts = pts.assign(color=pts["Location check"].map(lambda x: "#2E7D4F" if str(x).startswith("✅") else "#B3261E"))
        try:
            st.map(pts, latitude="Lat", longitude="Lon", color="color", size=60)
        except Exception:
            st.map(pts.rename(columns={"Lat": "lat", "Lon": "lon"})[["lat", "lon"]])

    st.markdown("**📈 What shops say about sales**")
    t1, t2 = st.columns(2)
    trend = v["Customer says sales"].value_counts().reindex(["⬆️ Up", "➡️ Same", "⬇️ Down"]).fillna(0).astype(int)
    t1.dataframe(trend.rename("Shops").to_frame(), use_container_width=True)
    down = v[v["Customer says sales"].eq("⬇️ Down")][["Customer", "Sales reason", "Competitor", "App trend %", "Staff"]]
    with t2:
        if len(down):
            st.caption("Shops saying ⬇️ Down")
            _si_show(down.reset_index(drop=True))
        else:
            st.caption("No shop said sales are down. 🎉")

    st.markdown("**📋 All visits**")
    show = v.assign(Time=v["_dt"].dt.strftime("%d %b %H:%M"))[
        ["Time", "Staff", "Zone", "Customer", "Location check", "Fridge", "Sticker", "Stickers changed", "Customer says sales",
         "Problems", "Status", "Notes", "Customer request", "Satisfaction"]]
    _si_show(show.reset_index(drop=True), height=min(460, 60 + 36 * len(show)))

    st.markdown("**🖼️ Photos**")
    pick = st.selectbox("Open the photos of a visit", ["-"] + [f"{r['_dt']:%d %b %H:%M} · {r['Customer']} · {r['Staff']}" for _, r in v.head(60).iterrows()],
                        key="vr_photo_pick")
    if pick != "-":
        r = v.head(60).iloc[[f"{x['_dt']:%d %b %H:%M} · {x['Customer']} · {x['Staff']}" for _, x in v.head(60).iterrows()].index(pick)]
        st.caption(f"Checks: {r.get('Checks', '-')} · Fix done: {r.get('Fix done', '-')}")
        _visit_show_photos(r["Photos"], "vr")
    if has_permission("reports"):
        try:
            _lazy_excel_download("📥 Download visits (Excel)", lambda: {"Visits": v.drop(columns=["_dt"]), "By staff": per},
                                 f"Shop_Visits_{start}_{end}.xlsx", "vr_dl")
        except Exception as e:
            st.warning(f"Could not build the Excel file: {e}")


def _visit_problems_body(visits):
    open_v = visits[visits["Status"].eq("Open")].sort_values("_dt") if not visits.empty else visits
    if open_v.empty:
        st.success("No open problems. 🎉")
        return
    f1, f2 = st.columns(2)
    who = f1.selectbox("Follow-up by", ["All"] + VISIT_FOLLOWUP[1:], key="vp_who")
    pri = f2.multiselect("Priority", ["Urgent", "Normal", "Low"], default=["Urgent", "Normal", "Low"], key="vp_pri")
    if who != "All":
        open_v = open_v[open_v["Follow-up by"].eq(who)]
    open_v = open_v[open_v["Priority"].isin(pri)]
    st.caption(f"{len(open_v)} open problems, oldest first.")
    can_fix = has_permission("edit")
    for _, r in open_v.head(40).iterrows():
        age = (pd.Timestamp(now_kh().replace(tzinfo=None)) - r["_dt"]).days
        with st.container(border=True):
            st.markdown(f"**{'🔴' if r['Priority'] == 'Urgent' else '🟠'} {r['Customer']}** · {r['Problems']}  \n"
                        f"<span style='color:#6B7280'>{r['_dt']:%d %b %H:%M} by {r['Staff']} · {age} days open · follow-up: {r['Follow-up by']}</span>",
                        unsafe_allow_html=True)
            if str(r["Notes"]) not in ("-", ""):
                st.write(r["Notes"])
            if can_fix:
                c1, c2 = st.columns([3, 1])
                note = c1.text_input("What was done", key=f"vfix_{r['VisitID']}", max_chars=120, label_visibility="collapsed",
                                     placeholder="What was done to fix it…")
                if c2.button("✅ Fixed", key=f"vfixb_{r['VisitID']}", use_container_width=True):
                    vid, by, at = r["VisitID"], current_user() or "-", now_str()

                    def _fix(df, vid=vid, by=by, at=at, note=note):
                        m = df["VisitID"].eq(vid)
                        df.loc[m, ["Status", "Fixed by", "Fixed at", "Fix note"]] = ["Fixed", by, at, safe_text(note or "-", 120)]
                        return df
                    try:
                        modify_csv(_visits_path(), VISIT_COLS, _fix)
                        audit("visit problem fixed", f"{r['Customer']} | {vid}")
                        st.session_state["flash"] = f"Marked fixed: {r['Customer']}"
                        _frag_rerun()
                    except Exception as e:
                        st.error("មិនអាចរក្សាទុកបានទេ: " + str(e)[:150])


VISIT_MIN_MINUTES = 5            # a visit shorter than this is flagged


def _visit_flags(r):
    """Reasons a manager should look closer at a submitted visit."""
    flags = []
    loc = str(r.get("Location check", ""))
    if not loc.startswith("✅"):
        flags.append("📍 មិនបានបញ្ជាក់ថានៅហាង" + (f" ({_km_loc(loc)})" if loc and loc != "-" else ""))
    mins = pd.to_numeric(r.get("Minutes"), errors="coerce")
    if pd.notna(mins) and mins < VISIT_MIN_MINUTES:
        flags.append(f"⏱️ នៅហាងតែ {int(mins)} នាទី")
    score = pd.to_numeric(r.get("Check score %"), errors="coerce")
    if pd.notna(score) and score < 50:
        flags.append(f"📋 ពិនិត្យហាងល្អតែ {int(score)}%")
    photos = [p for p in str(r.get("Photos", "")).split(";") if p and p != "-"]
    if len(photos) <= 1:
        flags.append("🖼️ មានតែរូបមុខហាង")
    if str(r.get("Fridge")) in ("Dirty", "Not cold", "Broken") and "Fridge" not in str(r.get("Fix done", "")) \
            and str(r.get("Problems")) in ("-", ""):
        flags.append(f"🧊 ទូទឹកកក “{_km(r.get('Fridge'))}” ប៉ុន្តែមិនបានរាយការណ៍បញ្ហា")
    if str(r.get("Sticker")) in ("Old / faded", "Missing") and str(r.get("Stickers changed")) in ("0", "-", ""):
        flags.append(f"🏷️ ស្ទីគ័រ “{_km(r.get('Sticker'))}” ប៉ុន្តែមិនបានប្តូរ")
    if str(r.get("Problems")) not in ("-", "") and str(r.get("Follow-up by")) in ("-", ""):
        flags.append("👤 មានបញ្ហា ប៉ុន្តែគ្មានអ្នកទទួលបន្ត")
    if str(r.get("Notes")) in ("-", ""):
        flags.append("📝 គ្មានកំណត់ចំណាំ")
    return flags


def _visit_review_state(r):
    rv = str(r.get("Review", "-"))
    return rv if rv in ("Approved", "Redo") else "To review"


def _visit_sheet(r):
    """The whole submitted form of one visit, easy to read."""
    yn = lambda ok: "✅" if ok else "❌"
    st.markdown(f"**{r['Customer']}** · {_km(r.get('Shop type', '-'))} · {_km(r.get('Size', '-'))} · {_km(r.get('Zone', '-'))}")
    st.caption(f"ដោយ **{r['Staff']}** · រក្សាទុក {r['_dt']:%d %b %Y %H:%M} · Check-in {str(r['Check-in'])[11:16] or '-'} · "
               f"{r['Minutes'] if str(r['Minutes']) not in ('', '-') else '?'} នាទី · លេខ {r['VisitID']}")
    loc = str(r["Location check"])
    (st.success if loc.startswith("✅") else st.warning)(
        f"{_km_loc(loc)} · GPS ±{r['GPS accuracy m']} m" + (f" · ឆ្ងាយពីទីតាំងហាង {r['Distance m']} m" if str(r["Distance m"]) not in ("-", "") else ""))
    if str(r["Lat"]) not in ("-", ""):
        st.link_button("🗺️ កន្លែងដែល Check-in", f"https://www.google.com/maps?q={r['Lat']},{r['Lon']}")
    c1, c2 = st.columns(2)
    with c1:
        st.markdown("**🔍 ពិនិត្យហាង**")
        st.markdown(f"- 🧊 ទូទឹកកក: **{_km(r['Fridge'])}**\n- 🥟 ការតាំង / FIFO: **{_km(r['Display FIFO'])}**\n"
                    f"- នំចាស់ / ខូច: **{r['Old/damaged pcs']} pcs**\n- 🏷️ ស្ទីគ័រ: **{_km(r['Sticker'])}** · បានប្តូរ **{r['Stickers changed']}**\n"
                    f"- 🛠️ បានជួសជុលថ្ងៃនេះ: **{_km_list(r.get('Fix done', '-'))}**")
        checks = [c.rsplit(": ", 1) for c in str(r.get("Checks", "")).split("; ") if ": " in c]
        if checks:
            st.markdown(f"**📋 បញ្ជីពិនិត្យ** (ល្អ {r.get('Check score %', '-')}%)")
            st.markdown("\n".join(f"- {yn(v == 'OK')} {_km(k)}" for k, v in checks))
    with c2:
        st.markdown("**📈 ការលក់**")
        st.markdown(f"- ម្ចាស់ហាងថា: **{_km(r['Customer says sales'])}** · មូលហេតុ: **{_km(r['Sales reason'])}**\n"
                    f"- តាម Sale Journal: **{r['App trend %']}%**\n- គូប្រជែង: **{r['Competitor']}**")
        st.markdown("**⚠️ បញ្ហា និងសំណើ**")
        st.markdown(f"- បញ្ហា: **{_km_list(r['Problems'])}**\n- អាទិភាព: **{_km(r['Priority'])}** · អ្នកទទួលបន្ត: **{_km(r['Follow-up by'])}**\n"
                    f"- ស្ថានភាព: **{_km(r['Status'])}**\n- ការពេញចិត្តរបស់ហាង: **{r['Satisfaction']} / 5**\n- សំណើ: {r['Customer request']}")
    st.markdown(f"**📝 កំណត់ចំណាំ:** {r['Notes']}")
    _visit_show_photos(r["Photos"], f"rv_{r['VisitID']}")


def _visit_review_body(visits):
    st.markdown("#### ✅ ពិនិត្យរបាយការណ៍ចុះហាង")
    st.caption("បើករបាយការណ៍នីមួយៗ ដើម្បីមើលអ្វីដែលបុគ្គលិកបានបំពេញ។ ⚑ សម្គាល់ចំណុចត្រូវពិនិត្យ។ អនុម័ត ឬបញ្ជូនត្រឡប់ "
               "with **Redo** and a note — staff see the note in their plan.")
    if visits.empty:
        st.info("មិនទាន់មានការចុះហាងទេ។")
        return
    today = today_kh()
    c1, c2, c3, c4 = st.columns([1, 1, 1, 1])
    start = c1.date_input("ពីថ្ងៃ", today - timedelta(days=6), key="rv_from")
    end = c2.date_input("ដល់ថ្ងៃ", today, key="rv_to")
    staff = c3.selectbox("បុគ្គលិក", ["All"] + sorted(visits["Staff"].unique()), key="rv_staff", format_func=_km)
    state = c4.selectbox("បង្ហាញ", ["To review", "Redo", "Approved", "All"], key="rv_state", format_func=_km)
    v = visits[(visits["_dt"].dt.date >= start) & (visits["_dt"].dt.date <= end)].copy()
    if staff != "All":
        v = v[v["Staff"].eq(staff)]
    v["_state"] = [_visit_review_state(r) for r in v.to_dict("records")]
    counts = v["_state"].value_counts()
    st.caption(f"⏳ រង់ចាំពិនិត្យ {counts.get('To review', 0)} · 🔁 ត្រូវធ្វើឡើងវិញ {counts.get('Redo', 0)} · ✅ បានអនុម័ត {counts.get('Approved', 0)}")
    if state != "All":
        v = v[v["_state"].eq(state)]
    if v.empty:
        st.success("គ្មានអ្វីទេ។ 🎉")
        return
    can = has_permission("edit")
    icon = {"To review": "⏳", "Redo": "🔁", "Approved": "✅"}
    for r in v.sort_values("_dt", ascending=False).head(40).to_dict("records"):
        flags = _visit_flags(r)
        head = (f"{icon[r['_state']]} {r['_dt']:%d %b %H:%M} · {r['Customer']} · {r['Staff']} · "
                f"{'📍✅' if str(r['Location check']).startswith('✅') else '📍⚠️'}" + (f" · ⚑ {len(flags)}" if flags else " · គ្រប់ចំណុច"))
        with st.expander(head):
            if flags:
                st.warning("**ត្រូវពិនិត្យ:** " + " · ".join(flags))
            if r["_state"] != "To review":
                st.caption(f"{icon[r['_state']]} {_km(r['_state'])} ដោយ {r.get('Reviewed by', '-')} ថ្ងៃ {str(r.get('Reviewed at', '-'))[:16]}"
                           + (f" — “{r['Review note']}”" if str(r.get("Review note", "-")) not in ("-", "") else ""))
            _visit_sheet(r)
            if can:
                st.divider()
                n1, n2, n3 = st.columns([3, 1, 1])
                note = n1.text_input("កំណត់ចំណាំទៅបុគ្គលិក", key=f"rvn_{r['VisitID']}", max_chars=150,
                                     placeholder="ឧ. ថតរូប AFTER មុំដូច BEFORE", label_visibility="collapsed")
                for col, verdict, label, kind in ((n2, "Approved", "✅ អនុម័ត", "primary"), (n3, "Redo", "🔁 ធ្វើឡើងវិញ", "secondary")):
                    if col.button(label, key=f"rv_{verdict}_{r['VisitID']}", use_container_width=True, type=kind):
                        if verdict == "Redo" and not note.strip():
                            st.error("សូមសរសេរអ្វីដែលបុគ្គលិកត្រូវធ្វើឡើងវិញ។")
                            continue
                        vid, by, at = r["VisitID"], current_user() or "-", now_str()

                        def _rev(df, vid=vid, verdict=verdict, by=by, at=at, note=note):
                            for c in ("Review", "Reviewed by", "Reviewed at", "Review note"):
                                if c not in df:
                                    df[c] = "-"
                            df.loc[df["VisitID"].eq(vid), ["Review", "Reviewed by", "Reviewed at", "Review note"]] = \
                                [verdict, by, at, safe_text(note or "-", 150)]
                            return df
                        try:
                            modify_csv(_visits_path(), VISIT_COLS, _rev)
                            audit("visit review", f"{r['Customer']} | {verdict} | {vid}")
                            st.session_state["flash"] = f"{_km(verdict)}: {r['Customer']}"
                            _frag_rerun()
                        except Exception as e:
                            st.error("មិនអាចរក្សាទុកបានទេ: " + str(e)[:150])


def _visit_redo_notice(visits, user, customer=None):
    """Staff see the visits a manager sent back."""
    if visits.empty or "Review" not in visits:
        return
    redo = visits[visits["Review"].eq("Redo") & visits["Staff"].eq(user)].sort_values("_dt", ascending=False)
    if customer is not None:
        redo = redo[redo["Customer"].map(norm_name) == norm_name(customer)]
    for r in redo.head(5).to_dict("records"):
        later = visits[(visits["Customer"].map(norm_name) == norm_name(r["Customer"])) & (visits["_dt"] > r["_dt"])]
        if later.empty:
            st.error(f"🔁 ត្រូវធ្វើឡើងវិញ **{r['Customer']}** (ចុះហាងថ្ងៃ {r['_dt']:%d %b}) — {r.get('Reviewed by', 'Admin')}: “{r.get('Review note', '')}”")


def _visit_show_photos(photos, key_prefix):
    """Shop front first, then BEFORE | AFTER side by side, then the rest."""
    files = [p for p in str(photos).split(";") if p and p != "-"]
    role = lambda n: n.rsplit("_", 1)[-1].split(".")[0]
    label = {"front": "📸 មុខហាង", "before": "🅱️ BEFORE", "after": "🅰️ AFTER"}
    order = {"front": 0, "before": 1, "after": 2}
    files.sort(key=lambda n: order.get(role(n), 3))
    pair = [f for f in files if role(f) in ("before", "after")]
    others = [f for f in files if f not in pair]

    def _img(col, name):
        try:
            col.image(_visit_photo_load(name), use_container_width=True, caption=label.get(role(name), "រូបថត"))
        except Exception as e:
            col.warning(f"{name}: {str(e)[:80]}")
    if others[:1]:
        _img(st.columns([2, 1])[0], others[0])
    if pair:
        cols = st.columns(2)
        for i, name in enumerate(pair[:2]):
            _img(cols[i], name)
    rest = others[1:]
    if rest:
        cols = st.columns(min(3, len(rest)))
        for i, name in enumerate(rest):
            _img(cols[i % len(cols)], name)


def _visit_settings_admin(route):
    st.markdown("#### 📅 How often to visit")
    cfg = _visit_settings()
    with st.form("visit_cfg"):
        c1, c2 = st.columns(2)
        big_pcs = c1.number_input("🟢 Big shop = at least this many pcs in 28 days", 100, 20000, cfg["big_pcs"], 50)
        medium_pcs = c2.number_input("🟡 Medium shop = at least this many pcs in 28 days", 1, 20000, cfg["medium_pcs"], 50)
        d1, d2, d3, d4 = st.columns(4)
        big_days = d1.number_input("Visit 🟢 Big every (days)", 7, 365, cfg["big_days"], 1)
        medium_days = d2.number_input("Visit 🟡 Medium every (days)", 7, 365, cfg["medium_days"], 1)
        small_days = d3.number_input("Visit ⚪ Small every (days)", 7, 365, cfg["small_days"], 1)
        staff_n = d4.number_input("Staff doing visits", 1, 20, cfg["staff"], 1)
        save = st.form_submit_button("💾 Save", type="primary")
    if save:
        if medium_pcs >= big_pcs:
            st.error("Medium must be smaller than Big.")
        else:
            try:
                _visit_settings_save({"big_pcs": int(big_pcs), "medium_pcs": int(medium_pcs), "big_days": int(big_days),
                                      "medium_days": int(medium_days), "small_days": int(small_days), "staff": int(staff_n)})
                audit("visit settings", f"{big_pcs}/{medium_pcs} pcs, {big_days}/{medium_days}/{small_days} days, {staff_n} staff")
                st.session_state["flash"] = "Visit frequency saved"
                _frag_rerun()
            except Exception as e:
                st.error("មិនអាចរក្សាទុកបានទេ: " + str(e)[:150])
    if not route.empty:
        sizes = route.groupby("Size").agg(Shops=("Customer", "size"), Every=("Every (days)", "first")).reset_index()
        sizes["Visits needed / month"] = (sizes["Shops"] * 30 / sizes["Every"]).round(0)
        need = int(sizes["Visits needed / month"].fillna(0).sum())
        cap = VISIT_DAILY_TARGET * VISIT_WORK_DAYS * cfg["staff"]
        _si_show(sizes.rename(columns={"Every": "Every (days)"}))
        msg = (f"Needs about **{need} visits a month**. {cfg['staff']} staff × {VISIT_DAILY_TARGET} a day × {VISIT_WORK_DAYS} days "
               f"= **{cap}**.")
        if need > cap:
            st.warning(msg + f" That is {need - cap} too many: visit Small or Medium shops less often, or do "
                             f"{math.ceil(need / VISIT_WORK_DAYS / cfg['staff'])} visits a day.")
        else:
            st.success(msg + " The plan fits. 👍")
        st.caption("Shops with no orders in 28 days are not scheduled; they appear only when they have an open problem.")


@st.cache_data(show_spinner=False, max_entries=4)
def _visit_effect(sig, _visits, _daily, window=14):
    """Bun pcs in the 14 days before vs after each visit, compared with all Phnom Penh shops in the same days."""
    visits, daily = _visits, _daily
    if visits.empty or daily.empty:
        return pd.DataFrame()
    today = pd.Timestamp(today_kh())
    tot = daily.groupby("D")["Pcs"].sum()
    by_key = {k: g.set_index("D")["Pcs"] for k, g in daily.groupby("Key")}
    rows = []
    for _, r in visits.iterrows():
        d = pd.Timestamp(r["_dt"]).normalize()
        k = norm_name(r["Customer"])
        ser = by_key.get(k, pd.Series(dtype=float))
        b0, b1, a0, a1 = d - pd.Timedelta(days=window), d - pd.Timedelta(days=1), d + pd.Timedelta(days=1), d + pd.Timedelta(days=window)
        ready = a1 <= today
        before = float(ser[(ser.index >= b0) & (ser.index <= b1)].sum())
        after = float(ser[(ser.index >= a0) & (ser.index <= min(a1, today))].sum())
        days_after = max(0, (min(a1, today) - d).days)
        tb = float(tot[(tot.index >= b0) & (tot.index <= b1)].sum())
        ta = float(tot[(tot.index >= a0) & (tot.index <= min(a1, today))].sum())
        # compare like with like while the 14 days after are not finished yet
        scale = window / days_after if days_after else None
        after_full, ta_full = (after * scale, ta * scale) if scale else (None, None)
        shop_pct = (after_full - before) / before * 100 if (scale and before > 0) else None
        all_pct = (ta_full - tb) / tb * 100 if (scale and tb > 0) else None
        actions = [a for a in str(r.get("Fix done", "-")).split("; ") if a and a != "-"]
        if str(r.get("Status")) == "Fixed":
            actions.append("Problem fixed later")
        rows.append({"Date": f"{d:%Y-%m-%d}", "Staff": r["Staff"], "Customer": r["Customer"], "Zone": r.get("Zone", "-"),
                     "Actions": ", ".join(actions) or "Visit only",
                     "Pcs 14 d before": int(before), "Pcs 14 d after": int(after),
                     "Shop change %": None if shop_pct is None else round(shop_pct),
                     "All PP shops %": None if all_pct is None else round(all_pct),
                     "Lift %": None if (shop_pct is None or all_pct is None) else round(shop_pct - all_pct),
                     "Result": "✅ 14 days done" if ready else (f"⏳ {days_after} of 14 days" if days_after else "⏳ waiting")})
    return pd.DataFrame(rows)


def _visit_effect_body(visits, daily):
    st.markdown("#### 📈 Did the visit help?")
    st.caption("For each visit: the shop's bun pcs in the 14 days **before** vs the 14 days **after**. "
               "**Lift** removes the normal ups and downs by comparing with all Phnom Penh shops in the same days: "
               "Lift +15% = this shop grew 15 points more than the market.")
    eff = _visit_effect(_si_frame_sig(visits) + _si_frame_sig(daily), visits, daily)
    if eff.empty:
        st.info("No visits yet, or no sales data.")
        return
    done = eff[eff["Result"].str.startswith("✅") & eff["Lift %"].notna()]
    k1, k2, k3 = st.columns(3)
    k1.metric("Visits with 14 days of results", f"{len(done):,}", f"{len(eff) - len(done)} still waiting", delta_color="off")
    k2.metric("Average lift", f"{done['Lift %'].mean():+.0f}%" if len(done) else "—")
    k3.metric("Shops that grew more than the market", f"{(done['Lift %'] > 0).mean() * 100:.0f}%" if len(done) else "—")
    if len(done):
        st.markdown("**By action** — which work raises sales")
        act = done.assign(Action=done["Actions"].str.split(", ")).explode("Action")
        _si_show(act.groupby("Action").agg(Visits=("Customer", "size"), **{"Avg lift %": ("Lift %", "mean"),
                 "Grew more than market": ("Lift %", lambda s: f"{(s > 0).mean() * 100:.0f}%")}).round(1)
                 .sort_values("Avg lift %", ascending=False).reset_index())
        st.markdown("**By staff**")
        _si_show(done.groupby("Staff").agg(Visits=("Customer", "size"), **{"Avg lift %": ("Lift %", "mean")}).round(1).reset_index())
    else:
        st.info("Results appear 14 days after each visit.")
    st.markdown("**Every visit**")
    _si_show(eff.sort_values("Date", ascending=False).reset_index(drop=True), money=("Pcs 14 d before", "Pcs 14 d after"),
             height=min(460, 60 + 36 * len(eff)))


def _visit_scorecard_body(visits, daily, names):
    st.markdown("#### 🏅 Monthly scorecard")
    if visits.empty:
        st.info("មិនទាន់មានការចុះហាងទេ។")
        return
    months = sorted(visits["_dt"].dt.strftime("%Y-%m").unique(), reverse=True)
    c1, c2 = st.columns(2)
    month = c1.selectbox("Month", months, key="vs_month")
    staff_all = sorted(visits["Staff"].unique())
    who = c2.selectbox("Staff", staff_all, key="vs_staff") if len(staff_all) > 1 else staff_all[0]
    m0 = pd.Timestamp(month + "-01")
    m1 = m0 + pd.offsets.MonthEnd(0)
    v = visits[(visits["_dt"] >= m0) & (visits["_dt"] <= m1 + pd.Timedelta(hours=23, minutes=59)) & (visits["Staff"] == who)].copy()
    for c in ("Minutes", "Stickers changed", "Check score %", "Satisfaction"):
        v[c] = pd.to_numeric(v[c], errors="coerce")
    day_counts = v.assign(Day=v["_dt"].dt.date, Key=v["Customer"].map(norm_name)).groupby("Day")["Key"].nunique()
    fixed = visits[(visits["Fixed by"] != "-") & pd.to_datetime(visits["Fixed at"], errors="coerce").between(m0, m1 + pd.Timedelta(days=1))]
    eff = _visit_effect(_si_frame_sig(visits) + _si_frame_sig(daily), visits, daily)
    eff_m = eff[(eff["Staff"] == who) & eff["Date"].str.startswith(month) & eff["Lift %"].notna()] if not eff.empty else eff
    zone_chg = None
    if not daily.empty:
        p0, p1 = m0 - pd.offsets.MonthBegin(1), m0 - pd.Timedelta(days=1)
        last_day = min(m1, pd.Timestamp(today_kh()))
        n_days = (last_day - m0).days + 1
        cur = daily[(daily["D"] >= m0) & (daily["D"] <= last_day)]["Pcs"].sum()
        prev = daily[(daily["D"] >= p0) & (daily["D"] <= min(p1, p0 + pd.Timedelta(days=n_days - 1)))]["Pcs"].sum()
        zone_chg = (cur - prev) / prev * 100 if prev > 0 else None
    st.markdown(f"**{who} · {m0:%B %Y}**")
    a1, a2, a3, a4 = st.columns(4)
    a1.metric("Visits", f"{len(v):,}", f"{v['Customer'].nunique()} shops", delta_color="off")
    a2.metric("Visits per working day", f"{day_counts.mean():.1f}" if len(day_counts) else "—",
              f"{int((day_counts >= VISIT_DAILY_TARGET).sum())} / {len(day_counts)} days hit {VISIT_DAILY_TARGET}", delta_color="off")
    a3.metric("Confirmed at shop", f"{v['Location check'].str.startswith('✅').mean() * 100:.0f}%" if len(v) else "—")
    a4.metric("Avg minutes per shop", f"{v['Minutes'].mean():.0f}" if v["Minutes"].notna().any() else "—")
    b1, b2, b3, b4 = st.columns(4)
    b1.metric("Stickers changed", f"{int(v['Stickers changed'].fillna(0).sum()):,}")
    b2.metric("Problems found / fixed", f"{int((v['Problems'] != '-').sum())} / {len(fixed)}")
    b3.metric("Shop check score", f"{v['Check score %'].mean():.0f}%" if v["Check score %"].notna().any() else "—")
    b4.metric("Lift of visited shops", f"{eff_m['Lift %'].mean():+.0f}%" if len(eff_m) else "⏳ wait 14 d")
    covered = visits.assign(Key=visits["Customer"].map(norm_name))
    covered = covered[covered["_dt"] >= pd.Timestamp(today_kh()) - pd.Timedelta(days=90)]["Key"].nunique()
    st.caption(f"Phnom Penh bun pcs this month: {('%+.0f%%' % zone_chg) if zone_chg is not None else '—'} vs the same days last month · "
               f"shops visited in the last 90 days: {covered} of {len(names)}.")
    st.markdown("**Month by month**")
    hist = visits[visits["Staff"] == who].assign(Month=visits["_dt"].dt.strftime("%Y-%m"), Key=visits["Customer"].map(norm_name),
                                                Day=visits["_dt"].dt.date)
    hist["Stickers changed"] = pd.to_numeric(hist["Stickers changed"], errors="coerce").fillna(0)
    trend = hist.groupby("Month").agg(Visits=("VisitID", "size"), Shops=("Key", "nunique"), Days=("Day", "nunique"),
                                      **{"At shop %": ("Location check", lambda s: round(s.str.startswith("✅").mean() * 100)),
                                         "Stickers": ("Stickers changed", "sum"),
                                         "Problems found": ("Problems", lambda s: int((s != "-").sum()))}).reset_index()
    trend["Visits / day"] = (trend["Visits"] / trend["Days"]).round(1)
    if not eff.empty:
        lift = eff[(eff["Staff"] == who) & eff["Lift %"].notna()].assign(Month=lambda f: f["Date"].str[:7]).groupby("Month")["Lift %"].mean().round(0)
        trend["Avg lift %"] = trend["Month"].map(lift)
    _si_show(trend.sort_values("Month", ascending=False))


def _visit_match_admin(names, have, cands):
    """Shops without a location + the Customer Map pins whose name looks alike. Admin ticks the right one."""
    rows = []
    for k, n in sorted(names.items(), key=lambda x: str(x[1]).upper()):
        if k in have:
            continue
        for score, pid, pname, lat, lon in cands.get(k, []):
            rows.append({"Use": False, "Shop (Master List)": n, "Pin name in Customer Map": pname,
                         "Same name %": round(score * 100), "Check": f"https://www.google.com/maps?q={lat},{lon}",
                         "_lat": lat, "_lon": lon})
    with st.expander(f"🔗 Match Customer Map pins to shops ({len({r['Shop (Master List)'] for r in rows})} shops have a likely pin)",
                     expanded=bool(rows)):
        if not rows:
            st.caption("No more likely matches. Shops left without a location must be saved at the shop.")
            return
        st.caption("These pins are in 📍 Customer Map but their name is spelled differently from the Master List. "
                   "Tick **Use** on the correct pin (one per shop) and press Save. Open **Check** if you are not sure.")
        frame = pd.DataFrame(rows)
        edited = st.data_editor(frame.drop(columns=["_lat", "_lon"]), hide_index=True, use_container_width=True, key="vmatch_editor",
                                disabled=["Shop (Master List)", "Pin name in Customer Map", "Same name %", "Check"],
                                column_config={"Use": st.column_config.CheckboxColumn("Use"),
                                               "Check": st.column_config.LinkColumn("Check", display_text="open map")},
                                height=min(520, 60 + 35 * len(frame)))
        picked = frame[edited["Use"].fillna(False).astype(bool).values]
        dup = picked["Shop (Master List)"].duplicated(keep=False)
        if dup.any():
            st.error("Tick only one pin per shop: " + ", ".join(sorted(set(picked.loc[dup, "Shop (Master List)"]))))
        elif st.button(f"💾 Save {len(picked)} match(es)", type="primary", disabled=picked.empty, key="vmatch_save"):
            try:
                rows_out = [{"Date": now_str(), "Customer": r["Shop (Master List)"], "Lat": f"{r['_lat']:.6f}", "Lon": f"{r['_lon']:.6f}",
                             "Accuracy m": "-", "Source": "Customer Map pin (confirmed)", "By": current_user() or "-",
                             "Status": "Active", "Note": f"map name: {r['Pin name in Customer Map']}"[:150]} for _, r in picked.iterrows()]
                append_rows(VISIT_PIN_FILE, rows_out)
                audit("shop pins matched", f"{len(rows_out)} shops")
                st.session_state["flash"] = f"Linked {len(rows_out)} shop(s) to their map pin"
                _frag_rerun()
            except Exception as e:
                st.error("មិនអាចរក្សាទុកបានទេ: " + str(e)[:150])


def _visit_pins_admin(names):
    st.markdown("#### 📍 Shop locations")
    registry = _visit_registry()
    store = _visit_pin_store()
    cands, auto = _visit_candidates_for(names, registry)
    have = {k for k, n in names.items() if _visit_pin(n, registry, store, auto)}
    p1, p2, p3, p4 = st.columns(4)
    p1.metric("Phnom Penh shops with a location", f"{len(have)} / {len(names)}")
    p2.metric("Linked automatically (spelling)", f"{sum(1 for k in auto if k in have and k not in store):,}")
    p3.metric("Saved / confirmed by staff", f"{sum(1 for k in names if k in store):,}")
    p4.metric("Still missing", f"{len(names) - len(have):,}")
    _visit_match_admin(names, have, cands)
    st.caption("A visit cannot start without a location. Staff save it at the shop with GPS (or a Google Maps link); "
               "a location saved at the shop is used before the 📍 Customer Map pin. Remove a location here if it is wrong.")
    try:
        df = read_raw(VISIT_PIN_FILE, VISIT_PIN_COLS)
    except Exception as e:
        st.warning("Shop locations could not be read: " + str(e)[:120])
        return
    act = df[df["Status"].eq("Active")].sort_values("_dt", ascending=False)
    if act.empty:
        st.info("No locations saved by staff yet.")
    else:
        show = act.assign(Map=[f"https://www.google.com/maps?q={a},{b}" for a, b in zip(act["Lat"], act["Lon"])])[
            ["Date", "Customer", "Source", "Accuracy m", "By", "Note", "Map"]].reset_index(drop=True)
        try:
            st.dataframe(show, hide_index=True, use_container_width=True,
                         column_config={"Map": st.column_config.LinkColumn("Map", display_text="open")},
                         height=min(420, 60 + 35 * len(show)))
        except Exception:
            st.dataframe(show, hide_index=True, use_container_width=True)
        pick = st.selectbox("Remove a wrong location", ["-"] + [f"{r['Date']} · {r['Customer']}" for _, r in act.iterrows()], key="vpin_rm")
        if pick != "-" and st.button("🗑️ Remove this location", key="vpin_rm_btn"):
            d, c = pick.split(" · ", 1)

            def _rm(frame, d=d, c=c):
                m = frame["Date"].eq(d) & frame["Customer"].eq(c) & frame["Status"].eq("Active")
                frame.loc[m, "Status"] = "Removed"
                frame.loc[m, "Note"] = safe_text(f"removed by {current_user() or '-'} {now_str()}", 120)
                return frame
            try:
                modify_csv(VISIT_PIN_FILE, VISIT_PIN_COLS, _rm)
                audit("shop pin removed", pick)
                st.session_state["flash"] = "Location removed"
                _frag_rerun()
            except Exception as e:
                st.error("Could not remove: " + str(e)[:150])
    missing = sorted(n for k, n in names.items() if k not in have)
    if missing:
        with st.expander(f"Shops still without a location ({len(missing)})"):
            st.write(", ".join(missing))


# ---------- 🆕 new customers from the NPHK Leads Report ----------
LEAD_COLS = ["Date", "Customer", "Phone", "Channel", "Sales rep", "Province", "Package", "Qty", "Lead status",
             "Map link", "Lat", "Lon", "Map note", "Notes", "Master name", "Imported at", "Imported by"]
LEAD_FIRST_VISIT_DAYS = 7          # a new shop should get its first visit within this many days of the sale
LEAD_NEW_DAYS = 45                 # a sale this recent still counts as "new customer"
LEAD_HEADER_MAP = {"DATE": "Date", "CUSTOMER NAME": "Customer", "PHONE NUMBER": "Phone", "CHANNEL": "Channel",
                   "ASSIGNED SALES REP": "Sales rep", "LOCATION / PROVINCE": "Province", "PRODUCT PACKAGE / MODEL": "Package",
                   "QUANTITY (QTY)": "Qty", "INQUIRY STATUS": "Lead status", "GOOGLE MAPS URL": "Map link",
                   "NOTES / REMARKS": "Notes"}
LEAD_FIRST_VISIT_CHECKS = ["Fridge installed & plugged in", "Stickers / poster put up",
                           "Owner knows prices & how to heat buns", "Owner has our phone / Telegram"]


def _lead_is_pp(province):
    p = unicodedata.normalize("NFC", str(province or "")).replace(" ", "")
    return p in ("ភ្នំពេញ", "PhnomPenh", "PHNOMPENH")


def _lead_is_sale(status):
    s = str(status or "").upper()
    return "CLOSED" in s or "CONFIRM" in s or "ទិញ" in s


def _lead_parse_report(data):
    """NPHK Leads Report .xlsx -> DataFrame with LEAD_COLS fields (header row found by 'CUSTOMER NAME')."""
    raw = pd.read_excel(io.BytesIO(data), header=None, dtype=object)
    hdr = None
    for i in range(min(15, len(raw))):
        cells = [str(v).strip().upper() for v in raw.iloc[i].tolist()]
        if "CUSTOMER NAME" in cells:
            hdr = i
            break
    if hdr is None:
        raise ValueError("this is not a Leads Report: no 'CUSTOMER NAME' column found")
    cols = [str(v).strip().upper() for v in raw.iloc[hdr].tolist()]
    df = raw.iloc[hdr + 1:].copy()
    df.columns = cols
    out = pd.DataFrame({new: df[old] if old in df else "" for old, new in LEAD_HEADER_MAP.items()})
    out = out[out["Customer"].notna() & out["Customer"].astype(str).str.strip().ne("")]
    out["Date"] = pd.to_datetime(out["Date"], errors="coerce").dt.strftime("%Y-%m-%d")
    out["Qty"] = pd.to_numeric(out["Qty"], errors="coerce").fillna(0).astype(int).astype(str)
    for c in out.columns:
        out[c] = out[c].map(lambda v: "-" if v is None or (isinstance(v, float) and math.isnan(v)) or str(v).strip() in ("", "nan", "NaT") else re.sub(r"\s+", " ", str(v)).strip())
    return out.reset_index(drop=True)


def _lead_read():
    try:
        return read_raw(LEADS_FILE, LEAD_COLS, max_age=300)
    except Exception as e:
        st.warning("New customer list could not be read: " + str(e)[:150])
        return pd.DataFrame(columns=LEAD_COLS + ["_dt"])


def _lead_master_index(snap):
    """{match key: (Master List name, area)} for every customer in the Master List."""
    areas = (snap or {}).get("areas", {}) or {}
    return {_visit_match_key(n): (n, areas.get(n, "Unknown")) for n in (snap or {}).get("customers", [])}


def _lead_best_master(name, mindex):
    import difflib
    k = _visit_match_key(name)
    if k in mindex:
        return mindex[k][0], 1.0
    best, score = None, 0.0
    for mk, (mn, _a) in mindex.items():
        sm = difflib.SequenceMatcher(None, k, mk)
        if sm.real_quick_ratio() < 0.6 or sm.quick_ratio() < 0.6:
            continue
        r = sm.ratio()
        if len(k) >= 4 and (mk.startswith(k) or k.startswith(mk)):
            r = max(r, 0.86)
        if r > score:
            best, score = mn, r
    return best, score


def _lead_map_coords(url, allow_network=True):
    """(lat, lon, note) from a Google Maps link; short links are opened when allowed."""
    if not url or url == "-":
        return None, None, "no map link"
    try:
        a = analyse_map_link(url)
        if a.get("Map status") != "Ready pin" and allow_network and trusted_map_url(url):
            a = analyse_map_link(resolve_map_link(url))
        if a.get("Map status") == "Ready pin":
            lat, lon = float(a["Latitude"]), float(a["Longitude"])
            if 10 <= lat <= 15 and 102 <= lon <= 108:
                return lat, lon, "ok"
            return None, None, "outside Cambodia"
        return None, None, a.get("Map status", "no pin")
    except Exception as e:
        return None, None, "link could not be opened: " + str(e)[:60]


def _lead_active(leads, mindex=None):
    """New customers that count for visits: confirmed sales in the last LEAD_NEW_DAYS days.
    -> {norm key of the name used in the visit list: dict(name, date, pp, lat, lon)}"""
    out = {}
    if leads is None or leads.empty:
        return out
    cut = pd.Timestamp(today_kh()) - pd.Timedelta(days=LEAD_NEW_DAYS)
    for _, r in leads.iterrows():
        d = pd.to_datetime(r["Date"], errors="coerce")
        if pd.isna(d) or d < cut or not _lead_is_sale(r["Lead status"]):
            continue
        name = r["Master name"] if r["Master name"] not in ("-", "") else r["Customer"]
        area = (mindex or {}).get(_visit_match_key(name), (None, None))[1]
        pp = (area == PP) if area in (PP, "Province") else _lead_is_pp(r["Province"])
        try:
            lat, lon = float(r["Lat"]), float(r["Lon"])
        except Exception:
            lat = lon = None
        k = norm_name(name)
        if k not in out or d > out[k]["date"]:
            out[k] = {"name": name, "date": d, "pp": pp, "lat": lat, "lon": lon, "lead": r["Customer"],
                      "in_master": r["Master name"] not in ("-", "")}
    return out


def _lead_checks(leads, mindex):
    """Problems a person should fix in the Master List or the leads report."""
    rows = []
    if leads.empty:
        return pd.DataFrame(columns=["Problem", "Customer", "Date", "Detail"])
    seen = {}
    for _, r in leads.iterrows():
        name, master = r["Customer"], r["Master name"]
        if master in ("-", ""):
            best, sc = _lead_best_master(name, mindex)
            rows.append({"Problem": "❗ Not in Master List", "Customer": name, "Date": r["Date"],
                         "Detail": f"closest: {best} ({sc * 100:.0f}%)" if best and sc >= 0.6 else "add this shop to the Master List"})
        else:
            area = mindex.get(_visit_match_key(master), (None, None))[1]
            lp = r["Province"]
            if lp not in ("-", "") and area in (PP, "Province") and (_lead_is_pp(lp) != (area == PP)):
                rows.append({"Problem": "⚠️ Province differs", "Customer": name, "Date": r["Date"],
                             "Detail": f"leads report: {lp} · Master List: {area}"})
            if _visit_match_key(master) != _visit_match_key(name):
                rows.append({"Problem": "ℹ️ Spelled differently", "Customer": name, "Date": r["Date"],
                             "Detail": f"Master List: {master}"})
        if r["Province"] in ("-", ""):
            rows.append({"Problem": "⚠️ No province", "Customer": name, "Date": r["Date"], "Detail": "fill LOCATION / PROVINCE"})
        if r["Map link"] in ("-", ""):
            rows.append({"Problem": "⚠️ No map link", "Customer": name, "Date": r["Date"], "Detail": "add the shop's Google Maps link"})
        elif r["Lat"] in ("-", ""):
            rows.append({"Problem": "⚠️ Map link has no pin", "Customer": name, "Date": r["Date"], "Detail": r["Map note"]})
        k = _visit_match_key(r["Master name"] if r["Master name"] not in ("-", "") else name)
        if k in seen:
            rows.append({"Problem": "⚠️ Listed twice", "Customer": name, "Date": r["Date"], "Detail": f"also on {seen[k]}"})
        seen[k] = r["Date"]
    import difflib
    keys = [(_visit_match_key(n), n) for n in leads["Customer"].unique()]
    for i, (a, an) in enumerate(keys):
        for b, bn in keys[i + 1:]:
            if a != b and difflib.SequenceMatcher(None, a, b).ratio() >= 0.9:
                rows.append({"Problem": "⚠️ Maybe the same shop", "Customer": an, "Date": "", "Detail": f"and “{bn}”"})
    return pd.DataFrame(rows)


def _lead_import_body(snap, visits):
    st.markdown("#### 🆕 New customers (from the NPHK Leads Report)")
    leads = _lead_read()
    mindex = _lead_master_index(snap)
    if has_permission("edit"):
        up = st.file_uploader("Upload the Leads Report (.xlsx)", type=["xlsx"], key="lead_upload",
                              help="The daily report from Sales & Marketing. Rows already imported are updated, not doubled.")
        if up is not None:
            try:
                new = _lead_parse_report(up.getvalue())
            except Exception as e:
                st.error("Could not read the file: " + str(e)[:160])
                new = None
            if new is not None:
                sales = new[new["Lead status"].map(_lead_is_sale)]
                st.caption(f"{len(new)} rows in the file · {len(sales)} confirmed sales.")
                if st.button(f"⬆️ Import {len(new)} rows", type="primary", key="lead_import_btn"):
                    with st.spinner("Matching names and opening map links…"):
                        old = {(_visit_match_key(c), d): r for (c, d), r in
                               zip(zip(leads["Customer"], leads["Date"]), leads.to_dict("records"))} if not leads.empty else {}
                        rows = []
                        for _, r in new.iterrows():
                            prev = old.get((_visit_match_key(r["Customer"]), r["Date"]))
                            master, sc = _lead_best_master(r["Customer"], mindex)
                            master = master if sc >= 0.999 else (prev["Master name"] if prev else "-")
                            if prev and prev["Map link"] == r["Map link"] and prev["Lat"] not in ("-", ""):
                                lat, lon, note = prev["Lat"], prev["Lon"], prev["Map note"]
                            else:
                                la, lo, note = _lead_map_coords(r["Map link"])
                                lat, lon = (f"{la:.6f}", f"{lo:.6f}") if la is not None else ("-", "-")
                            rows.append({**r.to_dict(), "Lat": lat, "Lon": lon, "Map note": note, "Master name": master or "-",
                                         "Imported at": now_str(), "Imported by": current_user() or "-"})
                        keys_new = {(_visit_match_key(r["Customer"]), r["Date"]) for r in rows}

                        def _merge(df, rows=rows, keys_new=keys_new):
                            df = df.drop(columns=[c for c in ("_dt",) if c in df])
                            keep = df[[(_visit_match_key(c), d) not in keys_new for c, d in zip(df["Customer"], df["Date"])]]
                            return pd.concat([keep, pd.DataFrame(rows)], ignore_index=True)
                        try:
                            modify_csv(LEADS_FILE, LEAD_COLS, _merge)
                            audit("leads imported", f"{len(rows)} rows from {up.name}")
                            st.session_state["flash"] = f"Imported {len(rows)} new-customer rows"
                            st.session_state.pop("lead_upload", None)
                            _frag_rerun()
                        except Exception as e:
                            st.error("Could not save: " + str(e)[:160])
    if leads.empty:
        st.info("No leads imported yet. Upload the NPHK Leads Report above.")
        return
    active = _lead_active(leads, mindex)
    visited = {}
    if not visits.empty:
        vv = visits.assign(Key=visits["Customer"].map(norm_name))
        visited = vv.groupby("Key")["_dt"].max().to_dict()
    pp = {k: v for k, v in active.items() if v["pp"]}
    waiting = {k: v for k, v in pp.items() if not (k in visited and visited[k] >= v["date"])}
    late = {k: v for k, v in waiting.items() if (pd.Timestamp(today_kh()) - v["date"]).days > LEAD_FIRST_VISIT_DAYS}
    k1, k2, k3, k4 = st.columns(4)
    k1.metric("New customers (last 45 days)", f"{len(active):,}", f"{len(pp)} in Phnom Penh", delta_color="off")
    k2.metric("Phnom Penh: first visit done", f"{len(pp) - len(waiting)} / {len(pp)}")
    k3.metric(f"First visit late (> {LEAD_FIRST_VISIT_DAYS} days)", f"{len(late):,}")
    k4.metric("Not in Master List", f"{int(leads['Master name'].isin(['-', '']).sum()):,}")

    # ---- link names to the Master List
    unl = leads[leads["Master name"].isin(["-", ""])].copy()
    if not unl.empty and has_permission("edit"):
        with st.expander(f"🔗 Link {len(unl)} leads to their Master List name", expanded=True):
            st.caption("Choose the same shop's name in the Master List. Leave empty if the shop is not in the Master List yet "
                       "(add it there first). Linked shops get their sales history, zone and map location.")
            options = [""] + sorted(n for n, _a in mindex.values())
            unl["Master List name"] = [(lambda b: b[0] if b[0] and b[1] >= 0.86 else "")(_lead_best_master(n, mindex)) for n in unl["Customer"]]
            view = unl[["Date", "Customer", "Province", "Master List name"]].reset_index()
            ed = st.data_editor(view, hide_index=True, use_container_width=True, key="lead_link_editor",
                                disabled=["index", "Date", "Customer", "Province"],
                                column_config={"index": None, "Master List name": st.column_config.SelectboxColumn(
                                    "Master List name", options=options, help="Suggested when the names are very close — check it")},
                                height=min(480, 60 + 35 * len(view)))
            chosen = ed[ed["Master List name"].fillna("").ne("")]
            if st.button(f"💾 Save {len(chosen)} link(s)", type="primary", disabled=chosen.empty, key="lead_link_save"):
                pairs = {(r["Customer"], r["Date"]): r["Master List name"] for _, r in chosen.iterrows()}

                def _link(df, pairs=pairs):
                    for (c, d), m in pairs.items():
                        df.loc[df["Customer"].eq(c) & df["Date"].eq(d), "Master name"] = m
                    return df
                try:
                    modify_csv(LEADS_FILE, LEAD_COLS, _link)
                    audit("leads linked", f"{len(pairs)}")
                    st.session_state["flash"] = f"Linked {len(pairs)} lead(s)"
                    _frag_rerun()
                except Exception as e:
                    st.error("មិនអាចរក្សាទុកបានទេ: " + str(e)[:150])

    st.markdown("**🗓️ First visit for new Phnom Penh shops**")
    if pp:
        rows = []
        for k, v in sorted(pp.items(), key=lambda x: x[1]["date"]):
            days = (pd.Timestamp(today_kh()) - v["date"]).days
            done = k in visited and visited[k] >= v["date"]
            rows.append({"Sold on": f"{v['date']:%d %b}", "Shop": v["name"], "Days since sale": days,
                         "First visit": f"✅ {visited[k]:%d %b}" if done else ("🔴 late" if days > LEAD_FIRST_VISIT_DAYS else "⏳ to do"),
                         "Map": "📍 yes" if v["lat"] is not None else "⚠️ no pin",
                         "In Master List": "yes" if v["in_master"] else "❗ no"})
        _si_show(pd.DataFrame(rows))
    else:
        st.caption("No new Phnom Penh customers in the last 45 days.")
    st.markdown("**🧹 Things to fix in the Master List / leads report**")
    chk = _lead_checks(leads, mindex)
    if chk.empty:
        st.success("Everything matches. 🎉")
    else:
        st.caption(" · ".join(f"{p}: {n}" for p, n in chk["Problem"].value_counts().items()))
        _si_show(chk, height=min(460, 60 + 35 * len(chk)))
    with st.expander("All imported leads"):
        _si_show(leads.drop(columns=["_dt"], errors="ignore"))


def _visit_start(customer):
    """Button callback: runs before the page is drawn again, so it may switch the section."""
    st.session_state["visit_customer"] = customer
    st.session_state.pop("visit_customer_box", None)
    st.session_state["visit_zone_force"] = True
    st.session_state["visit_view"] = "📝 New visit"


def _visit_test_clear():
    try:
        with _sync_state()["lock"], file_lock(VISITS_TEST_FILE):
            _write_atomic(VISITS_TEST_FILE, (",".join(VISIT_COLS) + "\n").encode("utf-8-sig"))
            if USE_DROPBOX:
                try:
                    pull(VISITS_TEST_FILE, force=True)
                except Exception:
                    pass
                _write_atomic(VISITS_TEST_FILE, (",".join(VISIT_COLS) + "\n").encode("utf-8-sig"))
                push(VISITS_TEST_FILE)
        for k in [k for k in st.session_state if str(k).startswith(("visit_gps", "visit_customer"))]:
            st.session_state.pop(k, None)
        audit("shop visit TEST cleared")
        st.session_state["flash"] = "🧪 Test visits deleted"
    except Exception as e:
        st.session_state["visit_gps_error"] = "Could not clear test visits: " + str(e)[:120]


def tab_shop_visits():
    """Shop Visits runs as a fragment: tapping inside it redraws only this section, not the whole app."""
    want_live = (st.session_state.get("visit_view") == "📊 Visit report" and bool(st.session_state.get("vr_live")))
    st.session_state["_visit_live_wrapper"] = want_live
    try:
        (_shop_visits_live if want_live else _shop_visits_fragment)()
    except Exception as e:
        if "fragment" in str(e).lower():
            _shop_visits_body()           # older Streamlit without fragments
        else:
            raise


@st.fragment
def _shop_visits_fragment():
    _shop_visits_body()


@st.fragment(run_every=30)
def _shop_visits_live():
    _shop_visits_body()


def _shop_visits_body():
    if _vf_draft_restore():                              # before any switch is drawn (it may turn Test mode on)
        st.session_state["visit_view"] = "📝 New visit"
        st.toast("បានយករបាយការណ៍ដែលមិនទាន់រួចមកវិញ។ សូមបន្តពីកន្លែងដែលបានឈប់។", icon="↩️")
    _flash = st.session_state.pop("flash", None)        # saves redraw only Shop Visits, so show their message here
    if _flash:
        st.toast(_flash, icon="✅")
    h1, h2, h3 = st.columns([3, 1.3, 2])
    h1.markdown("### 🏪 ចុះជួបហាង (Shop Visits)")
    _visit_phone_mode()
    h2.toggle("📱 Phone mode", key="visit_phone", help="ប៊ូតុងធំ និងទម្រង់ជាជំហានៗ។ បើកដោយស្វ័យប្រវត្តិលើទូរស័ព្ទ។")
    if _visit_phone_mode():
        st.markdown(VISIT_PHONE_CSS, unsafe_allow_html=True)
    if current_role() == "admin":
        h3.toggle("🧪 Test mode (practice — not in real reports)", key="visit_test_mode",
                  on_change=lambda: [st.session_state.pop(k, None) for k in ("visit_gps", "visit_customer", "visit_customer_box", "visit_draft")])
    if _visit_test_mode():
        b1, b2 = st.columns([4, 1])
        b1.warning("🧪 **TEST MODE.** You can fill in visits from anywhere: no real GPS or shop location needed, any photo is "
                   "accepted. Test visits are saved separately and never appear in the real plan, reports or scorecard. "
                   "Switch it off to see real data again.")
        b2.button("🗑️ Delete all test visits", key="visit_test_clear", on_click=_visit_test_clear, use_container_width=True)
    views = ["📋 Today's plan", "📝 New visit", "🆕 New customers"]
    if has_permission("reports"):
        views += ["✅ Review visits", "📊 Visit report", "🔴 Open problems", "📈 Did it help?", "🏅 Scorecard"]
    if current_role() == "admin":
        views.append("⚙️ Shops & zones")
    if st.session_state.get("visit_view") not in views:
        st.session_state["visit_view"] = views[0]
    if _visit_phone_mode():
        view = st.selectbox("ផ្នែក", views, key="visit_view", label_visibility="collapsed", format_func=_km)
    else:
        view = st.radio("ផ្នែក", views, horizontal=True, key="visit_view", label_visibility="collapsed", format_func=_km)
    if (view == "📊 Visit report" and bool(st.session_state.get("vr_live"))) != st.session_state.get("_visit_live_wrapper", False):
        st.rerun()                        # switch between the normal and the auto-refresh wrapper
    visits = _visit_read()
    if view == "📝 New visit":
        if not has_permission("edit"):
            st.info("គណនីរបស់អ្នកអាចមើលបាន ប៉ុន្តែមិនអាចកត់ត្រាការចុះហាងបានទេ។")
            return
        stats, names, _areas = _visit_customer_stats()
        _visit_new_form(visits, stats, names)
    elif view == "📋 Today's plan":
        user = current_user() or "-"
        stats, names, areas = _visit_customer_stats()
        if not names:
            st.info("រកមិនឃើញអតិថិជននៅភ្នំពេញទេ។ សូមពិនិត្យតំបន់ក្នុង Master List។")
            return
        _visit_progress(visits, user)
        _visit_redo_notice(visits, user)
        zone_map = _visit_zone_map(names)
        zone_src = {k: v[1] for k, v in _visit_zone_info(names).items()}
        all_route = _visit_route(visits, stats, names, areas, zone_map)
        due_all = _visit_is_due(all_route)
        zone = _visit_zone_picker(zone_map, "visit_zone_plan", Counter(due_all["Area"]))
        route = all_route[all_route["Area"].eq(zone)].reset_index(drop=True) if zone else all_route
        st.caption(f"📅 ហាងនៅភ្នំពេញ {len(due_all)} ត្រូវចុះឥឡូវ · ក្នុងតំបន់នេះ {len(_visit_is_due(route))}។")
        if route.empty:
            st.info("មិនទាន់មានហាងក្នុងតំបន់នេះទេ។")
            return
        registry = _visit_registry()
        pin_store = _visit_pin_store()
        try:
            _c, auto_pins = _visit_candidates_for(names, registry)
        except Exception:
            auto_pins = {}
        done_today = set(visits.loc[visits["_dt"].dt.date == today_kh(), "Customer"].map(norm_name)) if not visits.empty else set()
        todo = route[~route["Customer"].map(norm_name).isin(done_today)]
        st.markdown(f"**⭐ ហាងណែនាំ {VISIT_DAILY_TARGET} សម្រាប់ថ្ងៃនេះ** — ហាងសំខាន់បំផុតក្នុងតំបន់នេះ")
        q = st.text_input("🔎 ស្វែងរកហាងក្នុងតំបន់នេះ", key="vroute_q", max_chars=60)
        r = todo if not q.strip() else todo[todo["Customer"].str.contains(q.strip(), case=False, regex=False)]
        for n, (i, row) in enumerate(r.head(VISIT_DAILY_TARGET + 12).iterrows()):
            if n == VISIT_DAILY_TARGET and not q.strip():
                st.markdown("**ហាងផ្សេងទៀតក្នុងតំបន់នេះ**")
            link, exact = _visit_map_link(row["Customer"], registry, pin_store, auto_pins)
            with st.container(border=True):
                c1, c2, c3 = st.columns([4, 1, 1])
                c1.markdown(f"**{'⭐ ' if n < VISIT_DAILY_TARGET and not q.strip() else ''}{row['Customer']}**  \n{row['Why visit']}  \n"
                            f"<span style='color:#6B7280'>{_km(row['Size'])} · ចុះហាងចុងក្រោយ {_km_days(row['Last visit'])} · {row['Pcs 28 days']:,} pcs ក្នុង ២៨ ថ្ងៃ"
                            f" · {zone_src.get(norm_name(row['Customer']), '')}</span>",
                            unsafe_allow_html=True)
                c2.link_button("🧭 ទៅ" if exact else "⚠️ គ្មានទីតាំង", link, use_container_width=True,
                               help="ផ្លូវទៅទីតាំងហាងដែលបានរក្សាទុក" if exact
                               else "No saved location yet: this searches the name on Google Maps. Save the real location at the shop.")
                c3.button("ចាប់ផ្តើម ▶", key=f"vstart_{i}", use_container_width=True,
                          on_click=_visit_start, args=(row["Customer"],))
        if done_today & set(route["Customer"].map(norm_name)):
            st.caption("✅ បានចុះរួចថ្ងៃនេះ (ដោយអ្នកណាម្នាក់): " + ", ".join(route.loc[route["Customer"].map(norm_name).isin(done_today), "Customer"]))
    elif view == "⚙️ Shops & zones":
        stats, names, areas = _visit_customer_stats()
        _visit_settings_admin(_visit_route(visits, stats, names, areas, _visit_zone_map(names)))
        st.divider()
        _visit_pins_admin(names)
        st.divider()
        _visit_zones_admin(names, visits)
    elif view == "✅ Review visits":
        _visit_review_body(visits)
    elif view == "🆕 New customers":
        snap, _src, _path, _err = current_snapshot()
        _visit_customer_stats()
        _lead_import_body(snap or {}, visits)
    elif view == "📈 Did it help?":
        _s, names, _a = _visit_customer_stats()
        _visit_effect_body(visits, st.session_state.get("_visit_daily", pd.DataFrame()))
    elif view == "🏅 Scorecard":
        _s, names, _a = _visit_customer_stats()
        _visit_scorecard_body(visits, st.session_state.get("_visit_daily", pd.DataFrame()), names)
    elif view == "📊 Visit report":
        live = st.toggle("🔄 Live (refresh every 30 s)", key="vr_live")
        if live != st.session_state.get("_visit_live_wrapper", False):
            st.rerun()
        if live:
            st.caption(f"Live · updated {now_kh():%H:%M:%S}")
        _visit_report_body(visits)
    elif view == "🔴 Open problems":
        _visit_problems_body(visits)


# ==========================================
# 📸 MEDIA TEAM — photos & videos of Phnom Penh shops every Friday and Saturday
# ==========================================
MEDIA_FILE = os.path.join(DATA_DIR, "media_shoots.csv")
MEDIA_COLS = ["Date", "Customer", "ShootID", "Zone", "By", "Photos", "Videos", "Sticker", "Menu", "Banner",
              "Why", "Note", "Shoot day"]
MEDIA_DIR = "media"
MEDIA_DAYS = (4, 5)                       # Friday, Saturday (Monday = 0)
MEDIA_ITEMS = ["Sticker", "Menu", "Banner"]
MEDIA_STATES = ["✅ Put up a new one today", "👍 Has one, still good", "⚠️ Old — needs a new one", "❌ None — needs one",
                "➖ Not for this shop"]
MEDIA_NEED = ("⚠️ Old — needs a new one", "❌ None — needs one")
MEDIA_KM = {"Sticker": "ស្ទីគ័រ", "Menu": "ម៉ឺនុយ", "Banner": "បដា / Banner",
            "✅ Put up a new one today": "✅ បានដាក់ថ្មីថ្ងៃនេះ", "👍 Has one, still good": "👍 មានហើយ នៅល្អ",
            "⚠️ Old — needs a new one": "⚠️ ចាស់ — ត្រូវការថ្មី", "❌ None — needs one": "❌ មិនមាន — ត្រូវការ",
            "➖ Not for this shop": "➖ មិនត្រូវការសម្រាប់ហាងនេះ"}
MEDIA_PHOTO_MAX = 12
MEDIA_VIDEO_MAX_MB = 200
MEDIA_RECENT_DAYS = 45                    # journal events this recent put a shop on the media list
MEDIA_REFRESH_DAYS = 90                   # photos older than this are "old"
# journal remark words -> why the media team should go
MEDIA_EVENT_RULES = [
    ("fridge", 10, "🧊 ទូថ្មី", re.compile(r"ទូរ?\s*ថ្មី|NEW\s*FRIDGE", re.I)),
    ("display", 5, "🪧 ឧបករណ៍តាំងថ្មី", re.compile(r"X[\s\-]*STAND|រ៉េស៊ីស្តង់|ឆ័ត្រ|ឆ៍ត្រ|UMBRELLA|STICKER|ស្ទីគ័រ|BANNER|ផ្ទាំង|MENU|ម៉ឺនុយ", re.I)),
]


def _mkm(v):
    return MEDIA_KM.get(v, v)


def _media_read():
    try:
        return read_raw(MEDIA_FILE, MEDIA_COLS, max_age=60)
    except Exception:
        return pd.DataFrame(columns=MEDIA_COLS + ["_dt"])


def _media_next_shoot_day(today):
    """Today when it is Friday / Saturday, else the coming Friday."""
    if today.weekday() in MEDIA_DAYS:
        return today
    return today + timedelta(days=(4 - today.weekday()) % 7)


def _media_rel(name):
    month = name[1:7] if name[:1] == "M" and name[1:7].isdigit() else "misc"
    return f"{MEDIA_DIR}/{month[:4]}-{month[4:6]}/{name}"


def _media_save_file(name, data):
    """Photos and videos go to <Dropbox folder>/media/YYYY-MM/. Big videos are sent in 8 MB pieces."""
    rel = _media_rel(name)
    if not USE_DROPBOX:
        full = os.path.join(DATA_DIR, rel)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        _write_atomic(full, data)
        return
    import dropbox
    dbx, path, chunk = _dbx(), f"{DROPBOX_FOLDER}/{rel}", 8 * 1024 * 1024
    if len(data) <= 4 * chunk:
        dbx.files_upload(data, path, mode=dropbox.files.WriteMode.overwrite, mute=True)
        return
    start = dbx.files_upload_session_start(data[:chunk])
    cursor = dropbox.files.UploadSessionCursor(session_id=start.session_id, offset=chunk)
    while cursor.offset + chunk < len(data):
        dbx.files_upload_session_append_v2(data[cursor.offset:cursor.offset + chunk], cursor)
        cursor.offset += chunk
    dbx.files_upload_session_finish(data[cursor.offset:], cursor,
                                    dropbox.files.CommitInfo(path=path, mode=dropbox.files.WriteMode.overwrite, mute=True))


@st.cache_data(show_spinner=False, max_entries=120, ttl=3600)
def _media_load_photo(name):
    return _media_load(name)


def _media_load(name):
    rel = _media_rel(name)
    if USE_DROPBOX:
        _md, res = _dbx().files_download(f"{DROPBOX_FOLDER}/{rel}")
        return res.content
    with open(os.path.join(DATA_DIR, rel), "rb") as f:
        return f.read()


def _media_last_shoot(shoots):
    """{customer key: newest shoot row}."""
    if shoots.empty:
        return {}
    s = shoots.sort_values("_dt")
    return {norm_name(r["Customer"]): r for r in s.to_dict("records")}


def _media_events(names, today):
    """{key: [(date, kind, score, label, remark)]} from the journal remarks + first orders + new leads."""
    out = {}
    start = pd.Timestamp(today) - pd.Timedelta(days=MEDIA_RECENT_DAYS)
    comb = st.session_state.get("si_combined", pd.DataFrame())
    if comb is not None and not comb.empty and {"Date", "Customer", "Remark"} <= set(comb.columns):
        c = comb[["Date", "Customer", "Remark"]].copy()
        c["D"] = pd.to_datetime(c["Date"], errors="coerce")
        c = c[(c["D"] >= start) & c["Remark"].astype(str).str.strip().ne("-")]
        for d, cust, rem in zip(c["D"], c["Customer"], c["Remark"].astype(str)):
            k = norm_name(cust)
            if k not in names:
                continue
            for kind, score, label, rx in MEDIA_EVENT_RULES:
                if rx.search(rem):
                    out.setdefault(k, []).append((d.normalize(), kind, score, label, rem))
                    break
    daily = st.session_state.get("_visit_daily", pd.DataFrame())
    if daily is not None and not daily.empty:
        first = daily.groupby("Key")["D"].min()
        older = set()                                       # bought in months before the daily journal starts = not new
        try:
            hm = _si_read_hist(SI_HIST_MONTHLY_FILE)
            if not hm.empty and {"Customer", "Month"} <= set(hm.columns):
                start_m = pd.Timestamp(daily["D"].min()).strftime("%Y-%m")
                pcs = pd.to_numeric(hm["Pcs"], errors="coerce").fillna(0) if "Pcs" in hm.columns else 1
                older = set(hm.loc[(hm["Month"].astype(str) < start_m) & (pcs > 0), "Customer"].map(norm_name))
        except Exception:
            older = set()
        for k, d in first.items():
            if k in names and k not in older and d >= pd.Timestamp(today) - pd.Timedelta(days=30):
                out.setdefault(k, []).append((pd.Timestamp(d).normalize(), "new", 8, "🆕 អតិថិជនថ្មី", f"បញ្ជាទិញលើកដំបូង {d:%d %b}"))
    for k, v in (st.session_state.get("_visit_new", {}) or {}).items():
        if k in names and v.get("date") is not None and not any(e[1] == "new" for e in out.get(k, [])):
            out.setdefault(k, []).append((pd.Timestamp(v["date"]).normalize(), "new", 8, "🆕 អតិថិជនថ្មី", "ពី Leads report"))
    return out


def _media_priority(stats, names, zone_map, shoots, today):
    """Shops for the media team, most urgent first. A journal event counts until the shop is filmed after it."""
    events = _media_events(names, today)
    last = _media_last_shoot(shoots)
    t = pd.Timestamp(today)
    rows = []
    for k, name in names.items():
        zone = zone_map.get(k, VISIT_ZONE_NOT_SET)
        if str(zone).startswith("🚫"):
            continue
        ls = last.get(k)
        shot = pd.to_datetime(ls["_dt"]) if ls is not None else None
        shot_day = shot.normalize() if shot is not None and pd.notna(shot) else None
        score, why, open_events = 0, [], []
        for d, kind, sc, label, rem in sorted(events.get(k, []), key=lambda e: -e[2]):
            if shot_day is not None and shot_day >= d:
                continue                                   # already filmed after this happened
            if any(e[1] == kind for e in open_events):
                continue
            open_events.append((d, kind))
            score += sc
            why.append(f"{label} ({d:%d %b})")
        s = stats.loc[k] if (not stats.empty and k in stats.index) else None
        pcs28 = float(s["Pcs 28d"]) if s is not None and pd.notna(s["Pcs 28d"]) else 0.0
        if shot_day is None:
            if pcs28 > 0:
                score += 3
                why.append("📷 មិនទាន់មានរូប")
        elif (t - shot_day).days > MEDIA_REFRESH_DAYS and pcs28 > 0:
            score += 2
            why.append(f"📷 រូបចាស់ ({(t - shot_day).days} ថ្ងៃ)")
        if ls is not None and any(str(ls.get(i, "")) in MEDIA_NEED for i in MEDIA_ITEMS):
            need = [MEDIA_KM[i] for i in MEDIA_ITEMS if str(ls.get(i, "")) in MEDIA_NEED]
            score += 4
            why.append("🖨️ ត្រូវការ " + ", ".join(need))
        if score <= 0:
            continue
        if pcs28 >= 1000:
            score += 1
        rows.append({"Priority": score, "Customer": name, "Zone": zone, "Why": " · ".join(why),
                     "Last photo": f"{shot_day:%d %b %Y}" if shot_day is not None else "មិនទាន់",
                     "Pcs 28 days": int(pcs28), "_new": any(e[1] in ("fridge", "new") for e in open_events)})
    out = pd.DataFrame(rows)
    if out.empty:
        return out
    return out.sort_values(["Priority", "Pcs 28 days"], ascending=False).reset_index(drop=True)


def _media_start(customer):
    st.session_state["media_view"] = "📸 ថតហាង"
    st.session_state["media_customer"] = customer


def _media_plan_body(stats, names, zone_map, shoots, today):
    day = _media_next_shoot_day(today)
    is_day = today.weekday() in MEDIA_DAYS
    st.markdown(f"#### 📅 ថ្ងៃថត: **{'ថ្ងៃនេះ' if is_day else 'ថ្ងៃសុក្រ'} {day:%d %b}** " +
                ("· ថ្ងៃសៅរ៍បន្ទាប់" if day.weekday() == 4 and is_day else ""))
    plan = _media_priority(stats, names, zone_map, shoots, today)
    st.session_state["media_why"] = dict(zip(plan["Customer"].map(norm_name), plan["Why"])) if not plan.empty else {}
    if plan.empty:
        st.success("គ្មានហាងត្រូវថតទេ — ហាងទាំងអស់មានរូបថ្មីហើយ។ 🎉")
        return
    week_start = pd.Timestamp(today - timedelta(days=today.weekday()))
    done_week = shoots[shoots["_dt"] >= week_start] if not shoots.empty else shoots
    c1, c2, c3, c4 = st.columns(4)
    c1.metric("ហាងត្រូវថត", f"{len(plan)}")
    c2.metric("🆕 ទូថ្មី / អតិថិជនថ្មី", f"{int(plan['_new'].sum())}")
    c3.metric("ថតរួចសប្តាហ៍នេះ", f"{done_week['Customer'].map(norm_name).nunique() if not done_week.empty else 0}")
    c4.metric("រូប / វីដេអូ សប្តាហ៍នេះ",
              f"{sum(len([x for x in str(p).split(';') if x and x != '-']) for p in done_week.get('Photos', []))} / "
              f"{sum(len([x for x in str(p).split(';') if x and x != '-']) for p in done_week.get('Videos', []))}")
    only_new = st.toggle("🆕 បង្ហាញតែ ទូថ្មី និង អតិថិជនថ្មី", key="media_only_new")
    view = plan[plan["_new"]] if only_new else plan
    pz = {k: zone_map.get(norm_name(c), VISIT_ZONE_NOT_SET) for k, c in zip(view["Customer"].map(norm_name), view["Customer"])}
    zone = _visit_zone_picker(pz, "media_zone", due=Counter(view["Zone"]))
    if zone:
        view = view[view["Zone"] == zone]
    st.caption(f"{len(view)} ហាង · ចុច ▶ ដើម្បីថត និងបញ្ចូលរូប។ ហាងបាត់ពីបញ្ជីវិញ ពេលថតរួច។")
    registry, store = _visit_registry(), _visit_pin_store()
    try:
        auto = _visit_candidates_for({norm_name(c): c for c in view["Customer"]}, registry)[1]
    except Exception:
        auto = {}
    for i, r in enumerate(view.head(40).to_dict("records")):
        with st.container(border=True):
            a, b, c = st.columns([5, 1.2, 1.2])
            a.markdown(f"**{r['Customer']}**  \n<small>{r['Why']}<br>📷 រូបចុងក្រោយ: {r['Last photo']} · {r['Pcs 28 days']:,} pcs/28 ថ្ងៃ</small>",
                       unsafe_allow_html=True)
            link, exact = _visit_map_link(r["Customer"], registry, store, auto)
            b.link_button("🧭 ទៅ" if exact else "🔎 រក", link, use_container_width=True)
            c.button("ថត ▶", key=f"media_go_{i}", use_container_width=True, on_click=_media_start, args=(r["Customer"],))


def _media_form_body(names, zone_map, today):
    customers = sorted(set(names.values()), key=str.casefold)
    pre = st.session_state.get("media_customer")
    idx = customers.index(pre) if pre in customers else None
    customer = st.selectbox("1️⃣ ហាង (ភ្នំពេញ)", customers, index=idx, key="media_customer_box", placeholder="វាយឈ្មោះហាង…")
    if not customer:
        st.info("ជ្រើសហាង ឬចុច ▶ ពីផែនការ។")
        return
    st.session_state["media_customer"] = customer
    if today.weekday() not in MEDIA_DAYS:
        st.caption("ℹ️ ថ្ងៃនេះមិនមែនថ្ងៃសុក្រ/សៅរ៍ទេ — នៅតែអាចបញ្ចូលបាន។")
    with st.form("media_form", clear_on_submit=True):
        photos = st.file_uploader(f"2️⃣ រូបថតហាង (រហូតដល់ {MEDIA_PHOTO_MAX})", type=["jpg", "jpeg", "png", "heic", "webp"],
                                  accept_multiple_files=True)
        videos = st.file_uploader(f"3️⃣ វីដេអូ (mp4 / mov, ≤ {MEDIA_VIDEO_MAX_MB} MB នីមួយៗ)", type=["mp4", "mov", "m4v"],
                                  accept_multiple_files=True)
        st.markdown("**4️⃣ ស្ទីគ័រ · ម៉ឺនុយ · បដា**")
        cols = st.columns(3)
        states = {item: cols[n].selectbox(MEDIA_KM[item], MEDIA_STATES, index=None, format_func=_mkm,
                                          placeholder="ជ្រើស…", key=f"media_{item}")
                  for n, item in enumerate(MEDIA_ITEMS)}
        note = st.text_area("5️⃣ កំណត់ចំណាំ (ជម្រើស)", max_chars=1000, placeholder="ឧ. ទូដាក់ខាងក្នុង ពន្លឺតិច…")
        saved = st.form_submit_button("💾 រក្សាទុក", type="primary", use_container_width=True)
    if not saved:
        return
    errs = []
    if not photos and not videos:
        errs.append("សូមបញ្ចូលរូប ឬវីដេអូយ៉ាងហោចណាស់ 1")
    if photos and len(photos) > MEDIA_PHOTO_MAX:
        errs.append(f"រូបច្រើនពេក (អតិបរមា {MEDIA_PHOTO_MAX})")
    if any(v.size > MEDIA_VIDEO_MAX_MB * 1024 * 1024 for v in (videos or [])):
        errs.append(f"វីដេអូធំពេក (អតិបរមា {MEDIA_VIDEO_MAX_MB} MB)")
    missing = [MEDIA_KM[i] for i, v in states.items() if not v]
    if missing:
        errs.append("សូមជ្រើស: " + ", ".join(missing))
    if errs:
        st.error(" · ".join(errs))
        return
    sid = f"M{now_kh():%Y%m%d-%H%M%S}-{pysecrets.token_hex(2)}"
    who = current_user() or "-"
    p_names, v_names = [], []
    prog = st.progress(0.0, text="កំពុងបញ្ចូល…")
    total = len(photos or []) + len(videos or [])
    try:
        for n, f in enumerate(photos or [], 1):
            data = _visit_photo_prepare(f.getvalue(), [customer[:40], f"{now_kh():%d/%m/%Y %H:%M} · {who}"])
            name = f"{sid}_p{n}.jpg"
            _media_save_file(name, data)
            p_names.append(name)
            prog.progress(len(p_names) / total, text=f"រូប {n}/{len(photos)}")
        for n, f in enumerate(videos or [], 1):
            ext = os.path.splitext(f.name)[1].lower() or ".mp4"
            name = f"{sid}_v{n}{ext if ext in ('.mp4', '.mov', '.m4v') else '.mp4'}"
            _media_save_file(name, f.getvalue())
            v_names.append(name)
            prog.progress((len(p_names) + len(v_names)) / total, text=f"វីដេអូ {n}/{len(videos)}")
        k = norm_name(customer)
        append_row(MEDIA_FILE, {"Date": now_str(), "Customer": customer, "ShootID": sid,
                                "Zone": zone_map.get(k, VISIT_ZONE_NOT_SET), "By": who,
                                "Photos": ";".join(p_names) or "-", "Videos": ";".join(v_names) or "-",
                                **{i: states[i] for i in MEDIA_ITEMS},
                                "Why": st.session_state.get("media_why", {}).get(k, "-"), "Note": note.strip() or "-",
                                "Shoot day": "Yes" if today.weekday() in MEDIA_DAYS else "No"})
        audit("media shoot saved", f"{customer} | {len(p_names)} photos | {len(v_names)} videos")
    except Exception as e:
        prog.empty()
        st.error("មិនអាចរក្សាទុកបានទេ: " + str(e)[:200] + (" — រូបដែលបានបញ្ចូលរួច: " + str(len(p_names)) if p_names else ""))
        return
    prog.empty()
    st.session_state.pop("media_customer", None)
    st.session_state["flash"] = f"📸 បានរក្សាទុក {customer}: {len(p_names)} រូប · {len(v_names)} វីដេអូ"
    st.session_state["media_view"] = "📋 ផែនការ ថ្ងៃសុក្រ-សៅរ៍"
    st.rerun()


def _media_show_shoot(r, key):
    st.markdown(f"**{r['Customer']}** · {str(r['Date'])[:16]} · {r['By']}")
    st.caption(" · ".join(f"{MEDIA_KM[i]}: {_mkm(str(r.get(i, '-')))}" for i in MEDIA_ITEMS)
               + (f" · 📝 {r['Note']}" if str(r.get("Note", "-")) not in ("-", "") else ""))
    photos = [p for p in str(r.get("Photos", "")).split(";") if p and p != "-"]
    if photos:
        cols = st.columns(min(3, len(photos)))
        for i, name in enumerate(photos):
            try:
                cols[i % len(cols)].image(_media_load_photo(name), use_container_width=True)
            except Exception as e:
                cols[i % len(cols)].warning(f"{name}: {str(e)[:60]}")
    videos = [v for v in str(r.get("Videos", "")).split(";") if v and v != "-"]
    for i, name in enumerate(videos):
        vk = f"{key}_v{i}"
        if st.session_state.get(vk):
            try:
                st.video(_media_load(name))
            except Exception as e:
                st.warning(f"{name}: {str(e)[:80]}")
        elif st.button(f"▶️ បើកវីដេអូ {i + 1}", key=vk + "_btn"):
            st.session_state[vk] = True
            st.rerun()


def _media_gallery_body(shoots, names):
    if shoots.empty:
        st.info("មិនទាន់មានរូបថតទេ។")
        return
    options = sorted(set(shoots["Customer"]), key=str.casefold)
    pick = st.selectbox("ហាង", options, index=None, key="media_gal_shop", placeholder="ជ្រើសហាង ដើម្បីមើលរូបទាំងអស់…")
    if pick:
        rows = shoots[shoots["Customer"].map(norm_name).eq(norm_name(pick))].sort_values("_dt", ascending=False)
        for n, r in enumerate(rows.to_dict("records")):
            with st.container(border=True):
                _media_show_shoot(r, f"mg_{n}")
        return
    st.caption("ថតចុងក្រោយ (10 ចុងក្រោយ)")
    for n, r in enumerate(shoots.sort_values("_dt", ascending=False).head(10).to_dict("records")):
        with st.container(border=True):
            _media_show_shoot(r, f"ml_{n}")


def _media_report_body(shoots, today):
    if shoots.empty:
        st.info("មិនទាន់មានទិន្នន័យ។")
        return
    s = shoots.copy()
    s["Week"] = (s["_dt"] - pd.to_timedelta(s["_dt"].dt.weekday, unit="D")).dt.strftime("%d %b")
    s["n_photo"] = s["Photos"].map(lambda p: len([x for x in str(p).split(";") if x and x != "-"]))
    s["n_video"] = s["Videos"].map(lambda p: len([x for x in str(p).split(";") if x and x != "-"]))
    s["_wk"] = s["_dt"] - pd.to_timedelta(s["_dt"].dt.weekday, unit="D")
    wk = (s.groupby(["_wk", "Week"]).agg(ហាង=("Customer", "nunique"), រូប=("n_photo", "sum"), វីដេអូ=("n_video", "sum"),
                                       ថ្ងៃសុក្រសៅរ៍=("Shoot day", lambda x: int((x == "Yes").sum())))
          .reset_index().sort_values("_wk", ascending=False).drop(columns="_wk").head(10))
    st.markdown("**📊 តាមសប្តាហ៍**")
    show_df(wk.rename(columns={"Week": "សប្តាហ៍ចាប់ពី"}))
    st.markdown("**👤 តាមបុគ្គលិក (30 ថ្ងៃ)**")
    recent = s[s["_dt"] >= pd.Timestamp(today) - pd.Timedelta(days=30)]
    show_df(recent.groupby("By").agg(ហាង=("Customer", "nunique"), រូប=("n_photo", "sum"), វីដេអូ=("n_video", "sum")).reset_index())
    last = pd.DataFrame(list(_media_last_shoot(s).values()))
    need = last[last[MEDIA_ITEMS].isin(MEDIA_NEED).any(axis=1)] if not last.empty else last
    st.markdown(f"**🖨️ ហាងត្រូវការ ស្ទីគ័រ / ម៉ឺនុយ / បដា ថ្មី ({len(need)})**")
    if need.empty:
        st.caption("គ្មាន")
    else:
        t = need[["Customer", "Date"] + MEDIA_ITEMS].copy()
        for i in MEDIA_ITEMS:
            t[i] = t[i].map(lambda v: "🖨️ ត្រូវការ" if v in MEDIA_NEED else _mkm(v))
        show_df(t.rename(columns={"Date": "ថតចុងក្រោយ", **{i: MEDIA_KM[i] for i in MEDIA_ITEMS}}))
    if has_permission("reports"):
        _lazy_excel_download("📥 Download media report (Excel)",
                             lambda: {"Shoots": s.drop(columns=["_dt", "_wk"], errors="ignore"), "By week": wk,
                                      "Needs print": need.drop(columns=["_dt"], errors="ignore") if not need.empty else need},
                             f"Media_{today}.xlsx", "media_dl")


MEDIA_VIEWS = ["📋 ផែនការ ថ្ងៃសុក្រ-សៅរ៍", "📸 ថតហាង", "🖼️ រូបភាពហាង", "📊 របាយការណ៍"]


def _media_body():
    today = today_kh()
    st.subheader("📸 Media Team — ថតរូប និងវីដេអូ ហាងភ្នំពេញ (ថ្ងៃសុក្រ · សៅរ៍)")
    if st.session_state.get("media_view") not in MEDIA_VIEWS:
        st.session_state["media_view"] = MEDIA_VIEWS[0]
    view = st.radio("Media", MEDIA_VIEWS, key="media_view", horizontal=True, label_visibility="collapsed")
    shoots = _media_read()
    if view == "🖼️ រូបភាពហាង":
        _media_gallery_body(shoots, {})
        return
    if view == "📊 របាយការណ៍":
        _media_report_body(shoots, today)
        return
    snap, _src, _path, err = current_snapshot()
    if snap:
        try:
            _si_prepare(snap)                       # journal remarks (ទូថ្មី, X STAND…) for the priority list
        except Exception:
            pass
    stats, names, _areas = _visit_customer_stats()
    if not names:
        st.warning("រកមិនឃើញអតិថិជននៅភ្នំពេញទេ។ " + (err or ""))
        return
    zone_map = _visit_zone_map(names)
    if view == "📸 ថតហាង":
        _media_form_body(names, zone_map, today)
    else:
        _media_plan_body(stats, names, zone_map, shoots, today)


@st.fragment
def _media_fragment():
    _media_body()


def tab_media():
    """Runs as a fragment: taps inside redraw only this section."""
    try:
        _media_fragment()
    except Exception as e:
        if "fragment" in str(e).lower():
            _media_body()
        else:
            raise


ROLE = require_login()                     # nothing below runs until the person is logged in
_visit_read_gps_params()                   # a shop check-in comes back in the address bar
if "main_section" not in st.session_state:  # new session (phone woke up / reconnected) with an unfinished visit
    try:
        _dp = _vf_draft_path(current_user())
        if os.path.exists(_dp) and time.time() - os.path.getmtime(_dp) < VF_DRAFT_KEEP_H * 3600:
            st.session_state["main_section"] = "🏪 Shop Visits"
    except Exception:
        pass

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
if ROLE in ("admin", "staff", "sales"):
    labels.append("📝 Sale Order")
if _perms.get("view"):
    labels.append("📊 Live Dashboard (Sales)")
    labels.append("📍 Customer Map")
    labels.append("🎯 Sales Insights")
elif _perms.get("reports"):
    labels.append("📑 Reports")
if _perms.get("view") or _perms.get("reports"):
    labels.append("📞 Customer Follow-ups")
if ROLE in ("admin", "staff", "sales") and (_perms.get("edit") or _perms.get("reports")):
    labels.append("🏪 Shop Visits")
    labels.append("📸 Media Team")
if ROLE == "admin":
    labels.append("🤖 4. Admin: Bot, Users & Security")
if not labels:
    st.warning("No app sections are enabled for your account. Ask Admin to turn on Tasks, View, or Reports.")
    st.stop()
followup_alert_banner()

# Render only the selected section. Ordinary tabs execute every section on each rerun.
if st.session_state.get("main_section") not in labels:
    st.session_state["main_section"] = labels[0]
_label = st.radio("Open section", labels, key="main_section", horizontal=True)
st.caption("Save your form before changing sections. Only the selected section loads.")
if _label.startswith("📦"):
    tab_packing()
elif _label.startswith("🚚"):
    tab_dispatch()
elif _label.startswith("📝"):
    tab_sale_order()
elif _label.startswith("📊"):
    _live = st.checkbox(f"🔄 Live mode (refresh every {LIVE_REFRESH_SECONDS}s)", value=False, key="live_mode")
    tab_dashboard(_live)
elif _label.startswith("📑"):
    tab_dashboard(False)
elif _label.startswith("📍"):
    tab_customer_map()
elif _label.startswith("🎯"):
    tab_sales_insights()
elif _label.startswith("📞"):
    tab_followups()
elif _label.startswith("🏪"):
    tab_shop_visits()
elif _label.startswith("📸"):
    tab_media()
else:
    tab_bot()
