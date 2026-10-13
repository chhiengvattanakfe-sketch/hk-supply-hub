# ============================================================
#  នំប៉ាវហុងកុង Supply Chain Hub  -  V3 CLOUD EDITION (Dropbox + Bot)
# ============================================================
import streamlit as st
import pandas as pd
import os
import io
import re
import csv
import time
import hmac
import traceback
import contextlib
import threading
import difflib
from datetime import datetime, date, timedelta
from zoneinfo import ZoneInfo
import dropbox

if not hasattr(st, "fragment"):
    def _fragment_shim(func=None, **kwargs):
        return func if func is not None else (lambda f: f)
    st.fragment = _fragment_shim

import warnings
warnings.filterwarnings("ignore", category=UserWarning, module="openpyxl")
warnings.filterwarnings("ignore", message=".*Could not infer format.*")
warnings.filterwarnings("ignore", message=".*Parsing dates.*")

# ==========================================
# SECRETS & CLOUD CONFIGURATION
# ==========================================
def get_secret(key, default=""):
    try: return st.secrets[key]
    except Exception: return default

DBX_APP_KEY = get_secret("DROPBOX_APP_KEY")
DBX_APP_SECRET = get_secret("DROPBOX_APP_SECRET")
DBX_REFRESH_TOKEN = get_secret("DROPBOX_REFRESH_TOKEN")
ADMIN_PASSWORD = get_secret("ADMIN_PASSWORD", "hk2026")
APP_PASSWORD = get_secret("APP_PASSWORD", "staff2026")
VIEWER_PASSWORD = get_secret("VIEWER_PASSWORD", "")

# Dropbox Cloud Paths (Saving straight to your 4- Sale Jounal folder)
# Dropbox Cloud Paths (TESTING STATE)
DBX_EXCEL_PATH = "/dropbox/4- Sale Jounal/Test_Environment/10_Sale_Journal_OCT_2026.xlsx"
DBX_DATA_PATH = "/dropbox/4- Sale Jounal/Test_Environment/test_daily_delivery.csv"
DBX_PACKING_PATH = "/dropbox/4- Sale Jounal/Test_Environment/test_daily_packing.csv"
DBX_AUDIT_PATH = "/dropbox/4- Sale Jounal/Test_Environment/test_audit_log.csv"
DBX_BOT_LOG_PATH = "/dropbox/4- Sale Jounal/Test_Environment/test_bot_log.csv"

# Excel Headers
SHEET_NAME = "Master List"
JOURNAL_SHEET = "DAILY SALE JOUNAL"
COLUMN_NAME = "Customer Name"
JOURNAL_HEADER_TEXT = "ឈ្មោះអតិថិជន"
JOURNAL_CASES_HEADER = "កេស"          
JOURNAL_INVOICE_HEADER = "វិក្កយបត្រ"
JOURNAL_REMARK_HEADER = "ចំណាំ"
INVOICE_PREFIX = "NP"
URGENT_WORDS = ["ប្រញាប់", "URGENT"]

TZ = ZoneInfo("Asia/Phnom_Penh")
DAYFIRST = True                        

BOT_INTERVAL_MIN = 30
LIVE_REFRESH_SECONDS = 20

# Security
LOGIN_TTL_HOURS = 12
MAX_FAILS = 5
LOCKOUT_MIN = 5
MAX_CASES = 10000
MAX_RIEL = 50_000_000
MAX_TEXT = 200

# Teams
LOCAL_DRIVERS = ["ងិន វុទ្ធា", "អួន តួ"]
OPS_STAFF = ["ឆែម សំណុក", "សាយ ប៊ុនលី", "ប៉ៅ រីណា", "ពេជ រដ្ឋា", "រ៉ូ សុវណ្ណាឌែន", "ហេង រតនា", "កង សៀន", "ណាត ផានិត"]
FOR_SALE_TEAM = ["For Sale (Team 1)", "For Sale (Team 2)"]
ALL_STAFF_DRIVERS = OPS_STAFF + LOCAL_DRIVERS + FOR_SALE_TEAM

DISPATCH_COLS = ["Date", "Handled_By", "Customer", "Cases", "Local_Driver",
                 "Taxi_Station", "Phnom_Penh_Expense", "Taxi_Expense", "Note", "Verified_By"]
DISPATCH_NUM_COLS = ["Cases", "Phnom_Penh_Expense", "Taxi_Expense"]
PACKING_COLS = ["Date", "Prepared_By", "Customer", "Cases_Packed", "Status"]
PACKING_NUM_COLS = ["Cases_Packed"]
NUM_COLS_ALL = set(DISPATCH_NUM_COLS + PACKING_NUM_COLS)

FILES = {
    "dispatch": (DBX_DATA_PATH, DISPATCH_COLS, DISPATCH_NUM_COLS, "Dispatch CSV"),
    "packing": (DBX_PACKING_PATH, PACKING_COLS, PACKING_NUM_COLS, "Packing CSV"),
}

STATUS_RANK = {"✅ Sent": 1, "🔵 Partial": 2, "🟡 Ready for Delivery": 3, "🟠 Packing": 4, "⏳ Pending": 5}
ROLE_LABEL = {"admin": "Admin", "staff": "Staff", "viewer": "Viewer (read-only)"}

# ==========================================
# DROPBOX ENGINE (Replaces Local OS)
# ==========================================
@st.cache_resource(show_spinner=False)
def get_dbx():
    if not DBX_REFRESH_TOKEN:
        st.error("Missing Dropbox API credentials in Streamlit Secrets.")
        st.stop()
    return dropbox.Dropbox(app_key=DBX_APP_KEY, app_secret=DBX_APP_SECRET, oauth2_refresh_token=DBX_REFRESH_TOKEN)

dbx = get_dbx()

def download_csv_from_dbx(dbx_path, cols):
    try:
        _, res = dbx.files_download(dbx_path)
        df = pd.read_csv(io.BytesIO(res.content), dtype=str, keep_default_na=False, encoding="utf-8-sig")
    except dropbox.exceptions.ApiError:
        df = pd.DataFrame(columns=cols)
    except Exception as e:
        df = pd.DataFrame(columns=cols)

    for c in cols:
        if c not in df.columns: df[c] = "0" if c in NUM_COLS_ALL else "-"
    for c in df.columns:
        df[c] = df[c].astype(str).str.strip()
    for c in cols:
        if c == "Date": continue
        if c in NUM_COLS_ALL:
            df[c] = pd.to_numeric(df[c], errors="coerce").fillna(0).round().astype(int)
        else:
            df[c] = df[c].replace({"": "-", "nan": "-", "NaN": "-", "None": "-"})
            if c == "Customer": df[c] = df[c].str.replace(r"\s+", " ", regex=True)
    df["_dt"] = parse_dates(df["Date"])
    return df.reset_index(drop=True)

def upload_csv_to_dbx(df, dbx_path):
    out = df.drop(columns=[c for c in ("_dt",) if c in df.columns])
    csv_str = out.to_csv(index=False, encoding="utf-8-sig")
    try:
        dbx.files_upload(csv_str.encode('utf-8-sig'), dbx_path, mode=dropbox.files.WriteMode("overwrite"))
    except Exception as e:
        st.error(f"Error saving to Dropbox: {e}")

def read_raw(dbx_path, cols):
    return download_csv_from_dbx(dbx_path, cols)

def save_csv(dbx_path, df):
    upload_csv_to_dbx(df, dbx_path)

def append_row(dbx_path, row):
    cols = DISPATCH_COLS if "delivery" in dbx_path.lower() else PACKING_COLS
    df = download_csv_from_dbx(dbx_path, cols)
    ordered_row = {c: row.get(c, "-" if c not in NUM_COLS_ALL else 0) for c in cols}
    df = pd.concat([df, pd.DataFrame([ordered_row])], ignore_index=True)
    upload_csv_to_dbx(df, dbx_path)

# ==========================================
# TIME HELPERS
# ==========================================
def now_kh(): return datetime.now(TZ)
def today_kh(): return now_kh().date()
def now_str(): return now_kh().strftime("%Y-%m-%d %H:%M:%S")

def _try_parse(s, dayfirst):
    try:
        t = pd.to_datetime(s, dayfirst=dayfirst, errors="coerce")
        return None if pd.isna(t) else pd.Timestamp(t)
    except Exception: return None

def parse_dt(v):
    if isinstance(v, (datetime, pd.Timestamp)): return pd.Timestamp(v)
    s = str(v).strip()
    if not s or s.lower() in ("nan", "nat", "-", "none"): return pd.NaT
    if re.match(r"^\d{4}[-/]\d{1,2}[-/]\d{1,2}", s):
        t = _try_parse(s, False)
        return pd.NaT if t is None else t
    us, eu = _try_parse(s, False), _try_parse(s, True)
    if us is None and eu is None: return pd.NaT
    if us is None: return eu
    if eu is None or us == eu: return us
    today = pd.Timestamp(today_kh())
    return us if abs((us - today).days) <= abs((eu - today).days) else eu

def parse_dates(series):
    s = series.astype(str).str.strip()
    out = pd.to_datetime(s, format="%Y-%m-%d %H:%M:%S", errors="coerce")
    bad = out.isna()
    if bad.any(): out.loc[bad] = pd.to_datetime(s[bad].map(parse_dt), errors="coerce")
    return out

def cell_to_date(v, dominant=None):
    if v is None: return None
    if isinstance(v, (datetime, pd.Timestamp)): return v.date()
    if isinstance(v, date): return v
    s = str(v).strip()
    if not s: return None
    if re.match(r"^\d{4}[-/]\d{1,2}[-/]\d{1,2}", s):
        t = _try_parse(s, False)
        return None if t is None else t.date()
    us, eu = _try_parse(s, False), _try_parse(s, True)
    if us is None and eu is None: return None
    if us is None: return eu.date()
    if eu is None or us == eu: return us.date()
    if dominant:
        if (us.year, us.month) == dominant: return us.date()
        if (eu.year, eu.month) == dominant: return eu.date()
    return (eu if DAYFIRST else us).date()

def norm_name(s): return re.sub(r"\s+", " ", str(s)).strip().casefold()

def rows_for_day(df, target_date):
    if df.empty or "_dt" not in df.columns: return df.iloc[0:0].copy()
    mask = df["_dt"].dt.normalize() == pd.Timestamp(target_date)
    out = df[mask].copy()
    out["Time"] = out["_dt"].dt.strftime("%I:%M %p")
    return out

# ==========================================
# SECURITY & CLOUD AUDIT LOGS
# ==========================================
_CTRL = re.compile(r"[\x00-\x08\x0b-\x1f\x7f]")
_PHONE = re.compile(r"[+\-]?[\d\s().\-]+")

def safe_text(v, maxlen=MAX_TEXT):
    s = _CTRL.sub(" ", str(v)).replace("\r", " ").replace("\n", " ").strip()[:maxlen]
    if s and (s[0] in "=@" or (s[0] in "+-" and not _PHONE.fullmatch(s))): s = "'" + s
    return s

BOT_LOG_COLS = ["Time", "Level", "Check", "Message", "Action"]
AUDIT_COLS = ["Time", "Role", "Client", "Event", "Detail"]

def _append_log_cloud(path, cols, row):
    try:
        try:
            _, res = dbx.files_download(path)
            df = pd.read_csv(io.BytesIO(res.content), encoding="utf-8-sig")
        except:
            df = pd.DataFrame(columns=cols)
        
        new_row = pd.DataFrame([row], columns=cols)
        df = pd.concat([df, new_row], ignore_index=True).tail(500)
        csv_str = df.to_csv(index=False, encoding="utf-8-sig")
        dbx.files_upload(csv_str.encode('utf-8-sig'), path, mode=dropbox.files.WriteMode("overwrite"))
    except: pass

def bot_log(level, check, message, action="-"):
    _append_log_cloud(DBX_BOT_LOG_PATH, BOT_LOG_COLS, [now_str(), level, check, message, action])

def client_id(): return "cloud-user"

def current_role(): return st.session_state.get("role")

def audit(event, detail=""):
    _append_log_cloud(DBX_AUDIT_PATH, AUDIT_COLS, [now_str(), current_role() or "-", client_id(), event, safe_text(detail, 200)])

def get_codes():
    return ADMIN_PASSWORD, APP_PASSWORD, VIEWER_PASSWORD

@st.cache_resource(show_spinner=False)
def _login_guard():
    return {"fails": {}, "locked": {}, "lock": threading.Lock()}

def _try_login(code):
    guard, cid, now = _login_guard(), client_id(), time.time()
    with guard["lock"]:
        locked_until = guard["locked"].get(cid, 0)
    if locked_until > now:
        st.error(f"Too many wrong codes. Please wait {int((locked_until - now) // 60) + 1} minute(s) and try again.")
        return
    admin, staff, viewer = get_codes()
    given = (code or "").strip().encode()
    matched = {r: bool(c) and hmac.compare_digest(given, c.encode()) for r, c in (("viewer", viewer), ("staff", staff), ("admin", admin))}
    role = next((r for r in ("viewer", "staff", "admin") if matched[r]), None)
    if role:
        with guard["lock"]: guard["fails"].pop(cid, None)
        st.session_state["role"] = role
        st.session_state["login_time"] = time.time()
        audit("login", role)
        st.rerun()
    with guard["lock"]:
        guard["fails"][cid] = guard["fails"].get(cid, 0) + 1
        if guard["fails"][cid] >= MAX_FAILS:
            guard["locked"][cid] = time.time() + LOCKOUT_MIN * 60
            guard["fails"][cid] = 0
    time.sleep(1)
    st.error("❌ Wrong access code.")

def require_login():
    role = st.session_state.get("role")
    if role and time.time() - st.session_state.get("login_time", 0) < LOGIN_TTL_HOURS * 3600: return role
    if role:
        st.session_state.pop("role", None)
    st.markdown("<div style='height:8vh'></div>", unsafe_allow_html=True)
    _, mid, _ = st.columns([1, 2, 1])
    with mid:
        st.markdown("## 🔐 នំប៉ាវហុងកុង Hub")
        st.caption("Enter your access code to continue.")
        with st.form("login_form"):
            code = st.text_input("Access code (staff2026)", type="password", max_chars=64)
            go = st.form_submit_button("Log in", type="primary")
        if go: _try_login(code)
    st.stop()

# ==========================================
# EXCEL JOURNAL SNAPSHOT (CLOUD)
# ==========================================
def _cell_text(v):
    if v is None: return ""
    if isinstance(v, float) and v.is_integer(): return str(int(v))
    if isinstance(v, (datetime, date)): return v.strftime("%Y-%m-%d")
    s = re.sub(r"\s+", " ", str(v)).strip()
    return "" if s.lower() in ("nan", "none", "nat") else s

def _find_invoice(row, inv_col):
    """Smart Search: Looks for NP followed ONLY by numbers (e.g., NP312578) to ignore NPHK-00018"""
    if inv_col is not None and inv_col < len(row):
        s = _cell_text(row[inv_col])
        if s: return s
    for c_i in range(2, len(row)):
        v = row[c_i]
        if isinstance(v, str):
            s = v.strip().upper()
            if re.match(r"^" + re.escape(INVOICE_PREFIX.upper()) + r"\d+$", s): return s
    return "-"

@st.cache_data(ttl=60, show_spinner=False)
def current_snapshot():
    try:
        _, res = dbx.files_download(DBX_EXCEL_PATH)
        excel_bytes = io.BytesIO(res.content)
        df_cust = pd.read_excel(excel_bytes, sheet_name=SHEET_NAME)
        customers = sorted({str(x).strip() for x in df_cust[COLUMN_NAME].dropna() if str(x).strip()})
        
        excel_bytes.seek(0)
        from openpyxl import load_workbook
        wb = load_workbook(excel_bytes, read_only=True, data_only=True)
        ws = wb[JOURNAL_SHEET]
        
        raw_rows = []
        cases_col = inv_col = rem_col = None
        for r_i, row in enumerate(ws.iter_rows(values_only=True)):
            if r_i < 15 and (cases_col is None or inv_col is None or rem_col is None):
                for c_i, v in enumerate(row):
                    if v is None: continue
                    sv = str(v)
                    if cases_col is None and JOURNAL_CASES_HEADER in sv: cases_col = c_i
                    elif inv_col is None and JOURNAL_INVOICE_HEADER in sv: inv_col = c_i
                    elif rem_col is None and JOURNAL_REMARK_HEADER in sv: rem_col = c_i
            if len(row) < 2 or row[1] is None: continue
            name = re.sub(r"\s+", " ", str(row[1])).strip()
            if not name or name == JOURNAL_HEADER_TEXT: continue
            qty = row[cases_col] if (cases_col is not None and cases_col < len(row)) else None
            inv = _find_invoice(row, inv_col)
            rem = _cell_text(row[rem_col]) if (rem_col is not None and rem_col < len(row)) else ""
            raw_rows.append((row[0], name, qty, inv, rem or "-"))
        wb.close()
        
        from collections import Counter
        months = Counter((r[0].year, r[0].month) for r in raw_rows if isinstance(r[0], datetime))
        dominant = months.most_common(1)[0][0] if months else None
        out = []
        for v, name, qty, inv, rem in raw_rows:
            d = cell_to_date(v, dominant)
            if d is None: continue
            try: q = pd.to_numeric(qty, errors="coerce")
            except: q = None
            out.append((d, name, q if pd.notna(q) else None, inv, rem))
            
        journal = pd.DataFrame(out, columns=["Date", "Customer", "Cases", "Invoice", "Remark"])
        journal["Cases"] = pd.to_numeric(journal["Cases"], errors="coerce")
        snap = {"customers": customers, "journal": journal, "cases_col_found": cases_col is not None, "invoice_col_found": inv_col is not None}
        return snap, "fresh", DBX_EXCEL_PATH, None
    except Exception as e:
        return None, None, DBX_EXCEL_PATH, str(e)

def get_customer_list():
    snap, _, _, err = current_snapshot()
    if snap and snap["customers"]: return snap["customers"]
    return [f"⚠️ Error: {err or 'Master List is empty'}"]

# ==========================================
# 🤖 HEALTH BOT (CLOUD VERSION)
# ==========================================
LEVEL_ICON = {"ok": "✅ OK", "fixed": "🔧 Fixed", "warn": "⚠️ Warning", "error": "❌ Error", "info": "ℹ️ Info"}

def run_health_check(auto_fix=True):
    findings, suggestions = [], []
    def add(level, check, message, action="-"):
        findings.append({"Level": LEVEL_ICON[level], "Check": check, "Message": message, "Action": action})
        if level in ("fixed", "warn", "error") and auto_fix: bot_log(level, check, message, action)

    snap, src, path, err = current_snapshot()
    if err:
        add("error", "Excel", f"Cannot read from Dropbox: {err}", "Wait for Dropbox sync, bot retries automatically")
    else:
        if not snap["customers"]: add("warn", "Excel", "Master List has no customers", "check sheet 'Master List'")
        if not snap["cases_col_found"]: add("warn", "Excel", f"No column '{JOURNAL_CASES_HEADER}' found", "ordered cases will be empty")
        if not snap.get("invoice_col_found", True): add("info", "Excel", f"No column '{JOURNAL_INVOICE_HEADER}' found; using Smart Search.", "-")

    for key, (dbx_p, cols, nums, label) in FILES.items():
        try:
            df = read_raw(dbx_p, cols)
            if df.empty:
                if auto_fix:
                    pd.DataFrame(columns=cols).to_csv("temp.csv", index=False)
                    with open("temp.csv", "rb") as f: dbx.files_upload(f.read(), dbx_p, mode=dropbox.files.WriteMode("overwrite"))
                    add("fixed", label, "File was missing or empty", "created headers on Dropbox")
            bad_dates = df.index[df["_dt"].isna()].tolist()
            if bad_dates: add("warn", label, f"{len(bad_dates)} rows have bad dates", "fix in Admin tool")
        except Exception as e:
            add("error", label, f"Check failed: {e}", "-")

    if not findings: add("ok", "All checks", "No problems found, Cloud connection is solid.", "-")
    return findings, suggestions

@st.cache_data(ttl=BOT_INTERVAL_MIN * 60, show_spinner=False)
def auto_bot(_token=0):
    try: return run_health_check(auto_fix=True)
    except Exception as e: return [{"Level": LEVEL_ICON["error"], "Check": "Bot", "Message": str(e), "Action": "-"}], []

def safe_render(fn, label):
    try: fn()
    except Exception as e:
        if current_role() == "admin": st.error(f"⚠️ Problem in {label}: {e}")
        else: st.error("⚠️ Something went wrong. Press Retry.")
        if st.button("🔁 Retry now", key=f"retry_{label}"):
            st.cache_data.clear()
            st.rerun()

# ==========================================
# UI HELPERS
# ==========================================
CSS = """
<style>
.block-container {padding-top: 1.4rem; padding-bottom: 2.5rem; max-width: 1500px;}
div[data-testid="stMetric"] {background: rgba(128,128,128,.07); border: 1px solid rgba(128,128,128,.22); border-radius: 12px; padding: 8px 14px;}
.stButton > button, .stDownloadButton > button, div[data-testid="stFormSubmitButton"] > button { border-radius: 10px; min-height: 2.7rem; font-weight: 600;}
footer {visibility: hidden;}
@media (max-width: 640px) { .block-container {padding-left: .7rem; padding-right: .7rem;} h1 {font-size: 1.45rem !important;} }
</style>
"""

def show_df(df, height=None, key=None, selectable=False, column_config=None):
    base = {"hide_index": True}
    if height: base["height"] = height
    if column_config: base["column_config"] = column_config
    sel = dict(on_select="rerun", selection_mode="single-row", key=key) if selectable else {}
    for width_kw in ({"width": "stretch"}, {"use_container_width": True}):
        try: return st.dataframe(df, **base, **width_kw, **sel)
        except: continue
    st.dataframe(df, **base)

def kpi(container, label, value):
    try: container.metric(label, value, border=True)
    except TypeError: container.metric(label, value)

def flash_and_refresh(msg):
    st.session_state["flash"] = msg
    st.session_state["clear_sel"] = True
    st.rerun()

# ==========================================
# FORMS & TAB LOGIC
# ==========================================
def dispatch_form(form_key, fixed_customer=None, default_cases=1, verify=False):
    k = form_key
    with st.form(form_key, clear_on_submit=True):
        st.markdown("#### Order Details")
        dispatched_by = st.selectbox("Dispatched By:", ["-- Select Staff --"] + ALL_STAFF_DRIVERS, key=f"{k}_by")
        if fixed_customer is None: customer_name = st.selectbox("Customer Name / ID (Type to search):", ["-- Select a Customer --"] + get_customer_list(), key=f"{k}_cust")
        else:
            customer_name = fixed_customer
            st.markdown(f"**Customer:** {fixed_customer}")
        d_cases = max(0, min(int(default_cases), MAX_CASES))
        cases = st.number_input("ចំនួនកេស (Number of Cases):", min_value=0, max_value=MAX_CASES, step=1, value=d_cases, key=f"{k}_cases_{d_cases}")
        if verify: verified_by = st.selectbox("✅ Cases verified by:", ["-- Select Staff --"] + ALL_STAFF_DRIVERS, key=f"{k}_vby")
        else: verified_by = st.selectbox("Cases verified by (optional):", ["-"] + ALL_STAFF_DRIVERS, key=f"{k}_vby")

        st.markdown("---")
        st.markdown("#### Transportation Details")
        local_driver = st.selectbox("Local Driver (Phnom Penh):", ["None (Grab/TukTuk)"] + LOCAL_DRIVERS, key=f"{k}_drv")
        taxi_station = st.text_input("Taxi Station Name:", max_chars=MAX_TEXT, key=f"{k}_taxi")
        delivery_note = st.text_input("📝 Note:", max_chars=MAX_TEXT, key=f"{k}_note")

        st.markdown("#### Expenses (៛ Riel)")
        pp_expense = st.number_input("1. Phnom Penh Expense (៛):", min_value=0, max_value=MAX_RIEL, step=500, key=f"{k}_pp")
        taxi_expense = st.number_input("2. Taxi Expense (៛):", min_value=0, max_value=MAX_RIEL, step=500, key=f"{k}_te")

        if st.form_submit_button("💾 Save Dispatch & Expenses", type="primary"):
            if dispatched_by == "-- Select Staff --": st.error("❌ Please select who dispatched this order.")
            elif customer_name == "-- Select a Customer --": st.error("❌ Please select a valid Customer Name.")
            elif cases == 0: st.error("❌ Number of cases must be at least 1.")
            else:
                handler_local = local_driver if local_driver != "None (Grab/TukTuk)" else "Grab/TukTuk"
                append_row(DBX_DATA_PATH, {
                    "Date": now_str(), "Handled_By": dispatched_by, "Customer": customer_name.strip(),
                    "Cases": cases, "Local_Driver": handler_local, "Taxi_Station": taxi_station.strip() or "-",
                    "Phnom_Penh_Expense": pp_expense, "Taxi_Expense": taxi_expense, "Note": delivery_note.strip() or "-",
                    "Verified_By": verified_by,
                })
                audit("dispatch", f"{customer_name} | {cases} cases | by {dispatched_by}")
                flash_and_refresh(f"Dispatched by {dispatched_by}: {customer_name} | {cases} កេស")

def packing_form(form_key, fixed_customer=None, default_cases=1):
    k = form_key
    with st.form(form_key, clear_on_submit=True):
        if fixed_customer is None: customer = st.selectbox("Customer Name / ID (Type to search):", ["-- Select a Customer --"] + get_customer_list(), key=f"{k}_cust")
        else:
            customer = fixed_customer
            st.markdown(f"**Customer:** {fixed_customer}")
        prepared_by = st.selectbox("Prepared / Packed By:", ["-- Select Staff --"] + ALL_STAFF_DRIVERS, key=f"{k}_by")

        col1, col2 = st.columns(2)
        with col1: cases_packed = st.number_input("ចំនួនកេស (Cases Packed):", min_value=0, max_value=MAX_CASES, step=1, value=max(0, min(int(default_cases), MAX_CASES)), key=f"{k}_cases")
        with col2: pack_status = st.radio("Status:", ["In Progress (កំពុងធ្វើ)", "Completed (រួចរាល់)"], key=f"{k}_status")

        if st.form_submit_button("💾 Save Packing Progress", type="primary"):
            if prepared_by == "-- Select Staff --": st.error("❌ Please select who is preparing this order.")
            elif customer == "-- Select a Customer --": st.error("❌ Please select a valid Customer Name.")
            elif cases_packed == 0: st.error("❌ Number of cases must be at least 1.")
            else:
                append_row(DBX_PACKING_PATH, {
                    "Date": now_str(), "Prepared_By": prepared_by, "Customer": customer.strip(),
                    "Cases_Packed": cases_packed, "Status": pack_status,
                })
                audit("packing", f"{customer} | {cases_packed} cases | by {prepared_by}")
                flash_and_refresh(f"Packing logged: {customer} | {cases_packed} cases | {pack_status}")

def admin_editor(path, cols, num_cols, key, label_cols):
    if current_role() != "admin":
        st.info("🔒 Admin only.")
        return
    df = read_raw(path, cols)
    df_today = rows_for_day(df, today_kh())
    if df_today.empty: return st.info("No entries logged for today.")
    labels = {i: f"{i}: " + " | ".join(str(df_today.loc[i, c]) for c in label_cols) for i in df_today.index}
    row_idx = st.selectbox("Select entry to correct:", list(labels.keys()), format_func=lambda i: labels[i], key=f"sel_{key}")
    current = df.loc[row_idx]
    with st.form(f"edit_form_{key}"):
        new_vals = {}
        for c in cols:
            wkey = f"{key}_{c}_{row_idx}"
            if c in num_cols:
                step = 500 if c.endswith("Expense") else 1
                new_vals[c] = st.number_input(f"Edit {c}:", min_value=0, value=int(current[c]), step=step, key=wkey)
            else: new_vals[c] = st.text_input(f"Edit {c}:", value=str(current[c]), key=wkey)
        col_upd, col_del = st.columns(2)
        if col_upd.form_submit_button("🔄 Update Record"):
            for c in cols: df.loc[row_idx, c] = new_vals[c]
            save_csv(path, df)
            audit("edit", f"#{row_idx} {current['Customer']} updated")
            flash_and_refresh("Record updated")
        if col_del.form_submit_button("🗑️ Delete Entry"):
            audit("delete", f"#{row_idx} {current['Customer']} deleted")
            save_csv(path, df.drop(row_idx))
            flash_and_refresh("Record deleted")

def _packing_body():
    st.markdown("### 📦 Bun Preparation & Packing")
    packing_form("packing_form")
    with st.expander("🛠️ Admin: Fix or Edit Today's Packing"): admin_editor(DBX_PACKING_PATH, PACKING_COLS, PACKING_NUM_COLS, "pack", ["Customer", "Cases_Packed", "Status"])
    st.markdown("---")
    st.subheader("📋 Today's Packing Log")
    df_today = rows_for_day(read_raw(DBX_PACKING_PATH, PACKING_COLS), today_kh())
    if df_today.empty: return st.info("No packing logged today yet.")
    show_df(df_today[PACKING_COLS])

@st.fragment
def tab_packing(): safe_render(_packing_body, "Packing")

def _dispatch_body():
    st.markdown("### 🚚 Log Delivery Slip")
    dispatch_form("expense_form")
    st.markdown("---")
    with st.expander("🛠️ Admin: Fix or Edit Today's Dispatches"): admin_editor(DBX_DATA_PATH, DISPATCH_COLS, DISPATCH_NUM_COLS, "disp", ["Customer", "Cases"])
    st.markdown("---")
    st.subheader("📊 Today's Operations Log")
    df_today = rows_for_day(read_raw(DBX_DATA_PATH, DISPATCH_COLS), today_kh())
    m1, m2, m3 = st.columns(3)
    kpi(m1, "Total Slips", len(df_today))
    kpi(m2, "Total Cases", int(df_today["Cases"].sum()) if not df_today.empty else 0)
    kpi(m3, "Total Expenses (៛)", f"{int(df_today['Phnom_Penh_Expense'].sum() + df_today['Taxi_Expense'].sum()):,}" if not df_today.empty else "0")
    if df_today.empty: return st.info("No deliveries logged today yet.")
    show_df(df_today[["Handled_By", "Customer", "Cases", "Note", "Local_Driver", "Taxi_Station", "Phnom_Penh_Expense", "Taxi_Expense", "Verified_By"]])

@st.fragment
def tab_dispatch(): safe_render(_dispatch_body, "Delivery")

def _join_unique(series, sep=", ", limit=3):
    vals = [v for v in dict.fromkeys(series) if v and v != "-"]
    if not vals: return "-"
    return sep.join(vals[:limit]) + (f" +{len(vals) - limit}" if len(vals) > limit else "")

DASH_COLUMNS = ["🔥", "Customer", "Invoice", "Status", "កេស", "Packed Cases", "Prepared By", "Sent Cases", "Handled By", "Verified By", "Driver/Station", "Journal Note", "Note", "Time", "Source"]

def build_report(selected_date):
    snap, _, _, err = current_snapshot()
    scheduled, cases_found = {}, False
    if snap:
        cases_found = snap["cases_col_found"]
        j = snap["journal"]
        sub = j[j["Date"] == selected_date]
        for name, g in sub.groupby("Customer", sort=False):
            tot = g["Cases"].sum(min_count=1)
            scheduled[name] = {"cases": int(tot) if pd.notna(tot) else None, "invoice": _join_unique(g["Invoice"]), "remark": _join_unique(g["Remark"], sep=" / ")}

    pack_info = {}
    for cust, g in rows_for_day(read_raw(DBX_PACKING_PATH, PACKING_COLS), selected_date).groupby("Customer", sort=False):
        pack_info[cust] = {"cases": int(g["Cases_Packed"].sum()), "by": g["Prepared_By"].iloc[-1], "status": str(g["Status"].iloc[-1])}

    sent_info = {}
    for cust, g in rows_for_day(read_raw(DBX_DATA_PATH, DISPATCH_COLS), selected_date).groupby("Customer", sort=False):
        last = g.iloc[-1]
        station = str(last["Taxi_Station"]).strip()
        sent_info[cust] = {"cases": int(g["Cases"].sum()), "driver": f"{last['Local_Driver']} ➡️ {station}" if station not in ("-", "") else str(last["Local_Driver"]), "note": str(last["Note"]), "by": str(last["Handled_By"]), "verified": str(last["Verified_By"]), "time": last["Time"]}

    rows = []
    for cust in set(scheduled) | set(pack_info) | set(sent_info):
        p, s, info = pack_info.get(cust), sent_info.get(cust), scheduled.get(cust)
        packed, sent = p["cases"] if p else 0, s["cases"] if s else 0
        ordered, remark = (info["cases"], info["remark"]) if info else (None, "-")
        target = packed if packed > 0 else (ordered or 0)
        status = "🔵 Partial" if s and (target > 0 and sent < target) else ("✅ Sent" if s else ("🟠 Packing" if p and "In Progress" in p["status"] else ("🟡 Ready for Delivery" if p else "⏳ Pending")))
        urgent = any(w.upper() in remark.upper() for w in URGENT_WORDS)
        rows.append({"🔥": "🔥" if urgent else "", "Customer": cust, "Invoice": info["invoice"] if info else "-", "Status": status, "កេស": ordered, "Packed Cases": packed, "Prepared By": p["by"] if p else "-", "Sent Cases": sent, "Handled By": s["by"] if s else "-", "Verified By": s["verified"] if s else "-", "Driver/Station": s["driver"] if s else "-", "Journal Note": remark, "Note": s["note"] if s else "-", "Time": s["time"] if s else "-", "Source": "Journal" if info else "⚠️ Not in journal"})
    
    if not rows: return pd.DataFrame(), cases_found, err
    df = pd.DataFrame(rows)
    df["កេស"] = pd.array(df["កេស"].tolist(), dtype="Int64")
    df["_r"] = df["Status"].map(STATUS_RANK)
    df["_u"] = (df["🔥"] == "").astype(int)
    return df.sort_values(by=["_r", "_u", "Customer"]).drop(columns=["_r", "_u"]).reset_index(drop=True)[DASH_COLUMNS], cases_found, err

def _dashboard_body():
    can_edit = current_role() in ("staff", "admin")
    st.markdown("### 📊 Master Status Board")
    selected_date = st.date_input("Select Report Date:", value=today_kh(), key="dash_date")
    df_report, cases_found, err = build_report(selected_date)
    if err: st.warning(f"Excel problem: {err}")
    if df_report.empty: return st.info(f"📅 No orders scheduled or found in the journal for {selected_date}.")

    counts = df_report["Status"].value_counts()
    k1, k2, k3, k4, k5 = st.columns(5)
    kpi(k1, "⏳ Pending", int(counts.get("⏳ Pending", 0)))
    kpi(k2, "🟠 Packing", int(counts.get("🟠 Packing", 0)))
    kpi(k3, "🟡 Ready", int(counts.get("🟡 Ready for Delivery", 0)))
    kpi(k4, "🔵 Partial", int(counts.get("🔵 Partial", 0)))
    kpi(k5, "✅ Sent", int(counts.get("✅ Sent", 0)))

    f1, f2, f3 = st.columns([3, 3, 2])
    q = f1.text_input("🔎 Search customer or invoice", key="dash_q")
    pick_status = f2.multiselect("Status filter", list(STATUS_RANK), key="dash_status", placeholder="All statuses")

    df_view = df_report
    if q.strip(): df_view = df_view[df_view["Customer"].str.contains(q.strip(), case=False, na=False) | df_view["Invoice"].str.contains(q.strip(), case=False, na=False)]
    if pick_status: df_view = df_view[df_view["Status"].isin(pick_status)]
    df_view = df_view.reset_index(drop=True)

    if st.session_state.pop("clear_sel", False): st.session_state.pop("dash_table", None)
    cfg = {"🔥": st.column_config.TextColumn("🔥", width="small"), "Customer": st.column_config.TextColumn("Customer", width="large"), "Invoice": st.column_config.TextColumn("Invoice", width="medium"), "Status": st.column_config.TextColumn("Status", width="medium")}
    
    if df_view.empty:
        st.info("No customers match your search / filter.")
        event = None
    else:
        event = show_df(df_view, height=430, key="dash_table", selectable=can_edit, column_config=cfg)

    if not can_edit: return
    
    rows_sel = event.selection.rows if event else []
    if rows_sel: st.session_state["sel_cust"] = df_view.iloc[rows_sel[0]]["Customer"]
    selected = st.session_state.get("sel_cust")
    if selected not in set(df_report["Customer"]): return

    st.markdown("---")
    h1, h2 = st.columns([5, 1])
    h1.subheader(f"✏️ Update: {selected}")
    if h2.button("✖ Close", key="close_panel"):
        st.session_state.pop("sel_cust", None)
        st.session_state["clear_sel"] = True
        st.rerun()

    if selected_date != today_kh(): return st.info("Updates can only be saved for today.")

    p_row = df_report[df_report["Customer"] == selected].iloc[0]
    st.info(f"Status: **{p_row['Status']}**  |  Invoice: {p_row['Invoice']}  |  កេស ordered: {p_row['កេស'] if pd.notna(p_row['កេស']) else '-'}  |  Packed: {p_row['Packed Cases']}  |  Sent: {p_row['Sent Cases']}")
    
    pack_default = max((int(p_row['កេស']) if pd.notna(p_row['កេស']) else 0) - int(p_row['Packed Cases']), 0) or 1
    t_n = int(p_row['Packed Cases']) if int(p_row['Packed Cases']) > 0 else (int(p_row['កេស']) if pd.notna(p_row['កេស']) else 0)
    send_default = (t_n - int(p_row['Sent Cases'])) if (t_n - int(p_row['Sent Cases'])) > 0 else 1

    t_pack, t_send = st.tabs(["📦 Step 1: Packing", "🚚 Step 2: Send"])
    with t_pack: packing_form(f"dash_pack_{selected}", fixed_customer=selected, default_cases=pack_default)
    with t_send: dispatch_form(f"dash_send_{selected}", fixed_customer=selected, default_cases=send_default, verify=True)

def tab_dashboard(live):
    frag = st.fragment(run_every=LIVE_REFRESH_SECONDS)(lambda: safe_render(_dashboard_body, "Dashboard")) if live else st.fragment(lambda: safe_render(_dashboard_body, "Dashboard"))
    frag()

# ==========================================
# TAB: HEALTH BOT (ADMIN ONLY)
# ==========================================
def _bot_body():
    if current_role() != "admin": return st.info("🔒 Admin only.")
    st.markdown("### 🤖 Cloud Health Bot")
    st.caption("The bot checks files and connection to Dropbox. System logs are safely stored in your '4- Sale Jounal' folder.")
    
    if st.button("🔧 Run Cloud Check", type="primary"):
        findings, _ = run_health_check(auto_fix=True)
        show_df(pd.DataFrame(findings))
        
    st.markdown("---")
    st.markdown("### 🔐 Security & Audit Log")
    try:
        _, res = dbx.files_download(DBX_AUDIT_PATH)
        df_audit = pd.read_csv(io.BytesIO(res.content), encoding="utf-8-sig").iloc[::-1]
        show_df(df_audit, height=300)
    except: st.info("No audit logs found on Dropbox yet. A new log file will be generated when a user logs in.")

@st.fragment
def tab_bot(): safe_render(_bot_body, "Bot")

# ==========================================
# APP LAYOUT
# ==========================================
st.set_page_config(page_title="Delivery Operations", page_icon="🚚", layout="wide", initial_sidebar_state="collapsed")
st.markdown(CSS, unsafe_allow_html=True)

ROLE = require_login()

if st.session_state.pop("flash", None): st.toast("✅ Action saved successfully")

with st.sidebar:
    st.markdown(f"### 👤 {ROLE_LABEL.get(ROLE, ROLE)}")
    if st.button("🚪 Log out"):
        audit("logout", "manual")
        st.session_state.clear()
        st.rerun()

st.title("🚚 នំប៉ាវហុងកុង Supply Chain Hub")

_, _, _, _err = current_snapshot()
st.caption(f"{'✅ Connected to Dropbox' if not _err else '❌ Dropbox Sync Error'}  |  🕒 {now_kh():%Y-%m-%d %I:%M %p}")

labels = ["📊 Live Dashboard"] if ROLE == "viewer" else ["📦 1. Packing Progress", "🚚 2. Log Delivery", "📊 3. Live Dashboard"]
if ROLE == "admin": labels.append("🤖 4. Health Bot & Security")

for _label, _tab in dict(zip(labels, st.tabs(labels))).items():
    with _tab:
        if _label.startswith("📦"): tab_packing()
        elif _label.startswith("🚚"): tab_dispatch()
        elif _label.startswith("📊"): tab_dashboard(st.checkbox(f"🔄 Live mode (refresh 20s)"))
        else: tab_bot()
