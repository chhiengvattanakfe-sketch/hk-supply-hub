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
LOG_PUSH_DELAY = 10                                                # seconds before logs are copied to Dropbox
CACHE_DIR = os.path.join(tempfile.gettempdir(), "hk_supply_hub_cache")       # outside Dropbox = faster
CODES_DIR = os.path.join(os.path.expanduser("~"), ".hk_supply_hub")          # access codes live OUTSIDE Dropbox
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
SNAPSHOT_VERSION = 3                   # change this number to force the journal to be re-read
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
FOR_SALE_TEAM = ["For Sale (Team 1)", "For Sale (Team 2)"]
ALL_STAFF_DRIVERS = OPS_STAFF + LOCAL_DRIVERS + FOR_SALE_TEAM
DISPATCH_COLS = ["Date", "Handled_By", "Customer", "Cases", "Local_Driver",
                 "Taxi_Station", "Phnom_Penh_Expense", "Taxi_Expense", "Note", "Verified_By"]
DISPATCH_NUM_COLS = ["Cases", "Phnom_Penh_Expense", "Taxi_Expense"]
PACKING_COLS = ["Date", "Prepared_By", "Customer", "Cases_Packed", "Status"]
PACKING_NUM_COLS = ["Cases_Packed"]
NUM_COLS_ALL = set(DISPATCH_NUM_COLS + PACKING_NUM_COLS)
FILES = {
    "dispatch": (DATA_FILE, DISPATCH_COLS, DISPATCH_NUM_COLS, "Dispatch CSV"),
    "packing": (PACKING_FILE, PACKING_COLS, PACKING_NUM_COLS, "Packing CSV"),
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
AUDIT_COLS = ["Time", "Role", "Client", "Event", "Detail"]
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
def audit(event, detail=""):
    _append_log(AUDIT_FILE, AUDIT_COLS,
                [now_str(), current_role() or "-", client_id(), event, safe_text(detail, 200)], keep=2000, max_bytes=800_000)
def _stored_code(filename):
    """Access codes that are not set in secrets.toml are created once as random codes in your user folder."""
    path = os.path.join(CODES_DIR, filename)
    try:
        with open(path, "r", encoding="utf-8") as f:
            v = f.read().strip()
        if v:
            return v
    except OSError:
        pass
    code = "".join(pysecrets.choice("ABCDEFGHJKMNPQRSTUVWXYZ23456789") for _ in range(8))
    try:
        os.makedirs(CODES_DIR, exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write(code + "\n")
        try:
            os.chmod(path, 0o600)
        except OSError:
            pass
    except OSError:
        pass
    return code
def get_codes():
    """(admin, staff, viewer). viewer is optional (empty = no read-only login)."""
    admin = _secret("ADMIN_PASSWORD") or _stored_code("admin_code.txt")
    staff = _secret("APP_PASSWORD") or _stored_code("staff_code.txt")
    viewer = _secret("VIEWER_PASSWORD")
    return admin, staff, viewer
@st.cache_resource(show_spinner=False)
def _login_guard():
    return {"fails": {}, "locked": {}, "lock": threading.Lock()}
def _try_login(code):
    guard, cid, now = _login_guard(), client_id(), time.time()
    with guard["lock"]:
        locked_until = guard["locked"].get(cid, 0)
    if locked_until > now:
        st.error(f"Too many wrong codes. Please wait {int((locked_until - now) // 60) + 1} minute(s) and try again.")
        audit("login_blocked", "client is locked out")
        return
    admin, staff, viewer = get_codes()
    given = (code or "").strip().encode()
    matched = {r: bool(c) and hmac.compare_digest(given, c.encode())
               for r, c in (("viewer", viewer), ("staff", staff), ("admin", admin))}
    role = next((r for r in ("viewer", "staff", "admin") if matched[r]), None)   # lowest privilege wins
    if role:
        with guard["lock"]:
            guard["fails"].pop(cid, None)
        st.session_state["role"] = role
        st.session_state["login_time"] = time.time()
        audit("login", role)
        st.rerun()
    with guard["lock"]:
        guard["fails"][cid] = guard["fails"].get(cid, 0) + 1
        if guard["fails"][cid] >= MAX_FAILS:
            guard["locked"][cid] = time.time() + LOCKOUT_MIN * 60
            guard["fails"][cid] = 0
    audit("login_failed", "wrong code")
    time.sleep(1)                                            # slows down guessing
    st.error("❌ Wrong access code.")
def require_login():
    """Shows the login page and stops the app until the person is logged in. Returns the role."""
    if USE_DROPBOX and not (_secret("ADMIN_PASSWORD") and _secret("APP_PASSWORD")):
        st.error("🔐 Setup needed: add ADMIN_PASSWORD and APP_PASSWORD to the app Secrets "
                 "(online mode cannot create access codes by itself), then reboot the app.")
        st.stop()
    role = st.session_state.get("role")
    if role and time.time() - st.session_state.get("login_time", 0) < LOGIN_TTL_HOURS * 3600:
        return role
    if role:
        audit("logout", "session expired")
        st.session_state.pop("role", None)
    st.markdown("<div style='height:8vh'></div>", unsafe_allow_html=True)
    _, mid, _ = st.columns([1, 2, 1])
    with mid:
        st.markdown("## 🔐 នំប៉ាវហុងកុង Hub")
        st.caption("Enter your access code to continue.")
        with st.form("login_form"):
            code = st.text_input("Access code", type="password", max_chars=64)
            go = st.form_submit_button("Log in", type="primary")
        if go:
            _try_login(code)
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
            for f in (DATA_FILE, PACKING_FILE):
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
            for f in (DATA_FILE, PACKING_FILE):
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
def _append_local(path, row):
    """Appends one row to the local file, keeping the column order of the existing file."""
    with file_lock(path):
        exists = os.path.exists(path) and os.path.getsize(path) > 0
        if not exists:
            pd.DataFrame([row]).to_csv(path, index=False, encoding="utf-8-sig")
            return
        header = list(pd.read_csv(path, nrows=0, encoding="utf-8-sig").columns)
        if set(row) <= set(header):
            with open(path, "rb") as fh:                       # file must end with a newline
                fh.seek(-1, os.SEEK_END)
                needs_nl = fh.read(1) not in (b"\n", b"\r")
            if needs_nl:
                with open(path, "ab") as fh:
                    fh.write(b"\r\n")
            ordered = {c: row.get(c, "-") for c in header}
            pd.DataFrame([ordered]).to_csv(path, mode="a", header=False, index=False, encoding="utf-8-sig")
        else:                                                  # file lacks some columns -> rewrite once
            df = pd.read_csv(path, encoding="utf-8-sig")
            df = pd.concat([df, pd.DataFrame([row])], ignore_index=True)
            df.to_csv(path, index=False, encoding="utf-8-sig")
def append_row(path, row):
    """Add ONE row (text is cleaned first). Online: downloads the latest file, adds the row, uploads it
    with a version check, and retries if somebody else saved at the same moment."""
    row = {k: (v if k == "Date" or not isinstance(v, str) else safe_text(v)) for k, v in row.items()}
    if not USE_DROPBOX:
        _retry(lambda: _append_local(path, row))
        return
    last = None
    for attempt in range(6):
        try:
            with _sync_state()["lock"]:
                pull(path, force=True)
                _append_local(path, row)
                push(path)
            return
        except ConflictError as e:
            last = e
            time.sleep(0.2 * (attempt + 1))
    raise RuntimeError("Dropbox is busy - please press Save again") from last
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
        col_idx, seen = None, set()
        name_to_region = {}  # NEW: Region Map
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
                    seen.add(n)
                    reg = "Phnom Penh" 
                    for val in row:
                        if val is not None:
                            v_str = str(val).strip().lower()
                            if v_str == "province":
                                reg = "Province"
                                break
                            elif v_str == "phnom penh":
                                reg = "Phnom Penh"
                                break
                    name_to_region[n] = reg
        customers = sorted(seen)
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
    return {"customers": customers, "regions": name_to_region, "journal": journal, "cases_col_found": cases_col is not None,
            "invoice_col_found": inv_col is not None}
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
        admin, staff, viewer = get_codes()
        if admin == staff:
            add("warn", "Security", "Admin and staff use the SAME access code", "give admin its own code")
        if min(len(admin), len(staff)) < 6:
            add("warn", "Security", "An access code is shorter than 6 characters", "use a longer code")
        n_fail = failed_logins(1)
        if n_fail >= 15:
            add("warn", "Security", f"{n_fail} wrong-code login attempts in the last hour", "see Audit log; consider changing codes")
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
@media (max-width: 640px) {
  .block-container {padding-left: .7rem; padding-right: .7rem;}
  h1 {font-size: 1.45rem !important;}
}
</style>
"""
def show_df(df, height=None, key=None, selectable=False, column_config=None):
