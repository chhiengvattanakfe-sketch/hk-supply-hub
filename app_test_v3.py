# -*- coding: utf-8 -*-
"""
នំប៉ាវហុងកុង — Production & Live Stock
==========================================
A separate Streamlit app (same GitHub repo as the Supply Hub):
  * 📊 Live stock      — stock of every bun by production date, days of stock, alerts (updates by itself)
  * 🏭 Log production  — staff enter pcs produced per bun
  * 📦 Stock count     — physical count (opening stock) + adjustments (damaged, samples, ...)
  * 📅 Next week plan  — suggested production per day from sales speed and your stock rules, Excel download
  * ⚙️ Settings        — targets, 80,000 limit, shelf life, production days, who can use the app (Admin)

Stock goes DOWN with the pcs in the sale journal (DAILY SALE JOUNAL, columns N1 ... N43, invoice date),
oldest production date first (FIFO). Stock goes UP with logged production.
Same Dropbox folder and same logins as the Supply Hub (users.json). Secrets: the same as the Supply Hub.
"""
import fnmatch
import hashlib
import hmac
import io
import json
import math
import os
import re
import threading
import time
import uuid
from datetime import date, datetime, timedelta

import secrets as pysecrets

import pandas as pd
import streamlit as st
import streamlit.components.v1 as components

try:
    from zoneinfo import ZoneInfo
    TZ = ZoneInfo("Asia/Phnom_Penh")
except Exception:                                   # pragma: no cover
    TZ = None

st.set_page_config(page_title="Production & Stock · នំប៉ាវហុងកុង", page_icon="🏭", layout="wide")

APP_DIR = os.path.dirname(os.path.abspath(__file__))
LOCAL_DIR = os.path.join(APP_DIR, "production_data")
os.makedirs(LOCAL_DIR, exist_ok=True)


def _secret(name):
    try:
        v = st.secrets[name]
        return str(v).strip() if v else ""
    except Exception:
        return os.environ.get(name, "").strip()


USE_DROPBOX = bool(_secret("DROPBOX_REFRESH_TOKEN") or _secret("DROPBOX_ACCESS_TOKEN"))
DROPBOX_FOLDER = "/" + (_secret("DROPBOX_FOLDER") or "/dropbox/4- Sale Jounal").strip().strip("/")

PROD_FILE = "production_log.csv"
COUNT_FILE = "stock_counts.csv"
ADJ_FILE = "stock_adjustments.csv"
SETTINGS_FILE = "production_settings.json"
USERS_FILE = "users.json"
REMEMBER_FILE = "production_remember.json"    # "keep me signed in": only a hash of each browser's token is stored
COOKIE = "hk_prod_rt"
URL_TOK = "p_rt"
REMEMBER_DAYS = 30
JOURNAL_PATTERN = "*_Sale_Jou*.xlsx"
JOURNAL_SHEET = "DAILY SALE JOUNAL"
BUN_RE = re.compile(r"^N\d+$")
MONTHS = ["JAN", "FEB", "MAR", "APR", "MAY", "JUN", "JUL", "AUG", "SEP", "OCT", "NOV", "DEC"]
KH_DAYS = ["ច័ន្ទ", "អង្គារ", "ពុធ", "ព្រហស្បតិ៍", "សុក្រ", "សៅរ៍", "អាទិត្យ"]
EN_DAYS = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

PROD_COLS = ["Saved_At", "Prod_Date", "Bun", "Pcs", "By", "Note", "Entry_Id", "Team"]
TASK_FILE = "production_tasks.csv"
TASK_COLS = ["Date", "Task_Id", "Assigned", "Done_By", "Done_At", "Note", "Updated_At", "Updated_By"]
AUDIT_FILE = "production_audit.csv"
AUDIT_COLS = ["Time", "User", "Name", "Action", "Detail"]
ALL_DAYS = [0, 1, 2, 3, 4, 5, 6]
DEFAULT_TASKS = [
    {"id": "prod", "name": "🏭 Log today's production", "due": "17:00", "who": [], "auto": "prod", "days": ALL_DAYS},
    {"id": "count", "name": "📦 Evening stock count", "due": "19:30", "who": [], "auto": "count", "days": ALL_DAYS},
]
COUNT_COLS = ["Saved_At", "Count_Date", "Bun", "Prod_Date", "Pcs", "By", "Count_Id", "Place"]
ADJ_COLS = ["Saved_At", "Date", "Bun", "Prod_Date", "Pcs", "Reason", "By", "Adj_Id"]
DEFAULT_BUNS = ["N1", "N2", "N21", "N22", "N23", "N3", "N31", "N32", "N34", "N4", "N41", "N42", "N43"]
PRIORITY_DEFAULT = ["N1", "N2"]
DEFAULT_SETTINGS = {
    "max_total": 80000,             # total stock (pcs) must never go above this
    "target_days": {"N1": 6, "N2": 6},
    "target_default": 5,            # every other bun
    "priority": PRIORITY_DEFAULT,   # kept at their target first when the 80,000 limit bites
    "shelf_days": 10,               # a batch older than this is flagged 'sell first / too old'
    "shelf_by_bun": {},
    "prod_days": {"N1": [0, 1, 2, 3, 4, 5, 6], "N2": [0, 1, 2, 3, 4, 5, 6]},
    "prod_days_default": [0, 1, 2, 3, 4, 5],   # Mon-Sat (Sunday off) for the others
    "lookback_days": 28,            # sales history used for the sales speed / forecast
    "round_to": 10,                 # planned pcs rounded up to this
    "max_prod_per_day": 0,          # 0 = no limit
    "access_by_role": {"staff": "edit", "sales": "view", "viewer": "view"},   # automatic, by Supply Hub role
    "access_override": {},          # username -> hidden / view / edit, only for people who differ from their role
    "access_default": "view",
    "places": ["ស្តុកនំក្នុងទូរ", "ស្តុកទូរកក"],   # freezers counted every evening (one tab each)
    "tasks": DEFAULT_TASKS,         # daily checklist (Admin adds / assigns in ⚙️ Settings and 📋 Tasks)
    "prod_staff": [],               # names offered in "👷 Produced by"
}


def now_kh():
    return datetime.now(TZ) if TZ else datetime.utcnow() + timedelta(hours=7)


def today_kh():
    return now_kh().date()


# ==========================================
# STORAGE (Dropbox or local files) — every write is "read, change, save if nobody saved in between"
# ==========================================
class Conflict(Exception):
    pass


@st.cache_resource(show_spinner=False)
def _dbx():
    import dropbox
    refresh = _secret("DROPBOX_REFRESH_TOKEN")
    if refresh:
        return dropbox.Dropbox(oauth2_refresh_token=refresh, app_key=_secret("DROPBOX_APP_KEY"),
                               app_secret=_secret("DROPBOX_APP_SECRET"), timeout=30)
    return dropbox.Dropbox(oauth2_access_token=_secret("DROPBOX_ACCESS_TOKEN"), timeout=30)


@st.cache_resource(show_spinner=False)
def _mem():
    """Shared by every visitor: file contents by revision, folder listing, locks."""
    return {"files": {}, "list": None, "list_t": 0.0, "lock": threading.RLock()}


def _listing(max_age=8):
    """{name: (rev, size, modified)} of the Dropbox folder, refreshed at most every few seconds."""
    m = _mem()
    with m["lock"]:
        if m["list"] is not None and time.time() - m["list_t"] < max_age:
            return m["list"]
    out, dbx = {}, _dbx()
    res = dbx.files_list_folder(DROPBOX_FOLDER)
    while True:
        for e in res.entries:
            if hasattr(e, "rev"):
                out[e.name] = (e.rev, e.size, e.server_modified)
        if not res.has_more:
            break
        res = dbx.files_list_folder_continue(res.cursor)
    with m["lock"]:
        m["list"], m["list_t"] = out, time.time()
    return out


def read_bytes(name, max_age=8):
    """(bytes or None, revision). Dropbox content is downloaded only when its revision changed."""
    if not USE_DROPBOX:
        p = os.path.join(LOCAL_DIR, name)
        if not os.path.exists(p):
            return None, None
        with open(p, "rb") as f:
            data = f.read()
        return data, str(os.stat(p).st_mtime_ns)
    meta = _listing(max_age).get(name)
    if meta is None:
        return None, None
    rev = meta[0]
    m = _mem()
    hit = m["files"].get(name)
    if hit and hit[0] == rev:
        return hit[1], rev
    _md, res = _dbx().files_download(f"{DROPBOX_FOLDER}/{name}")
    m["files"][name] = (rev, res.content)
    return res.content, rev


def write_bytes(name, data, rev):
    """Save only if the file is still at `rev` (None = must not exist yet). Keeps a daily backup."""
    if not USE_DROPBOX:
        p = os.path.join(LOCAL_DIR, name)
        cur = str(os.stat(p).st_mtime_ns) if os.path.exists(p) else None
        if cur != rev:
            raise Conflict(name)
        tmp = p + ".tmp"
        with open(tmp, "wb") as f:
            f.write(data)
        os.replace(tmp, p)
        return
    import dropbox
    path = f"{DROPBOX_FOLDER}/{name}"
    mode = dropbox.files.WriteMode.update(rev) if rev else dropbox.files.WriteMode.add
    m = _mem()
    day_key = (name, today_kh().isoformat())
    if rev and day_key not in m.setdefault("backed_up", set()):
        try:                                               # first save of the day keeps yesterday's version
            _dbx().files_copy_v2(path, f"{DROPBOX_FOLDER}/backups/{today_kh():%Y-%m-%d}_{name}")
        except Exception:
            pass                                           # already copied today (or no file yet)
        m["backed_up"].add(day_key)                        # only once a day: saving stays fast
    for attempt in range(3):
        try:
            md = _dbx().files_upload(data, path, mode=mode, mute=True, autorename=False)
            break
        except dropbox.exceptions.ApiError as e:
            if "conflict" in str(e).lower():
                raise Conflict(name) from e
            raise
        except Exception:                                  # network hiccup: try again, then tell the person
            if attempt == 2:
                raise RuntimeError("No connection to Dropbox — check the internet and press Save again. "
                                   "Your numbers are still on the screen.")
            time.sleep(1.0 * (attempt + 1))
    with m["lock"]:
        m["files"][name] = (md.rev, data)
        if m["list"] is not None:
            m["list"] = dict(m["list"])
            m["list"][name] = (md.rev, md.size, md.server_modified)


def read_csv(name, cols, max_age=8):
    data, rev = read_bytes(name, max_age)
    if not data:
        return pd.DataFrame(columns=cols), rev
    df = pd.read_csv(io.BytesIO(data), dtype=str, keep_default_na=False, encoding="utf-8-sig")
    for c in cols:
        if c not in df.columns:
            df[c] = ""
    return df[cols], rev


def modify_csv(name, cols, change):
    """read -> change(frame) -> save; retried if someone else saved at the same moment."""
    for attempt in range(5):
        df, rev = read_csv(name, cols, max_age=0)
        new = change(df.copy())
        try:
            write_bytes(name, new[cols].to_csv(index=False).encode("utf-8-sig"), rev)
            return new
        except Conflict:
            time.sleep(0.4 * (attempt + 1))
    raise RuntimeError("Someone else is saving the same file right now. Please press Save again.")


def load_settings():
    data, rev = read_bytes(SETTINGS_FILE)
    s = json.loads(json.dumps(DEFAULT_SETTINGS))
    if data:
        try:
            s.update(json.loads(data.decode("utf-8")))
        except Exception:
            pass
    return s, rev


def update_settings(changes):
    """Saves only the parts that changed, on top of the NEWEST settings file — so two people saving
    different parts (e.g. room sizes and stock targets) never undo each other.
    `changes` = {key: value} or a function(settings) that changes the dict."""
    for attempt in range(4):
        data, rev = read_bytes(SETTINGS_FILE, max_age=0)
        cur = {}
        if data:
            try:
                cur = json.loads(data.decode("utf-8"))
            except Exception:
                raise RuntimeError("The settings file cannot be read — nothing was changed.")
        if callable(changes):
            changes(cur)
        else:
            cur.update(changes)
        try:
            write_bytes(SETTINGS_FILE, json.dumps(cur, ensure_ascii=False, indent=1).encode("utf-8"), rev)
            return cur
        except Conflict:
            time.sleep(0.4 * (attempt + 1))
    raise RuntimeError("Settings were being saved by someone else. Try again.")


# ==========================================
# LOGIN — same accounts as the Supply Hub
# ==========================================
def load_users():
    data, _rev = read_bytes(USERS_FILE, max_age=30)
    if not data:
        return {}
    try:
        users = json.loads(data.decode("utf-8-sig")).get("users", {})
        return users if isinstance(users, dict) else {}
    except Exception:
        return {}


def audit(action, detail=""):
    """🕘 History: who did what, when. Never stops the work if it cannot be written."""
    row = {"Time": now_kh().strftime("%Y-%m-%d %H:%M:%S"), "User": st.session_state.get("p_user", ""),
           "Name": st.session_state.get("p_name", ""), "Action": action, "Detail": str(detail)[:500]}
    try:
        modify_csv(AUDIT_FILE, AUDIT_COLS, lambda df: pd.concat([df, pd.DataFrame([row])], ignore_index=True))
    except Exception:
        pass


def _hash_pw(password):
    salt = os.urandom(16)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 200_000)
    return {"salt": salt.hex(), "hash": dk.hex(), "iter": 200_000}


def modify_users(change):
    """Read-change-save of the SHARED accounts file (same accounts as the Supply Hub)."""
    for attempt in range(4):
        data, rev = read_bytes(USERS_FILE, max_age=0)
        doc = json.loads(data.decode("utf-8-sig")) if data else {"users": {}}
        if not isinstance(doc, dict) or not isinstance(doc.get("users"), dict):
            raise RuntimeError("The accounts file cannot be read safely — nothing was changed.")
        change(doc["users"])
        try:
            write_bytes(USERS_FILE, json.dumps(doc, ensure_ascii=False, indent=1).encode("utf-8"), rev)
            return
        except Conflict:
            time.sleep(0.4 * (attempt + 1))
    raise RuntimeError("Someone else is saving the accounts right now. Try again.")


def change_password(user, new_pw):
    stamp = now_kh().strftime("%Y-%m-%d %H:%M:%S")

    def ch(users):
        if user not in users:
            raise RuntimeError("Account not found.")
        users[user].update(_hash_pw(new_pw), pw_changed=stamp, must_change=False)
    modify_users(ch)
    return stamp


def _check_pw(password, rec):
    try:
        dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), bytes.fromhex(rec["salt"]), int(rec["iter"]))
        return hmac.compare_digest(dk.hex(), rec["hash"])
    except Exception:
        return False


ROLE_TITLES = {"staff": "👷 Operation staff", "sales": "💼 Sales", "viewer": "👁️ Viewer"}


def access_of(username, role, settings):
    """Admin: always edit. Everyone else: their own setting if Admin gave one, otherwise automatic by role
    (every operation staff account = edit, also new ones added later in the Supply Hub)."""
    if role == "admin":
        return "edit"
    own = (settings.get("access_override") or {}).get(username)
    if own in ("hidden", "view", "edit"):
        return own
    by_role = {**DEFAULT_SETTINGS["access_by_role"], **(settings.get("access_by_role") or {})}
    return by_role.get(role, settings.get("access_default", "view"))


def ops_names(cfg, users=None):
    """Operation staff (role staff) + extra names from Settings: offered in 👷 Produced by and 📋 Tasks."""
    users = load_users() if users is None else users
    ops = [(r.get("staff_name") or u) for u, r in users.items() if r.get("active", True) and r.get("role") == "staff"]
    return list(dict.fromkeys(sorted(ops, key=str.lower) + list(cfg.get("prod_staff") or [])))


# ---- keep me signed in (survives refresh, closed tab, phone lock, app restart) ----
def _tok_hash(t):
    return hashlib.sha256(str(t).encode("utf-8")).hexdigest()


def _modify_json(name, fn):
    for attempt in range(4):
        try:
            data, rev = read_bytes(name, max_age=0)
            d = json.loads(data.decode("utf-8")) if data else {}
            d = fn(d if isinstance(d, dict) else {}) or d
            write_bytes(name, json.dumps(d).encode("utf-8"), rev)
            return True
        except Conflict:
            time.sleep(0.3 * (attempt + 1))
        except Exception:
            return False
    return False


def _js(code):
    try:
        components.html(f"<script>try{{var W=window.parent;{code}}}catch(e){{}}</script>", height=0)
    except Exception:
        pass


def _js_set_cookie(tok):
    t, age = json.dumps(tok), REMEMBER_DAYS * 86400
    return (f"var s=(W.location.protocol==='https:')?'; Secure':'';"
            f"W.document.cookie='{COOKIE}='+{t}+'; max-age={age}; path=/; SameSite=Lax'+s;"
            f"try{{W.localStorage.setItem('{COOKIE}',{t});}}catch(e){{}}")


def _js_clear_cookie():
    return (f"W.document.cookie='{COOKIE}=; max-age=0; path=/';"
            f"try{{W.localStorage.removeItem('{COOKIE}');}}catch(e){{}}")


def issue_token(user, pw_stamp):
    tok, now = pysecrets.token_urlsafe(32), time.time()

    def add(d):
        for h in [h for h, r in d.items() if r.get("exp", 0) < now]:
            d.pop(h, None)
        mine = sorted((r.get("created", 0), h) for h, r in d.items() if r.get("user") == user)
        for _c, h in mine[:-39]:
            d.pop(h, None)                                # at most 40 browsers per person
        d[_tok_hash(tok)] = {"user": user, "created": now, "exp": now + REMEMBER_DAYS * 86400, "pw": pw_stamp}
        return d
    return tok if _modify_json(REMEMBER_FILE, add) else None


def restore_login():
    """Signs the person in again from the token saved in this browser. True / False."""
    tok = None
    try:
        tok = st.query_params.get(URL_TOK)
        if URL_TOK in st.query_params:
            del st.query_params[URL_TOK]                   # never stays in the address
    except Exception:
        pass
    if not tok:
        try:
            tok = st.context.cookies.get(COOKIE)
        except Exception:
            tok = None
    if not isinstance(tok, str) or not 20 <= len(tok) <= 100:
        return False
    h, now = _tok_hash(tok), time.time()
    rec = None
    for age in (30, 0):                                    # second try reads the newest file
        data, _rev = read_bytes(REMEMBER_FILE, max_age=age)
        try:
            rec = (json.loads(data.decode("utf-8")) if data else {}).get(h)
        except Exception:
            rec = None
        if rec:
            break
    users = load_users()
    u = users.get(rec["user"]) if rec else None
    if not rec or rec.get("exp", 0) < now or not u or not u.get("active", True) or rec.get("pw", "") != u.get("pw_changed", ""):
        st.session_state["p_cookie_clear"] = True          # bad / old token: forget it in this browser
        return False
    st.session_state.update(p_user=rec["user"], p_role=u.get("role", "staff"), p_name=u.get("staff_name") or rec["user"],
                            p_tok=tok)
    if rec.get("exp", 0) - now < (REMEMBER_DAYS - 1) * 86400:     # renew once a day
        _modify_json(REMEMBER_FILE, lambda d: (d[h].update(exp=now + REMEMBER_DAYS * 86400) if h in d else None, d)[1])
    return True


def sign_out():
    tok = st.session_state.get("p_tok")
    if tok:
        _modify_json(REMEMBER_FILE, lambda d: (d.pop(_tok_hash(tok), None), d)[1])
    for k in [k for k in st.session_state.keys()]:
        del st.session_state[k]
    st.session_state["p_cookie_clear"] = True


PIN_RE = re.compile(r"^[0-9]{4,6}$")


def _pin_hash(pin):
    salt = os.urandom(16)
    return {"salt": salt.hex(), "hash": hashlib.pbkdf2_hmac("sha256", pin.encode(), salt, 100_000).hex(), "iter": 100_000}


def _pin_ok(pin, rec):
    p = rec.get("pin") or {}
    try:
        dk = hashlib.pbkdf2_hmac("sha256", str(pin).encode(), bytes.fromhex(p["salt"]), int(p["iter"]))
        return hmac.compare_digest(dk.hex(), p["hash"])
    except Exception:
        return False


def _locked(user):
    """5 wrong PINs in 10 minutes -> wait 10 minutes (a PIN is short, so guessing is stopped)."""
    n, t0 = _mem().setdefault("pin_fail", {}).get(user, (0, 0))
    return n >= 5 and time.time() - t0 < 600


def _failed(user):
    fails = _mem().setdefault("pin_fail", {})
    n, t0 = fails.get(user, (0, 0))
    if time.time() - t0 >= 600:
        n, t0 = 0, time.time()                      # a new 10-minute window
    fails[user] = (n + 1, t0)


def set_pin(user, pin):
    def ch(users):
        if user not in users:
            raise RuntimeError("Account not found.")
        users[user]["pin"] = _pin_hash(pin)
    modify_users(ch)


def _finish_login(u, rec, keep, how):
    st.session_state.update(p_user=u, p_role=rec.get("role", "staff"), p_name=rec.get("staff_name") or u,
                            p_must_change=bool(rec.get("must_change")) and not rec.get("pin"))
    _mem().setdefault("pin_fail", {}).pop(u, None)
    audit("sign in", how)
    if keep:
        tok = issue_token(u, rec.get("pw_changed", ""))
        if tok:
            st.session_state["p_tok"] = tok
            st.session_state["p_cookie_set"] = True
    st.rerun()


NUMERIC_PIN_JS = ("var f=function(){W.document.querySelectorAll('input[aria-label*=\"PIN\"]').forEach(function(x){"
                  "x.setAttribute('inputmode','numeric');x.setAttribute('pattern','[0-9]*');"
                  "x.setAttribute('autocomplete','one-time-code');});};f();"
                  "new MutationObserver(f).observe(W.document.body,{childList:true,subtree:true});")


def login_box():
    users = load_users()
    st.markdown("## 🏭 Production & Live Stock")
    if not users:
        if USE_DROPBOX:
            st.error("Cannot read the accounts (users.json) in the Dropbox folder. Check the app Secrets.")
            st.stop()
        st.info("Local test mode: no accounts file — you are signed in as admin.")
        st.session_state.update(p_user="admin", p_role="admin", p_name="admin")
        st.rerun()
    if st.session_state.pop("p_cookie_clear", False):
        _js(_js_clear_cookie())
    else:
        # the browser still has a saved sign-in that did not reach the server (phone woke up, first load...):
        # hand it over once through the address, at most every 20 s (never loops)
        _js(f"var t='';try{{t=W.localStorage.getItem('{COOKIE}')||'';}}catch(e){{}}"
            f"if(!t){{var m=W.document.cookie.match(/(?:^|; ){COOKIE}=([^;]+)/);t=m?m[1]:'';}}"
            f"var last=+(W.sessionStorage.getItem('p_rescued')||0);"
            f"if(t&&Date.now()-last>20000){{W.sessionStorage.setItem('p_rescued',String(Date.now()));"
            f"var sc=W.document.createElement('script');"          # run in the page itself (the frame may not reload it)
            f"sc.text=\"var u=new URL(location.href);u.searchParams.set('{URL_TOK}',\"+JSON.stringify(t)+\");location.replace(u.toString());\";"
            f"W.document.body.appendChild(sc);}}")
    _js(NUMERIC_PIN_JS)                                    # PIN box opens the number keypad on phones
    cfg, _r = load_settings()
    people = sorted([u for u, r in users.items() if r.get("active", True)
                     and access_of(u, r.get("role", "staff"), cfg) != "hidden"],
                    key=lambda u: ({"staff": 0, "sales": 1, "viewer": 2}.get(users[u].get("role"), 3),
                                   (users[u].get("staff_name") or u).lower()))
    t_pin, t_pw = st.tabs(["👤 My name + PIN", "🔑 Username + password"])
    with t_pin:
        with st.form("pin_login"):
            who = st.selectbox("👤 Your name", people, index=None, placeholder="Tap to choose your name",
                               format_func=lambda u: f"{users[u].get('staff_name') or u}  ({u})"
                               + ("" if users[u].get("pin") else "  · no PIN yet"))
            pin = st.text_input("🔢 PIN (4–6 numbers)", type="password", max_chars=6)
            keep = st.checkbox(f"Keep me signed in on this phone ({REMEMBER_DAYS} days)", value=True, key="keep_pin")
            ok = st.form_submit_button("Sign in", type="primary", width="stretch")
        st.caption("No PIN yet? Sign in once with your password (other tab), then tap 🔑 PIN at the top to choose one. "
                   "Or ask Admin to give you one.")
        if ok:
            rec = users.get(who or "")
            if not rec:
                st.error("Choose your name first.")
            elif _locked(who):
                st.error("Too many wrong PINs. Wait 10 minutes, or sign in with your password.")
            elif not rec.get("pin"):
                st.warning("You have no PIN yet — sign in with your password once, then choose a PIN.")
            elif rec.get("active", True) and _pin_ok(pin.strip(), rec):
                _finish_login(who, rec, keep, "PIN")
            else:
                _failed(who)
                time.sleep(1)
                st.error("Wrong PIN.")
    with t_pw:
        with st.form("login"):
            u = st.text_input("Username").strip().lower()
            p = st.text_input("Password", type="password")
            keep2 = st.checkbox(f"Keep me signed in on this phone / computer ({REMEMBER_DAYS} days)", value=True)
            ok2 = st.form_submit_button("Sign in", type="primary", width="stretch")
        st.caption("The same username and password as the Supply Hub app.")
        if ok2:
            rec = users.get(u)
            if rec and rec.get("active", True) and _check_pw(p, rec):
                _finish_login(u, rec, keep2, "password")
            time.sleep(1)
            st.error("Wrong username or password.")
    st.stop()


def _say(kind, msg):
    """Shows the result even when the 🔑 box closes after saving."""
    st.toast(("✅ " if kind == "success" else "⚠️ ") + msg.lstrip("✅ "), duration="long")
    (st.success if kind == "success" else st.error)(msg)


def my_pin_password_box(me_user):
    """🔑 Everyone: choose / change my PIN, change my password."""
    t1, t2 = st.tabs(["🔢 My PIN", "🔑 My password"])
    with t1:
        with st.form("my_pin", clear_on_submit=True):
            a = st.text_input("New PIN (4–6 numbers)", type="password", max_chars=6)
            b = st.text_input("Type the PIN again", type="password", max_chars=6)
            ok = st.form_submit_button("💾 Save my PIN", type="primary")
        if ok:
            if pin_problem(a, b):
                _say("error", pin_problem(a, b))
            else:
                try:
                    set_pin(me_user, a)
                    st.session_state["p_must_change"] = False
                    audit("PIN changed", me_user)
                    _say("success", "✅ PIN saved. Next time: choose your name + type this PIN.")
                except Exception as e:
                    _say("error", f"Not saved: {e}")
    with t2:
        with st.form("my_pw", clear_on_submit=True):
            old = st.text_input("Current password", type="password")
            a = st.text_input("New password (8+ characters, letters and numbers)", type="password")
            b = st.text_input("Type the new password again", type="password")
            ok = st.form_submit_button("💾 Change my password")
        if ok:
            rec = load_users().get(me_user, {})
            if not _check_pw(old, rec):
                _say("error", "The current password is wrong.")
            elif pw_problem(a) or a != b:
                _say("error", pw_problem(a) or "The two new passwords are different.")
            else:
                try:
                    stamp = change_password(me_user, a)
                    tok = issue_token(me_user, stamp)               # stay signed in on this phone
                    if tok:
                        st.session_state["p_tok"], st.session_state["p_cookie_set"] = tok, True
                    audit("password changed", me_user)
                    _say("success", "✅ Password changed (also for the Supply Hub).")
                except Exception as e:
                    st.error(f"Not saved: {e}")



# ==========================================
# SALE JOURNAL -> pcs sold per bun per day
# ==========================================
def _cell_date(v, ym):
    if isinstance(v, datetime):
        return v.date()
    if isinstance(v, date):
        return v
    if isinstance(v, (int, float)) and 20000 < v < 80000:
        return (datetime(1899, 12, 30) + timedelta(days=int(v))).date()
    if isinstance(v, str):
        t = v.strip()
        for fmt in ("%Y-%m-%d", "%d/%m/%Y", "%m/%d/%Y", "%d-%m-%Y", "%d-%b-%Y", "%a, %b%d, %y", "%d %b %Y"):
            try:
                return datetime.strptime(t.split(" ")[0] if fmt == "%Y-%m-%d" else t, fmt).date()
            except ValueError:
                pass
        m = re.match(r"^(\d{1,2})$", t)
        if m and ym:
            try:
                return date(ym[0], ym[1], int(m.group(1)))
            except ValueError:
                return None
    return None


@st.cache_resource(show_spinner=False, max_entries=8)
def parse_journal(name, rev, data):
    """(sales DataFrame Date/Bun/Pcs, {code: Khmer name}) from one monthly journal. Cached per file revision."""
    import openpyxl
    wb = openpyxl.load_workbook(io.BytesIO(data), read_only=True, data_only=True)
    try:
        ws = wb[JOURNAL_SHEET] if JOURNAL_SHEET in wb.sheetnames else wb.worksheets[0]
        rows = list(ws.iter_rows(values_only=True))
    finally:
        wb.close()
    hdr, cols = None, {}
    for i, r in enumerate(rows[:20]):
        found = {str(v).strip(): c for c, v in enumerate(r) if v is not None and BUN_RE.match(str(v).strip())}
        if len(found) >= 3:
            hdr, cols = i, found
            break
    if hdr is None:
        return pd.DataFrame(columns=["Date", "Bun", "Pcs"]), {}
    names = {}
    if hdr >= 1:
        for k, c in cols.items():
            v = rows[hdr - 1][c] if c < len(rows[hdr - 1]) else None
            names[k] = str(v).strip() if v is not None else ""
    m = re.match(r"^(\d{1,2})_", name)
    yr = re.search(r"(20\d\d)", name)
    ym = (int(yr.group(1)), int(m.group(1))) if m and yr else None
    out = []
    for r in rows[hdr + 1:]:
        if not r or len(r) < 2 or r[1] is None or str(r[1]).strip() == "":
            continue
        d = _cell_date(r[0], ym)
        if d is None:
            continue
        for k, c in cols.items():
            v = r[c] if c < len(r) else None
            if isinstance(v, (int, float)) and v:
                out.append((d, k, float(v)))
            elif isinstance(v, str) and v.strip().replace(".", "", 1).isdigit():
                out.append((d, k, float(v)))
    df = pd.DataFrame(out, columns=["Date", "Bun", "Pcs"])
    if ym and not df.empty:                       # a journal only speaks for its own month
        df = df[[(x.year, x.month) == ym for x in df["Date"]]]
    return df.groupby(["Date", "Bun"], as_index=False)["Pcs"].sum(), names


def journal_names_for(days_back):
    """Monthly journal files covering today and the last `days_back` days."""
    t = today_kh()
    months = {((t - timedelta(days=i)).year, (t - timedelta(days=i)).month) for i in range(days_back + 1)}
    wanted = {f"{mo:02d}_SALE_JOURNAL_{MONTHS[mo - 1]}_{yr}" for yr, mo in months}
    if USE_DROPBOX:
        names = [n for n in _listing() if fnmatch.fnmatchcase(n.lower(), JOURNAL_PATTERN.lower())]
    else:
        names = [n for n in os.listdir(LOCAL_DIR) if fnmatch.fnmatchcase(n.lower(), JOURNAL_PATTERN.lower())]
    return [n for n in names if os.path.splitext(n)[0].upper().replace(" ", "_") in wanted]


def load_sales(days_back):
    frames, names = [], {}
    for n in journal_names_for(days_back):
        data, rev = read_bytes(n, max_age=20)
        if data:
            df, nm = parse_journal(n, rev, data)
            frames.append(df)
            names.update({k: v for k, v in nm.items() if v})
    sales = pd.concat(frames, ignore_index=True) if frames else pd.DataFrame(columns=["Date", "Bun", "Pcs"])
    if not sales.empty:
        sales = sales.groupby(["Date", "Bun"], as_index=False)["Pcs"].sum()
    return sales, names


# ==========================================
# STOCK ENGINE (FIFO by production date)
# ==========================================
def _num(v):
    try:
        return float(str(v).replace(",", "").strip() or 0)
    except ValueError:
        return 0.0


def _day(v):
    try:
        return datetime.strptime(str(v)[:10], "%Y-%m-%d").date()
    except ValueError:
        return None


def latest_counts(counts):
    """{bun: (count_date, {prod_date: pcs})} from the newest count of each bun."""
    out = {}
    if counts.empty:
        return out
    c = counts.copy()
    c["_cd"] = c["Count_Date"].map(_day)
    c = c[c["_cd"].notna()]
    for bun, g in c.groupby("Bun"):
        g = g.sort_values(["_cd", "Saved_At"])
        last = g[g["Count_Id"] == g["Count_Id"].iloc[-1]]
        batches = {}
        for _, r in last.iterrows():
            pdte = _day(r["Prod_Date"]) or last["_cd"].iloc[0]
            batches[pdte] = batches.get(pdte, 0) + _num(r["Pcs"])
        out[bun] = (last["_cd"].iloc[0], {k: v for k, v in batches.items() if v})
    return out


def compute_stock(buns, prod, counts, adjs, sales, until):
    """Replays every day after each bun's last count up to `until`.
    Returns (batches {bun: {prod_date: pcs}}, short {bun: pcs sold with no stock}, history DataFrame Date/Bun/Stock,
    no_count [buns never counted])."""
    base = latest_counts(counts)
    p = prod.copy()
    p["_d"] = p["Prod_Date"].map(_day)
    p["_n"] = p["Pcs"].map(_num).astype(float)
    a = adjs.copy()
    a["_d"] = a["Date"].map(_day)
    a["_pd"] = a["Prod_Date"].map(_day)
    a["_n"] = a["Pcs"].map(_num).astype(float)
    sale_map = {}
    for d, b, n in sales[["Date", "Bun", "Pcs"]].itertuples(index=False):
        sale_map[(d, b)] = sale_map.get((d, b), 0) + n
    batches, short, hist, no_count = {}, {}, [], []
    first_day = min([d for d in p["_d"].dropna()] + [until])
    for bun in buns:
        if bun in base:
            start, bt = base[bun][0], dict(base[bun][1])
        else:
            no_count.append(bun)
            start, bt = first_day - timedelta(days=1), {}
        miss = 0.0
        pb = p[(p["Bun"] == bun) & p["_d"].notna()]
        prod_by_day = pb.groupby("_d")["_n"].sum().to_dict()
        ab = a[(a["Bun"] == bun) & a["_d"].notna()]
        d = start + timedelta(days=1)
        while d <= until:
            if prod_by_day.get(d):
                bt[d] = bt.get(d, 0) + prod_by_day[d]
            for _, r in ab[ab["_d"] == d].iterrows():
                n = r["_n"]
                if n >= 0:
                    k = r["_pd"] or d
                    bt[k] = bt.get(k, 0) + n
                else:
                    rest = -n
                    keys = [r["_pd"]] if r["_pd"] in bt else sorted(bt)
                    for k in keys:
                        take = min(bt.get(k, 0), rest)
                        bt[k] = bt.get(k, 0) - take
                        rest -= take
                        if rest <= 0:
                            break
            need = sale_map.get((d, bun), 0)
            for k in sorted(bt):                        # oldest production date first
                if need <= 0:
                    break
                take = min(bt[k], need)
                bt[k] -= take
                need -= take
            miss += need
            bt = {k: v for k, v in bt.items() if v > 0.0001}
            hist.append((d, bun, sum(bt.values())))
            d += timedelta(days=1)
        batches[bun], short[bun] = bt, miss
    return batches, short, pd.DataFrame(hist, columns=["Date", "Bun", "Stock"]), no_count


def sales_speed(sales, buns, until, lookback):
    """Average pcs per SELLING day (days the journal has sales) over the last `lookback` days before `until`."""
    lo = until - timedelta(days=lookback)
    win = sales[(sales["Date"] > lo) & (sales["Date"] < until)] if not sales.empty else sales
    sell_days = sorted(set(win["Date"])) if not win.empty else []
    n = max(len(sell_days), 1)
    tot = win.groupby("Bun")["Pcs"].sum().to_dict() if not win.empty else {}
    return {b: tot.get(b, 0) / n for b in buns}, len(sell_days)


def forecast(sales, buns, start, days, lookback):
    """{(date, bun): pcs} — same weekday average over the last weeks (falls back to the overall average)."""
    lo = start - timedelta(days=lookback)
    win = sales[(sales["Date"] >= lo) & (sales["Date"] < start)] if not sales.empty else sales
    speed, _n = sales_speed(sales, buns, start, lookback)
    by_wd = {}
    if not win.empty:
        w = win.copy()
        w["wd"] = [d.weekday() for d in w["Date"]]
        day_tot = w.groupby(["Date", "wd"])["Pcs"].sum().reset_index()
        open_days = day_tot.groupby("wd")["Date"].nunique().to_dict()
        tot_days = {wd: len({d for d in set(win["Date"]) if d.weekday() == wd}) for wd in range(7)}
        cal_days = {wd: sum(1 for i in range((start - lo).days) if (lo + timedelta(days=i)).weekday() == wd) for wd in range(7)}
        per = w.groupby(["Bun", "wd"])["Pcs"].sum().to_dict()
        for wd in range(7):
            closed = cal_days.get(wd, 0) >= 2 and tot_days.get(wd, 0) == 0     # e.g. never sells on that weekday
            for b in buns:
                if closed:
                    by_wd[(wd, b)] = 0.0
                elif open_days.get(wd, 0) >= 2:
                    by_wd[(wd, b)] = per.get((b, wd), 0) / open_days[wd]
    out = {}
    for i in range(days):
        d = start + timedelta(days=i)
        for b in buns:
            out[(d, b)] = by_wd.get((d.weekday(), b), speed.get(b, 0))
    return out


def plan_production(buns, stock_now, fc, start, days, cfg):
    """Day by day: produce so the stock at the end of the day covers the next `target` selling days.
    Then keep the total under max_total (the non-priority buns are lowered first) and under the daily capacity."""
    tgt = {b: int(cfg["target_days"].get(b, cfg["target_default"])) for b in buns}
    pdays = {b: cfg["prod_days"].get(b, cfg["prod_days_default"]) for b in buns}
    prio = [b for b in cfg.get("priority", PRIORITY_DEFAULT) if b in buns]
    rnd = max(int(cfg.get("round_to", 10) or 1), 1)
    cap_total, cap_prod = float(cfg["max_total"]), float(cfg.get("max_prod_per_day") or 0)
    horizon = start + timedelta(days=days + 10)
    stock = dict(stock_now)
    rows = []
    for i in range(days):
        d = start + timedelta(days=i)
        prod = {}
        for b in buns:
            if d.weekday() not in pdays[b]:
                prod[b] = 0
                continue
            need, k, j = 0.0, 0, 1                      # sales of the next `target` SELLING days
            while k < tgt[b] and d + timedelta(days=j) <= horizon:
                dd = d + timedelta(days=j)
                if sum(fc.get((dd, x), 0) for x in buns) > 0:     # a day the shop sells (closed days skipped)
                    need += fc.get((dd, b), 0)
                    k += 1
                j += 1
            want = need + fc.get((d, b), 0) - stock.get(b, 0)
            prod[b] = int(-(-max(want, 0) // rnd) * rnd)
        # daily capacity
        if cap_prod and sum(prod.values()) > cap_prod:
            over = sum(prod.values()) - cap_prod
            for group in ([b for b in buns if b not in prio], prio):
                tot = sum(prod[b] for b in group)
                if tot <= 0 or over <= 0:
                    continue
                cut = min(over, tot)
                for b in group:
                    prod[b] -= int(cut * prod[b] / tot // rnd * rnd)
                over = sum(prod.values()) - cap_prod
        # total stock limit at the end of the day
        end = {b: stock.get(b, 0) + prod[b] - fc.get((d, b), 0) for b in buns}
        over = sum(max(v, 0) for v in end.values()) - cap_total
        for group in ([b for b in buns if b not in prio], prio):
            if over <= 0:
                break
            tot = sum(prod[b] for b in group)
            if tot <= 0:
                continue
            cut = min(over, tot)
            for b in group:
                prod[b] = max(0, prod[b] - int(-(-cut * prod[b] / tot // rnd) * rnd))
            end = {b: stock.get(b, 0) + prod[b] - fc.get((d, b), 0) for b in buns}
            over = sum(max(v, 0) for v in end.values()) - cap_total
        for b in buns:
            rows.append({"Date": d, "Bun": b, "Produce": prod[b], "Expected sales": round(fc.get((d, b), 0)),
                         "Stock end of day": round(end[b])})
            stock[b] = max(end[b], 0)
    return pd.DataFrame(rows)


# ==========================================
# PAGE PIECES
# ==========================================
CSS = """
<style>
.block-container {padding-top: 1.2rem; max-width: 1400px;}
.p-tiles {display:grid; grid-template-columns: repeat(5, minmax(0,1fr)); gap:10px; margin: 6px 0 12px;}
.p-tile {border:1px solid rgba(128,128,128,.25); border-radius:14px; padding:10px 14px; background: rgba(15,118,110,.04);}
.p-tile .t {font-size:.82rem; opacity:.75;} .p-tile .v {font-size:1.65rem; font-weight:800; line-height:1.15;}
.p-tile .s {font-size:.8rem; opacity:.75;}
.p-bar {height:12px; border-radius:99px; background:rgba(128,128,128,.18); overflow:hidden; margin:4px 0 2px;}
.p-bar span {display:block; height:100%;}
@media (max-width: 760px) { .p-tiles {grid-template-columns: repeat(2, minmax(0,1fr));} .p-tile .v {font-size:1.3rem;} }
</style>
"""


def tiles(items):
    html = "<div class='p-tiles'>" + "".join(
        f"<div class='p-tile'><div class='t'>{t}</div><div class='v'>{v}</div><div class='s'>{s}</div></div>"
        for t, v, s in items) + "</div>"
    st.markdown(html, unsafe_allow_html=True)


def bun_label(b, names):
    n = names.get(b, "")
    return f"{b} {n}".strip()


# Your sheet: short names and column colours (ស / ល / ក / តយ = N4 / N41 / N42 / N43)
SHORT = {"N4": "ស", "N41": "ល", "N42": "ក", "N43": "តយ"}
COLORS = {"N1": "#ED7D31", "N2": "#D9E1F2", "N21": "#FCE4D6", "N22": "#ACB9CA", "N23": "#F4B084", "N3": "#B4C6E7",
          "N31": "#FFF2CC", "N32": "#FCE4D6", "N34": "#EDEDED", "N4": "#FFFFFF", "N41": "#FFE699", "N42": "#F8CBAD",
          "N43": "#E2EFDA"}
TOTAL_BG, HEAD_BG, SUM_BG = "#BDD7EE", "#BDD7EE", "#FFC000"
DOT = {"N1": "🟧", "N2": "🟦", "N21": "🟫", "N22": "⬛", "N23": "🟠", "N3": "🔷", "N31": "🟨", "N32": "🟤", "N34": "⚪",
       "N4": "⬜", "N41": "🟡", "N42": "🔶", "N43": "🟩"}
PHONE_CSS = """<style>
[data-testid="stNumberInput"] input {font-size:1.3rem !important; min-height:2.8rem;}
[data-testid="stNumberInput"] label p {font-size:1.05rem !important; font-weight:600;}
.stButton button, .stDownloadButton button {min-height:3rem; font-size:1.05rem;}
div[role="radiogroup"] label p {font-size:1.02rem;}
</style>"""


def phone_label(b, names):
    return f"{DOT.get(b, '▫️')} {short(b)} · {names.get(b, '')}".strip(" ·")


def bun_inputs(show, names, values, key, step=10):
    """Phone: one big number box per bun (the number keypad opens). Empty box = 0. -> {bun: pcs}"""
    out = {}
    for b in show:
        v = values.get(b)
        n = st.number_input(phone_label(b, names), min_value=0, max_value=200000, step=step,
                            value=int(v) if v else None, placeholder="0", key=f"{key}_{b}")
        if n:
            out[b] = int(n)
    return out


def short(b):
    return SHORT.get(b, b)


def day_label(d):
    return f"{d:%a, %b/%d, %y}"


def active_buns(buns, sales, batches=None):
    """Hide a bun (e.g. N34) that has no sales in the last weeks and no stock."""
    sold = set(sales["Bun"]) if not sales.empty else set()
    have = {b for b, v in (batches or {}).items() if v and sum(v.values()) > 0.5}
    return [b for b in buns if b in sold or b in have or b in DEFAULT_BUNS and b != "N34"]


def excel_html(title, rows, buns, total_title="សរុប", first_col="Item", note=""):
    """Your Excel layout: blue title, coloured bun columns, blue សរុប column, yellow total row.
    rows = [(label, {bun: pcs})]."""
    th = "padding:6px 8px;border:1px solid #333;text-align:center;font-weight:700;"
    td = "padding:5px 8px;border:1px solid #333;text-align:center;"
    h = (f"<div style='overflow-x:auto;margin:4px 0 10px'><table style='border-collapse:collapse;font-size:.92rem;"
         f"min-width:{180 + 70 * (len(buns) + 1)}px;color:#111;background:#fff'>"
         f"<tr><th style='{th}background:{HEAD_BG}'>Date</th><th colspan='{len(buns)}' style='{th}background:{HEAD_BG}'>{title}</th>"
         f"<th style='{th}background:{HEAD_BG}'>{total_title}</th></tr><tr><th style='{th}background:#fff'>{first_col}</th>")
    for b in buns:
        h += f"<th style='{th}background:{COLORS.get(b, '#fff')}' title='{b}'>{short(b)}</th>"
    h += f"<th style='{th}background:#FFFF00'></th></tr>"
    col_tot = {b: 0 for b in buns}
    for label, vals in rows:
        h += f"<tr><td style='{td}background:#fff;white-space:nowrap'>{label}</td>"
        rt = 0
        for b in buns:
            v = int(round(vals.get(b, 0) or 0))
            rt += v
            col_tot[b] += v
            h += f"<td style='{td}background:{COLORS.get(b, '#fff')}'>{f'{v:,}' if v else ''}</td>"
        h += f"<td style='{td}background:{TOTAL_BG}'>{rt:,}</td></tr>"
    h += f"<tr><td style='{td}background:#fff'></td>"
    for b in buns:
        h += f"<td style='{td}background:{SUM_BG};font-weight:800'>{col_tot[b]:,}</td>"
    h += f"<td style='{td}background:{TOTAL_BG};font-weight:800'>{sum(col_tot.values()):,}</td></tr></table></div>"
    if note:
        h += f"<div style='font-size:.8rem;opacity:.75;margin:-6px 0 8px'>{note}</div>"
    return h


def get_data(cfg):
    prod, _ = read_csv(PROD_FILE, PROD_COLS)
    counts, _ = read_csv(COUNT_FILE, COUNT_COLS)
    adjs, _ = read_csv(ADJ_FILE, ADJ_COLS)
    sales, names = load_sales(max(int(cfg.get("lookback_days", 28)), 7) + 45)
    buns = list(dict.fromkeys([b for b in DEFAULT_BUNS] + sorted(set(sales["Bun"]) if not sales.empty else [],
                                                                       key=lambda x: (len(x), x))))
    return prod, counts, adjs, sales, names, buns


def stock_status(stock, speed, tgt):
    if stock < 0.5 and speed > 0:
        return "🔴 Out of stock"
    if speed <= 0:
        return "⚪ No recent sales"
    days = stock / speed
    if days < tgt - 1:
        return "🔴 Too low"
    if days < tgt:
        return "🟡 A bit low"
    if days > tgt + 3:
        return "🟠 Too much"
    return "🟢 OK"


def page_live(cfg, can_edit):
    st.subheader("📊 Live stock")
    prod, counts, adjs, sales, names, buns = get_data(cfg)
    t = today_kh()
    batches, short, hist, no_count = compute_stock(buns, prod, counts, adjs, sales, t)
    speed, n_sell = sales_speed(sales, buns, t, int(cfg["lookback_days"]))
    total = sum(sum(v.values()) for v in batches.values())
    cap = float(cfg["max_total"])
    p_today = prod[prod["Prod_Date"].map(_day) == t]["Pcs"].map(_num).astype(float).sum()
    s_today = sales[sales["Date"] == t]["Pcs"].sum() if not sales.empty else 0
    shelf = int(cfg.get("shelf_days", 10))
    rows, alerts = [], []
    for b in buns:
        stk = sum(batches[b].values())
        tgt = int(cfg["target_days"].get(b, cfg["target_default"]))
        sp = speed.get(b, 0)
        oldest = min(batches[b]) if batches[b] else None
        age = (t - oldest).days if oldest else None
        b_shelf = int(cfg.get("shelf_by_bun", {}).get(b, shelf))
        old_pcs = sum(v for k, v in batches[b].items() if (t - k).days > b_shelf)
        status = stock_status(stk, sp, tgt)
        rows.append({"Bun": bun_label(b, names), "In stock (pcs)": int(round(stk)), "Sold / day": int(round(sp)),
                     "Days of stock": round(stk / sp, 1) if sp else None, "Target days": tgt, "Status": status,
                     "Oldest batch": f"{oldest:%d %b} ({age} d)" if oldest else "-",
                     f"Older than {b_shelf} d": int(old_pcs), "Sold today": int(sales[(sales["Date"] == t) & (sales["Bun"] == b)]["Pcs"].sum()) if not sales.empty else 0})
        if status.startswith("🔴"):
            alerts.append(f"🔴 **{bun_label(b, names)}**: {status[2:]} — {int(stk):,} pcs ≈ {stk / sp:.1f} days (target {tgt})" if sp else
                          f"🔴 **{bun_label(b, names)}**: out of stock")
        if old_pcs:
            alerts.append(f"🟤 **{bun_label(b, names)}**: {int(old_pcs):,} pcs older than {b_shelf} days — sell first / check quality")
        if short.get(b, 0) > 0.5:
            alerts.append(f"⚠️ **{bun_label(b, names)}**: the journal sold {int(short[b]):,} pcs more than the stock "
                          "(production not logged, or the stock count is missing)")
    if total > cap:
        alerts.insert(0, f"🚨 **Total stock {int(total):,} pcs is above the {int(cap):,} limit** — produce less / sell first")
    elif total > cap * 0.9:
        alerts.insert(0, f"🟠 Total stock {int(total):,} pcs is close to the {int(cap):,} limit")
    pct = min(total / cap, 1.5) if cap else 0
    col = "#2e7d32" if total <= cap * 0.9 else ("#f9a825" if total <= cap else "#c62828")
    low = sum(1 for r in rows if r["Status"].startswith("🔴"))
    tiles([("📦 Total stock", f"{int(total):,}", f"limit {int(cap):,} pcs"),
           ("🏭 Produced today", f"{int(p_today):,}", "pcs logged"),
           ("🧾 Sold today", f"{int(s_today):,}", "pcs in the sale journal"),
           ("🔴 Buns too low", low, f"of {len(buns)} buns"),
           ("🟤 Old pcs", f"{int(sum(r[k] for r in rows for k in r if k.startswith('Older than'))):,}",
            f"older than shelf life")])
    st.markdown(f"<div class='p-bar'><span style='width:{min(pct, 1) * 100:.1f}%;background:{col}'></span></div>"
                f"<div style='font-size:.85rem;opacity:.8'>Total stock {int(total):,} / {int(cap):,} pcs "
                f"({total / cap * 100:.0f}% of the limit) · sales speed from the last {n_sell} selling days · "
                f"updated {now_kh():%H:%M:%S}</div>", unsafe_allow_html=True)
    if no_count:
        st.warning("No stock count yet for: " + ", ".join(no_count) + ". Enter one in **📦 Stock count** — "
                   "until then their stock only counts production logged here.")
    for a in alerts[:12]:
        st.markdown(a)
    df = pd.DataFrame(rows)
    st.dataframe(df, hide_index=True, width="stretch", column_config={
        "Days of stock": st.column_config.ProgressColumn("Days of stock", min_value=0, max_value=10, format="%.1f d"),
        "In stock (pcs)": st.column_config.NumberColumn(format="%d")})
    with st.expander("🗓️ Stock by production date (oldest at the top = sell first)", expanded=True):
        dates = sorted({k for v in batches.values() for k in v})
        if dates:
            show = active_buns(buns, sales, batches)
            st.markdown(excel_html(f"ស្តុកនំសរុប ({t:%d.%m.%Y}) — calculated now", [
                (day_label(k), {b: batches[b].get(k, 0) for b in show}) for k in dates], show,
                note=f"Older than {shelf} days = check / sell first."), unsafe_allow_html=True)
        else:
            st.info("No stock yet. Start with the evening stock count in 📦 Stock count.")
    with st.expander("📈 Total stock per day (last 21 days)"):
        if not hist.empty:
            h = hist[hist["Date"] >= t - timedelta(days=21)].groupby("Date")["Stock"].sum().reset_index()
            h["Limit"] = cap
            st.line_chart(h.set_index("Date"))


def _rerun_here():
    """Refresh only this page (smooth); falls back to a full refresh when not inside a page refresh."""
    try:
        st.rerun(scope="fragment")
    except st.errors.StreamlitAPIException:
        st.rerun()


# ---- saving made safe and easy: drafts kept, no double saves, undo ----
UNDO_MINUTES = 15


def show_flash(key):
    """Green message after a save (also a toast, seen even when the page is scrolled down)."""
    msg = st.session_state.pop(key, None)
    if msg:
        st.success(msg)
        st.toast(msg[:140])


def save_guard(kind, sig):
    """False when exactly the same data was just saved (double tap / slow phone) — it is never saved twice."""
    last = st.session_state.get(f"_sig_{kind}")
    if last and last[0] == sig and time.time() - last[1] < 120:
        return False
    st.session_state[f"_sig_{kind}"] = (sig, time.time())
    return True


def remember_undo(kind, file, cols, idcol, rid, label):
    st.session_state[f"_undo_{kind}"] = {"file": file, "cols": cols, "idcol": idcol, "id": rid, "label": label,
                                         "t": time.time(), "at": now_kh().strftime("%H:%M")}


def undo_bar(kind, flash_key):
    """'↩️ Undo last save' for a few minutes after a save (removes exactly the lines of that save)."""
    u = st.session_state.get(f"_undo_{kind}")
    if not u or time.time() - u["t"] > UNDO_MINUTES * 60:
        return
    c1, c2 = st.columns([3, 1])
    c1.caption(f"🕘 Your last save ({u['at']}): {u['label']} — saved something wrong? You can undo it for "
               f"{UNDO_MINUTES} minutes.")
    if c2.button("↩️ Undo last save", key=f"undo_{kind}", width="stretch"):
        try:
            modify_csv(u["file"], u["cols"], lambda df: df[df[u["idcol"]] != u["id"]])
            audit(f"{kind} undone", u["label"])
            st.session_state.pop(f"_undo_{kind}", None)
            st.session_state.pop(f"_sig_{kind}", None)
            st.session_state[flash_key] = f"↩️ Undone: {u['label']}"
            _rerun_here()
        except Exception as e:
            st.error(f"Not undone: {e}")


def draft_grid(default_rows, buns, key, **kw):
    """The Excel-like editor, but what you typed is KEPT when you open another page and come back.
    Returns (rows, restored_from_draft)."""
    bases = st.session_state.setdefault("_grid_base", {})
    drafts = st.session_state.setdefault("_grid_draft", {})
    restored = False
    if key not in st.session_state:                      # shown for the first time, or back from another page
        d = drafts.get(key)
        restored = bool(d) and any(v for _d, v in d)
        bases[key] = d if restored else default_rows
    ed = _grid(bases[key], buns, key, **kw)
    rows = _grid_values(ed, buns)
    drafts[key] = rows
    return rows, restored


def drop_draft(*keys):
    for k in keys:
        st.session_state.get("_grid_base", {}).pop(k, None)
        st.session_state.get("_grid_draft", {}).pop(k, None)


def _grid_values(df, buns):
    """Editor rows -> [(date, {bun: pcs})] (rows without a date or pcs are skipped)."""
    out = []
    for r in df.to_dict("records"):
        try:
            ts = pd.Timestamp(r.get("Production date"))
        except (ValueError, TypeError):
            continue
        if pd.isna(ts):
            continue
        d = ts.date()
        vals = {b: int(_num(r.get(short(b)))) for b in buns if _num(r.get(short(b))) > 0}
        out.append((d, vals))
    return out


def _grid(rows, buns, key, height=None, max_date=None):
    """Excel-like editor: one row per production date, one column per bun (your short names)."""
    rows = list(rows) or [(max_date or today_kh(), {})]         # never an empty table: one row to start typing
    data = [{"Production date": d, **{short(b): (int(v[b]) if v.get(b) else None) for b in buns}} for d, v in rows]
    df = pd.DataFrame(data, columns=["Production date"] + [short(b) for b in buns])
    df["Production date"] = pd.to_datetime(df["Production date"])
    for b in buns:                    # digits as text: an empty cell stays really empty (no grey 'None')
        df[short(b)] = pd.Series(["" if v is None or pd.isna(v) else str(int(v)) for v in df[short(b)]],
                                 index=df.index, dtype="string")
    cfg = {"Production date": st.column_config.DateColumn("Date", format="ddd, MMM/DD, YY", max_value=max_date,
                                                          required=True, width="medium")}
    for b in buns:
        cfg[short(b)] = st.column_config.TextColumn(short(b), help=f"{b} — pcs (numbers only)", width="small",
                                                    validate=r"^[0-9]{0,6}$", max_chars=6)
    return st.data_editor(df, key=key, num_rows="dynamic", hide_index=True, width="stretch", column_config=cfg,
                          height=height or min(80 + 35 * (len(df) + 1), 560))


def page_production(cfg, can_edit, me):
    st.subheader("🏭 Log production")
    prod, _rev = read_csv(PROD_FILE, PROD_COLS)
    _p, _c, _a, sales, names, buns = get_data(cfg)
    show = active_buns(buns, sales)
    show_flash("p_flash")
    if can_edit:
        phone = st.session_state.get("phone_mode")
        st.markdown("Type the pcs produced for each bun. **Empty = 0.**" if phone else
                    "Type the pcs produced like in your Excel sheet — **one row per production date** "
                    "(add a row with ＋ for another day). Empty = 0.")
        n = st.session_state.get("prod_grid_n", 0)
        gkey = f"prod_grid_{n}"
        if phone:
            dr = st.session_state.get("_pp_draft") or {}
            dr = dr if dr.get("n") == n else {}
            pdate = st.date_input("📅 Production date", value=dr.get("date") or today_kh(),
                                  max_value=today_kh() + timedelta(days=1), key=f"pp_date_{n}")
            vals = bun_inputs(show, names, dr.get("vals") or {}, key=f"pp_{n}")
            st.session_state["_pp_draft"] = {"n": n, "date": pdate, "vals": vals}
            got = [(pdate, vals)] if vals else []
            if got:
                st.info(f"📝 Not saved yet · {day_label(pdate)} · **{sum(vals.values()):,} pcs** · "
                        + " · ".join(f"{short(b)} {v:,}" for b, v in vals.items()))
        else:
            rows, restored = draft_grid([(today_kh(), {})], show, gkey, height=120,
                                        max_date=today_kh() + timedelta(days=1))
            got = [(d, v) for d, v in rows if v]
            if restored:
                st.info("📝 Your numbers from before are still here — they are NOT saved yet.")
            if got:
                st.markdown(excel_html("ផលិតថ្មី (📝 not saved yet)", [(day_label(d), v) for d, v in got], show),
                            unsafe_allow_html=True)
        # same day + bun already logged? (a second save ADDS — warn so nothing is counted twice)
        if got and not prod.empty:
            have = prod.assign(_n=prod["Pcs"].map(_num).astype(float))
            dup = []
            for d, vals in got:
                for b in vals:
                    m = have[(have["Prod_Date"] == d.isoformat()) & (have["Bun"] == b)]
                    if len(m):
                        dup.append(f"{d:%d %b} {short(b)} {int(m['_n'].sum()):,} pcs "
                                   f"({', '.join(sorted(set(m['By'])))} {str(m['Saved_At'].iloc[-1])[11:16]})")
            if dup:
                st.warning("ℹ️ Already saved before: " + " · ".join(dup[:8]) + (" …" if len(dup) > 8 else "")
                           + " — saving now **adds** these pcs. If it is the same production, do not save again.")
        team_opts = list(dict.fromkeys(ops_names(cfg) + [me]))
        team = st.multiselect("👷 Produced by", team_opts, default=[me], key=f"prod_team_{n}",
                              help="Everyone who made these buns (Admin adds names in ⚙️ Settings).")
        c1, c2 = st.columns([3, 1])
        note = c1.text_input("Note (optional)", max_chars=120, key=f"prod_note_{n}")
        c2.write("")
        total_new = sum(v for _d, vals in got for v in vals.values())
        clicked = c2.button(f"💾 Save {total_new:,} pcs" if got else "💾 Save production", type="primary",
                            width="stretch", disabled=not got or not team, key=f"prod_save_{n}")
        if not got:
            st.caption("Type at least one number to save.")
        elif not team:
            st.caption("Choose who produced these buns (👷 Produced by).")
        if clicked:
            sig = json.dumps([(d.isoformat(), sorted(v.items())) for d, v in got])
            if not save_guard("production", sig):
                st.info("✅ This was already saved a moment ago — it is not saved twice.")
            else:
                stamp, eid = now_kh().strftime("%Y-%m-%d %H:%M:%S"), uuid.uuid4().hex[:10]
                new = pd.DataFrame([{"Saved_At": stamp, "Prod_Date": d.isoformat(), "Bun": b, "Pcs": str(int(v)),
                                     "By": me, "Note": note.strip(), "Entry_Id": eid, "Team": "; ".join(team)}
                                    for d, vals in got for b, v in vals.items()])
                try:
                    modify_csv(PROD_FILE, PROD_COLS, lambda df: pd.concat([df, new], ignore_index=True))
                    label = (f"{total_new:,} pcs · " + ", ".join(f"{d:%d %b}" for d, _v in got))
                    audit("production saved", "; ".join(f"{d:%d %b}: " + ", ".join(f"{short(b)} {v}" for b, v in vals.items())
                                                        for d, vals in got) + f" | by {', '.join(team)}")
                    remember_undo("production", PROD_FILE, PROD_COLS, "Entry_Id", eid, label)
                    st.session_state["p_flash"] = f"✅ Saved {label}"
                    st.session_state["prod_grid_n"] = n + 1           # empty sheet for the next entry
                    st.session_state.pop("_pp_draft", None)
                    drop_draft(gkey)
                    _rerun_here()
                except Exception as e:
                    st.session_state.pop("_sig_production", None)    # not saved: the next tap may save
                    st.error(f"Not saved: {e}")
        undo_bar("production", "p_flash")
    else:
        st.info("👁️ View only — ask Admin for edit access to log production.")
    st.markdown("**📋 Production logged**")
    c1, c2 = st.columns(2)
    d_from = c1.date_input("From", value=today_kh() - timedelta(days=6), key="pl_from")
    d_to = c2.date_input("To", value=today_kh(), key="pl_to")
    prod = prod.copy()
    prod["_d"] = prod["Prod_Date"].map(_day)
    view = prod[(prod["_d"] >= d_from) & (prod["_d"] <= d_to)] if not prod.empty else prod
    if view.empty:
        st.info("Nothing logged in these dates.")
        return
    view = view.assign(_n=view["Pcs"].map(_num).astype(float))
    by_day = view.groupby(["_d", "Bun"])["_n"].sum()
    rows = [(day_label(d), {b: by_day.get((d, b), 0) for b in show}) for d in sorted(set(view["_d"]))]
    st.markdown(excel_html(f"ផលិត ({d_from:%d.%m} – {d_to:%d.%m.%Y})", rows, show), unsafe_allow_html=True)
    with st.expander(f"✏️ Fix or delete a saved line ({len(view)} lines)"):
        mine = view if st.session_state.get("p_role") == "admin" else view[view["By"] == me]
        if not can_edit or mine.empty:
            st.caption("Only your own lines (Admin: all) can be changed here.")
            return
        ed = st.data_editor(mine[["Saved_At", "Prod_Date", "Bun", "Pcs", "By", "Team", "Note", "Entry_Id"]].assign(Delete=False),
                            hide_index=True, width="stretch", key="prod_fix",
                            disabled=["Saved_At", "By", "Team", "Entry_Id", "Bun"],
                            column_config={"Pcs": st.column_config.NumberColumn(min_value=0, step=10),
                                           "Delete": st.column_config.CheckboxColumn("🗑️ Delete")})
        if st.button("💾 Save fixes", key="prod_fix_save"):
            changes = {(r["Entry_Id"], r["Bun"], r["Prod_Date"]): r for r in ed.to_dict("records")}

            def apply(df):
                keep = []
                for _, r in df.iterrows():
                    k = (r["Entry_Id"], r["Bun"], r["Prod_Date"])
                    if k in changes:
                        c = changes[k]
                        if c["Delete"]:
                            continue
                        r["Pcs"], r["Note"] = str(int(_num(c["Pcs"]))), c["Note"]
                    keep.append(r)
                return pd.DataFrame(keep, columns=PROD_COLS)
            try:
                modify_csv(PROD_FILE, PROD_COLS, apply)
                old = {(r["Entry_Id"], r["Bun"], r["Prod_Date"]): r for r in mine.to_dict("records")}
                audit("production fixed", "; ".join(
                    f"{k[2]} {short(k[1])}: " + ("deleted" if c["Delete"] else f"{old[k]['Pcs']} → {int(_num(c['Pcs']))}")
                    for k, c in changes.items() if k in old and (c["Delete"] or str(int(_num(c["Pcs"]))) != str(old[k]["Pcs"]))))
                st.session_state["p_flash"] = "✅ Fixes saved"
                _rerun_here()
            except Exception as e:
                st.error(f"Not saved: {e}")


def _place_of(row, places):
    p = str(row.get("Place", "") or "").strip()
    if p:
        return p
    return places[1] if len(places) > 1 and "ទូរកក" in str(row.get("By", "")) else places[0]


def last_place_counts(counts, places):
    """{place: (count_date, {(prod_date, bun): pcs})} — the newest count of each freezer."""
    out = {}
    if counts.empty:
        return out
    c = counts.copy()
    c["_cd"] = c["Count_Date"].map(_day)
    c = c[c["_cd"].notna()]
    c["_pl"] = [_place_of(r, places) for r in c.to_dict("records")]
    for pl, g in c.groupby("_pl"):
        g = g.sort_values(["_cd", "Saved_At"])
        last = g[g["Count_Id"] == g["Count_Id"].iloc[-1]]
        vals = {}
        for r in last.to_dict("records"):
            pd_ = _day(r["Prod_Date"])
            if pd_ and _num(r["Pcs"]) > 0:
                vals[(pd_, r["Bun"])] = vals.get((pd_, r["Bun"]), 0) + _num(r["Pcs"])
        out[pl] = (last["_cd"].iloc[0], vals)
    return out


def count_sheet_excel(places, sheets, buns, cd):
    """Printable count sheet in your layout (one sheet per freezer), pre-filled."""
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
    wb = Workbook()
    wb.remove(wb.active)
    thin = Side(style="thin", color="333333")
    box = Border(left=thin, right=thin, top=thin, bottom=thin)
    fill = lambda c: PatternFill("solid", fgColor=c.replace("#", ""))
    for pl in places:
        ws = wb.create_sheet(re.sub(r"[\[\]\*\?/\\:]", "", pl)[:28] or "Count")
        rows = sheets.get(pl, [])
        n = len(buns)
        ws.cell(1, 1, f"{pl}({cd:%d.%m.%Y})").font = Font(bold=True, size=13)
        ws.cell(2, 1, "Date").font = Font(bold=True)
        ws.merge_cells(start_row=2, start_column=2, end_row=2, end_column=1 + n)
        ws.cell(2, 2, f"{pl} ({cd:%d.%m.%Y})").alignment = Alignment(horizontal="center")
        ws.cell(2, 2 + n, "សរុប")
        ws.cell(3, 1, "Item")
        for i, b in enumerate(buns):
            ws.cell(3, 2 + i, short(b))
        for c in range(1, 3 + n):
            for r in (2, 3):
                cell = ws.cell(r, c)
                cell.border, cell.font = box, Font(bold=True, size=12)
                cell.alignment = Alignment(horizontal="center", vertical="center")
                cell.fill = fill(HEAD_BG if r == 2 else (COLORS.get(buns[c - 2], "#FFFFFF") if 1 < c < 2 + n
                                                          else ("#FFFF00" if c == 2 + n else "#FFFFFF")))
        body = list(rows) + [(None, {})] * 4                     # 4 empty lines to write new dates
        for j, (d, vals) in enumerate(body):
            r = 4 + j
            ws.cell(r, 1, day_label(d) if d else "")
            for i, b in enumerate(buns):
                ws.cell(r, 2 + i, int(vals[b]) if vals.get(b) else None)
            ws.cell(r, 2 + n, f"=SUM(B{r}:{ws.cell(r, 1 + n).column_letter}{r})")
            for c in range(1, 3 + n):
                cell = ws.cell(r, c)
                cell.border, cell.number_format = box, "#,##0"
                cell.alignment = Alignment(horizontal="center")
                cell.fill = fill(COLORS.get(buns[c - 2], "#FFFFFF") if 1 < c < 2 + n else (TOTAL_BG if c == 2 + n else "#FFFFFF"))
        tr = 4 + len(body)
        for c in range(2, 3 + n):
            L = ws.cell(tr, c).column_letter
            cell = ws.cell(tr, c, f"=SUM({L}4:{L}{tr - 1})")
            cell.border, cell.font, cell.number_format = box, Font(bold=True), "#,##0"
            cell.alignment, cell.fill = Alignment(horizontal="center"), fill(SUM_BG if c < 2 + n else TOTAL_BG)
        ws.column_dimensions["A"].width = 18
        for c in range(2, 3 + n):
            ws.column_dimensions[ws.cell(1, c).column_letter].width = 9
        ws.freeze_panes = "B4"
    buf = io.BytesIO()
    wb.save(buf)
    return buf.getvalue()


def _count_phone(places, start_rows, show, names, cd, sig):
    """Phone: one freezer, one production date at a time, big number boxes, ✅ Counted · next."""
    dk = "cntp_" + sig
    if dk not in st.session_state:
        st.session_state[dk] = {"data": {pl: {d: dict(v) for d, v in start_rows[pl]} for pl in places},
                                "done": {pl: [] for pl in places}, "idx": {pl: 0 for pl in places}}
    S = st.session_state[dk]
    if S.get("goto_pl"):
        st.session_state[dk + "_pl"] = S.pop("goto_pl")       # set before the picker is drawn
    pl = st.radio("🧊 Freezer", places, horizontal=True, key=dk + "_pl")      # fixed labels: the choice never jumps
    st.caption(" · ".join(f"{x}: {len(S['done'][x])}/{max(len(S['data'][x]), 1)} ✅" for x in places))
    data, done = S["data"][pl], S["done"][pl]
    if not data:
        data[cd] = {}
    dates = sorted(data)
    i = min(S["idx"][pl], len(dates) - 1)
    st.progress(sum(1 for x in dates if x in done) / len(dates),
                text=f"{sum(1 for x in dates if x in done)} of {len(dates)} production dates counted in {pl}")
    d = st.selectbox("📅 Production date", dates, index=i, key=f"{dk}_{pl}_sel_{i}_{len(dates)}",
                     format_func=lambda x: f"{'✅' if x in done else '⬜'} {day_label(x)} · {sum(data[x].values()):,} pcs")
    S["idx"][pl] = dates.index(d)
    i = S["idx"][pl]
    with st.container(border=True):
        st.markdown(f"**{pl} · {day_label(d)}** — type what you see. Empty = 0.")
        data[d] = bun_inputs(show, names, data[d], key=f"{dk}_{pl}_{d}", step=1)
        st.markdown(f"**សរុប {sum(data[d].values()):,} pcs**")
    b1, b2 = st.columns(2)
    if b1.button("⬅️ Back", key=f"{dk}_back", disabled=i == 0, width="stretch"):
        S["idx"][pl] = i - 1
        _rerun_here()
    last = i == len(dates) - 1
    if b2.button("✅ Counted · next ➡️" if not last else "✅ Counted (last date)", key=f"{dk}_next", type="primary",
                 width="stretch"):
        if d not in done:
            done.append(d)
        if not last:
            S["idx"][pl] = i + 1
        else:
            nxt = [x for x in places if len(S["done"][x]) < len(S["data"][x])]
            if nxt and nxt[0] != pl:
                S["goto_pl"] = nxt[0]                             # go on with the next freezer
        _rerun_here()
    with st.expander("➕ Add a production date that is missing"):
        nd = st.date_input("Production date", value=cd, max_value=cd, key=f"{dk}_{pl}_newd")
        if st.button("➕ Add this date", key=f"{dk}_{pl}_add"):
            data.setdefault(nd, {})
            S["idx"][pl] = sorted(data).index(nd)
            _rerun_here()
    if sum(len(S["done"][x]) for x in places) == sum(len(S["data"][x]) for x in places):
        st.success("🎉 All freezers and dates counted — check the totals below and press 💾 Save.")
    return {x: sorted((dd, {b: v for b, v in vals.items() if v}) for dd, vals in S["data"][x].items()) for x in places}


def page_count(cfg, can_edit, me):
    st.subheader("📦 Evening stock count")
    prod, counts, adjs, sales, names, buns = get_data(cfg)
    places = list(cfg.get("places") or DEFAULT_SETTINGS["places"])
    show_flash("c_flash")
    c1, c2 = st.columns([1, 2])
    cd = c1.date_input("Count date (stock at the END of this day)", value=today_kh(), max_value=today_kh(), key="cnt_date")
    expected, _short, _h, _nc = compute_stock(buns, prod, counts, adjs, sales, cd)
    show = active_buns(buns, sales, expected)
    lastp = last_place_counts(counts, places)
    c2.caption("Count every freezer in the evening, after the last delivery. It starts filled in with what the app "
               "expects — **only change the numbers that are different**, add a date that is missing, empty a box "
               "that is empty in the freezer." + (" On the phone: one freezer and one production date at a time."
                                                  if st.session_state.get("phone_mode") else
                                                  " Each tab is one freezer, laid out like your Excel sheet."))
    # what each freezer probably holds now: other freezers = their last count, the first freezer = the rest
    other = {}
    for pl in places[1:]:
        for (d, b), v in lastp.get(pl, (None, {}))[1].items():
            if d <= cd:
                other[(d, b)] = other.get((d, b), 0) + v
    start_rows = {}
    for i, pl in enumerate(places):
        if i == 0:
            vals = {}
            for b in show:
                for d, v in expected.get(b, {}).items():
                    rest = v - other.get((d, b), 0)
                    if rest >= 0.5:
                        vals.setdefault(d, {})[b] = round(rest)
            vals.setdefault(cd, {})
        else:
            vals = {}
            for (d, b), v in lastp.get(pl, (None, {}))[1].items():
                if b in show and d <= cd:
                    vals.setdefault(d, {})[b] = v
        start_rows[pl] = sorted(vals.items())
    mode = st.radio("Start the sheets from", ["🧮 What the app expects (recommended)", "⬜ Empty sheets"],
                    horizontal=True, key="cnt_mode")
    if mode.startswith("⬜"):
        start_rows = {pl: [(cd, {})] for pl in places}
    if st.session_state.get("phone_mode"):
        counted = _count_phone(places, start_rows, show, names, cd,
                               f"{cd}_{mode[:2]}_{st.session_state.get('cnt_n', 0)}")
        st.markdown("#### ✅ Check & save")
        check_box = st.container()
    else:
        st.caption("➡️ Count each freezer tab, then open **✅ Check & save** to save. What you type is kept if you "
                   "open another page and come back.")
        tabs = st.tabs([f"🧊 {pl}" for pl in places] + ["✅ Check & save"])
        counted, any_restored = {}, False
        for i, (pl, tab) in enumerate(zip(places, tabs)):
            with tab:
                gk = f"cnt_{pl}_{cd}_{mode[:2]}_{st.session_state.get('cnt_n', 0)}"
                counted[pl], restored = draft_grid(start_rows[pl], show, gk, max_date=cd)
                any_restored = any_restored or restored
                st.markdown(excel_html(f"{pl} ({cd:%d.%m.%Y})", [(day_label(d), v) for d, v in sorted(counted[pl])], show),
                            unsafe_allow_html=True)
                nxt = f"🧊 {places[i + 1]}" if i + 1 < len(places) else "✅ Check & save"
                st.caption(f"➡️ Next: open the **{nxt}** tab above.")
        if any_restored:
            st.info("📝 Your count from before is still here — it is NOT saved yet.")
        check_box = tabs[-1]
    with check_box:
        tot_c = {b: sum(v.get(b, 0) for pl in places for _d, v in counted[pl]) for b in show}
        tot_e = {b: sum(expected.get(b, {}).values()) for b in show}
        chk = pd.DataFrame([{"Bun": short(b), "Code": b, "App expected": int(round(tot_e[b])), "Counted": int(tot_c[b]),
                             "Difference": int(tot_c[b] - round(tot_e[b]))} for b in show])
        chk.loc[len(chk)] = ["សរុប", "", int(chk["App expected"].sum()), int(chk["Counted"].sum()), int(chk["Difference"].sum())]
        st.dataframe(chk.style.map(lambda v: "color:#c62828;font-weight:700" if isinstance(v, (int, float)) and v < 0
                                   else ("color:#2e7d32;font-weight:700" if isinstance(v, (int, float)) and v > 0 else ""),
                                   subset=["Difference"]), hide_index=True, width="stretch")
        st.caption("Difference = counted − what the app expected from the last count + production − journal sales. "
                   "A big minus = sold/taken without invoice, damaged, or production not logged.")
        all_rows = {}
        for pl in places:
            for d, v in counted[pl]:
                for b, n in v.items():
                    all_rows[(d, b)] = all_rows.get((d, b), 0) + n
        st.markdown(excel_html(f"ស្តុកនំសរុប ({cd:%d.%m.%Y}) — all freezers",
                               [(day_label(d), {b: all_rows.get((d, b), 0) for b in show})
                                for d in sorted({d for d, _b in all_rows})], show), unsafe_allow_html=True)
        if can_edit:
            # a count for this day already saved? (saving again replaces it — say so)
            same = counts[counts["Count_Date"] == cd.isoformat()] if not counts.empty else counts
            if len(same):
                lastc = same[same["Count_Id"] == same.sort_values("Saved_At")["Count_Id"].iloc[-1]]
                st.warning(f"ℹ️ A count for {cd:%d %b %Y} was already saved at {str(lastc['Saved_At'].iloc[0])[11:16]} "
                           f"by {', '.join(sorted(set(lastc['By'])))} ({int(lastc['Pcs'].map(_num).astype(float).sum()):,} pcs). "
                           "Saving again **replaces** it with the numbers here.")
            # big differences: ask for one more look before saving
            exp_all = sum(tot_e.values())
            big = [b for b in show if abs(tot_c[b] - tot_e[b]) > max(300, 0.15 * tot_e[b])]
            big_total = abs(sum(tot_c.values()) - exp_all) > max(500, 0.03 * exp_all)
            ok_big = True
            if big or big_total:
                st.warning("⚠️ Big difference from what the app expected: " + ", ".join(
                    f"{short(b)} {int(tot_c[b] - round(tot_e[b])):+,}" for b in big[:8])
                    + (f" · total {int(sum(tot_c.values()) - round(exp_all)):+,} pcs" if big_total else "")
                    + ". Check those buns once more (a missing date? a typo?).")
                ok_big = st.checkbox("✔️ I checked these numbers — they are right", key=f"cnt_ok_{st.session_state.get('cnt_n', 0)}")
            clicked = st.button(f"💾 Save the evening count ({int(sum(tot_c.values())):,} pcs)", type="primary",
                                key="cnt_save", disabled=not ok_big, width="stretch")
            undo_bar("count", "c_flash")
            sig = json.dumps([cd.isoformat()] + [(pl, [(d.isoformat(), sorted(v.items())) for d, v in sorted(counted[pl])])
                                                 for pl in places])
            if clicked and not save_guard("count", sig):
                st.info("✅ This count was already saved a moment ago — it is not saved twice.")
            elif clicked:
                cid, stamp = uuid.uuid4().hex[:10], now_kh().strftime("%Y-%m-%d %H:%M:%S")
                new = [{"Saved_At": stamp, "Count_Date": cd.isoformat(), "Bun": b, "Prod_Date": d.isoformat(),
                        "Pcs": str(int(n)), "By": me, "Count_Id": cid, "Place": pl}
                       for pl in places for d, v in counted[pl] for b, n in v.items()]
                have = {r["Bun"] for r in new}
                new += [{"Saved_At": stamp, "Count_Date": cd.isoformat(), "Bun": b, "Prod_Date": cd.isoformat(), "Pcs": "0",
                         "By": me, "Count_Id": cid, "Place": places[0]} for b in buns if b not in have]   # counted empty
                try:
                    modify_csv(COUNT_FILE, COUNT_COLS, lambda df: pd.concat([df, pd.DataFrame(new)], ignore_index=True))
                    audit("evening count saved", f"{cd:%d %b %Y}: {int(sum(tot_c.values())):,} pcs · " + ", ".join(
                        f"{short(b)} {int(tot_c[b])} ({int(tot_c[b] - round(tot_e[b])):+d})" for b in show if tot_c[b] or tot_e[b]))
                    label = f"count {cd:%d %b %Y} · {int(sum(tot_c.values())):,} pcs"
                    remember_undo("count", COUNT_FILE, COUNT_COLS, "Count_Id", cid, label)
                    st.session_state["c_flash"] = f"✅ Evening count saved for {cd:%d %b %Y}: {int(sum(tot_c.values())):,} pcs"
                    drop_draft(*[f"cnt_{pl}_{cd}_{mode[:2]}_{st.session_state.get('cnt_n', 0)}" for pl in places])
                    st.session_state["cnt_n"] = st.session_state.get("cnt_n", 0) + 1
                    _rerun_here()
                except Exception as e:
                    st.session_state.pop("_sig_count", None)
                    st.error(f"Not saved: {e}")
        else:
            st.info("👁️ View only — ask Admin for edit access to save a count.")
        st.download_button("📥 Count sheet for printing (Excel, your layout)",
                           data=count_sheet_excel(places, {pl: sorted(counted[pl]) for pl in places}, show, cd),
                           file_name=f"Stock_count_{cd:%Y-%m-%d}.xlsx", key="cnt_xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    lc = latest_counts(counts)
    if lc:
        st.caption("Last saved count: " + ", ".join(sorted({f"{v[0]:%d %b %Y}" for v in lc.values()})))
    st.divider()
    st.markdown("**➕➖ Adjustment** — buns that leave or enter stock without a sale invoice "
                "(damaged, samples, staff meals, returned...).")
    if can_edit:
        with st.form("adj_form", clear_on_submit=True):
            c1, c2, c3, c4 = st.columns([1.3, 1, 1, 1.4])
            b = c1.selectbox("Bun", [bun_label(x, names) for x in buns])
            kind = c2.radio("Type", ["➖ Remove", "➕ Add"], horizontal=False)
            n = c3.number_input("Pcs", min_value=1, max_value=100000, step=10)
            d = c4.date_input("Date", value=today_kh(), max_value=today_kh())
            c5, c6 = st.columns([1, 2])
            pdte = c5.date_input("Batch production date (optional)", value=None)
            reason = c6.selectbox("Reason", ["Damaged / broken", "Expired / old", "Sample / FOC not in journal",
                                             "Staff meal", "Returned by customer", "Other"])
            ok = st.form_submit_button("💾 Save adjustment")
        if ok:
            code = {bun_label(x, names): x for x in buns}[b]
            row = {"Saved_At": now_kh().strftime("%Y-%m-%d %H:%M:%S"), "Date": d.isoformat(), "Bun": code,
                   "Prod_Date": pdte.isoformat() if pdte else "", "Pcs": str(int(n if kind.startswith("➕") else -n)),
                   "Reason": reason, "By": me, "Adj_Id": uuid.uuid4().hex[:10]}
            if not save_guard("adjustment", json.dumps([row["Date"], code, row["Pcs"], reason])):
                st.info("✅ This adjustment was already saved a moment ago — it is not saved twice.")
            else:
                try:
                    modify_csv(ADJ_FILE, ADJ_COLS, lambda df: pd.concat([df, pd.DataFrame([row])], ignore_index=True))
                    audit("adjustment", f"{row['Date']} {short(code)} {row['Pcs']} pcs · {reason}")
                    remember_undo("adjustment", ADJ_FILE, ADJ_COLS, "Adj_Id", row["Adj_Id"],
                                  f"{kind[2:]} {n:,} pcs {short(code)} · {reason}")
                    st.session_state["c_flash"] = f"✅ Adjustment saved: {kind[2:]} {n:,} pcs {b}"
                    _rerun_here()
                except Exception as e:
                    st.session_state.pop("_sig_adjustment", None)
                    st.error(f"Not saved: {e}")
        undo_bar("adjustment", "c_flash")
    if not adjs.empty:
        recent = adjs.sort_values("Saved_At", ascending=False).head(50)
        mine = recent if st.session_state.get("p_role") == "admin" else recent[recent["By"] == me]
        st.dataframe(recent[["Date", "Bun", "Prod_Date", "Pcs", "Reason", "By"]], hide_index=True, width="stretch")
        if can_edit and not mine.empty:
            with st.expander("🗑️ Delete a wrong adjustment" + ("" if st.session_state.get("p_role") == "admin"
                                                              else " (your own lines)")):
                ed = st.data_editor(mine[["Saved_At", "Date", "Bun", "Pcs", "Reason", "By", "Adj_Id"]].assign(Delete=False),
                                    hide_index=True, width="stretch", key="adj_del",
                                    disabled=["Saved_At", "Date", "Bun", "Pcs", "Reason", "By", "Adj_Id"],
                                    column_config={"Adj_Id": None, "Delete": st.column_config.CheckboxColumn("🗑️ Delete")})
                gone = [r for r in ed.to_dict("records") if r["Delete"]]
                if st.button(f"🗑️ Delete {len(gone)} line(s)", key="adj_del_save", disabled=not gone):
                    ids = {r["Adj_Id"] for r in gone}
                    try:
                        modify_csv(ADJ_FILE, ADJ_COLS, lambda df: df[~df["Adj_Id"].isin(ids)])
                        audit("adjustment deleted", "; ".join(f"{r['Date']} {short(r['Bun'])} {r['Pcs']} · {r['Reason']}"
                                                              for r in gone))
                        st.session_state["c_flash"] = f"🗑️ Deleted {len(gone)} adjustment line(s)"
                        _rerun_here()
                    except Exception as e:
                        st.error(f"Not deleted: {e}")


def plan_excel(plan, buns, names, start, days, cfg):
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
    from openpyxl.utils import get_column_letter
    wb = Workbook()
    ws = wb.active
    ws.title = "Production plan"
    dates = [start + timedelta(days=i) for i in range(days)]
    thin = Side(style="thin", color="999999")
    box = Border(left=thin, right=thin, top=thin, bottom=thin)
    head = PatternFill("solid", fgColor="0F766E")
    ws.cell(1, 1, f"កាលវិភាគផលិតប្រចាំសប្តាហ៍ · Weekly production schedule {dates[0]:%d %b} – {dates[-1]:%d %b %Y}").font = Font(bold=True, size=14)
    ws.cell(2, 1, f"Targets: N1/N2 {cfg['target_days'].get('N1', 6)} days, others {cfg['target_default']} days · "
                  f"total stock ≤ {int(cfg['max_total']):,} pcs · made {now_kh():%d %b %Y %H:%M}").font = Font(italic=True, size=9)
    hdr = ["Code", "Bun"] + [f"{KH_DAYS[d.weekday()]}\n{d:%d/%m}" for d in dates] + ["TOTAL", "Stock end"]
    for c, v in enumerate(hdr, 1):
        cell = ws.cell(4, c, v)
        cell.font, cell.fill, cell.border = Font(bold=True, color="FFFFFF"), head, box
        cell.alignment = Alignment(horizontal="center", vertical="center", wrap_text=True)
    ws.row_dimensions[4].height = 32
    p = plan.pivot_table(index="Bun", columns="Date", values="Produce", aggfunc="sum")
    e = plan.pivot_table(index="Bun", columns="Date", values="Stock end of day", aggfunc="sum")
    for r, b in enumerate(buns, 5):
        vals = [int(p.at[b, d]) if b in p.index and d in p.columns else 0 for d in dates]
        row = [b, names.get(b, "")] + [v or None for v in vals] + [sum(vals), int(e.at[b, dates[-1]]) if b in e.index else 0]
        for c, v in enumerate(row, 1):
            cell = ws.cell(r, c, v)
            cell.border = box
            if c > 2:
                cell.number_format = "#,##0"
                cell.alignment = Alignment(horizontal="center")
            if b in cfg.get("priority", []):
                cell.fill = PatternFill("solid", fgColor="E6F4F1")
    tr = 5 + len(buns)
    ws.cell(tr, 1, "TOTAL").font = Font(bold=True)
    for c in range(3, 3 + days + 2):
        col = get_column_letter(c)
        cell = ws.cell(tr, c, f"=SUM({col}5:{col}{tr - 1})")
        cell.font, cell.border, cell.number_format = Font(bold=True), box, "#,##0"
        cell.alignment = Alignment(horizontal="center")
    ws.column_dimensions["A"].width, ws.column_dimensions["B"].width = 8, 14
    for c in range(3, 3 + days + 2):
        ws.column_dimensions[get_column_letter(c)].width = 11
    ws.freeze_panes = "C5"
    det = wb.create_sheet("Detail")
    det.append(["Date", "Day", "Bun", "Produce", "Expected sales", "Stock end of day"])
    for r in plan.itertuples(index=False):
        det.append([r.Date, EN_DAYS[r.Date.weekday()], r.Bun, r.Produce, r._3, r._4])
    buf = io.BytesIO()
    wb.save(buf)
    return buf.getvalue()


def page_plan(cfg, can_edit):
    st.subheader("📅 Next week production plan")
    prod, counts, adjs, sales, names, buns = get_data(cfg)
    t = today_kh()
    nxt_mon = t + timedelta(days=(7 - t.weekday()) % 7 or 7)
    c1, c2 = st.columns(2)
    start = c1.date_input("Plan from", value=t + timedelta(days=1), min_value=t, key="plan_start",
                          help="The plan starts from the stock you have now. Plan from tomorrow so the days before "
                               "next week are counted too.")
    end = c2.date_input("Plan until", value=nxt_mon + timedelta(days=6), min_value=start, key="plan_end")
    days = (end - start).days + 1
    batches, _short, _h, no_count = compute_stock(buns, prod, counts, adjs, sales, t)
    stock_now = {b: sum(v.values()) for b, v in batches.items()}
    # what is still logged as produced for the days of the plan (e.g. tomorrow already produced) is not planned again
    fc = forecast(sales, buns, start, days + 14, int(cfg["lookback_days"]))
    if start > t + timedelta(days=1):                         # days between today and the plan start
        gap = forecast(sales, buns, t + timedelta(days=1), (start - t).days - 1, int(cfg["lookback_days"]))
        for b in buns:
            stock_now[b] = max(stock_now[b] - sum(gap.get((t + timedelta(days=i + 1), b), 0)
                                                  for i in range((start - t).days - 1)), 0)
    plan = plan_production(buns, stock_now, fc, start, days, cfg)
    if no_count:
        st.warning("No stock count yet for " + ", ".join(no_count) + " — the plan treats their stock as 0.")
    dates = [start + timedelta(days=i) for i in range(days)]
    piv = plan.pivot_table(index="Bun", columns="Date", values="Produce", aggfunc="sum").reindex(buns)
    piv.columns = [f"{EN_DAYS[d.weekday()]} {d:%d/%m}" for d in piv.columns]
    piv.insert(0, "Bun", [names.get(b, "") for b in piv.index])
    piv["TOTAL"] = piv.drop(columns=["Bun"]).sum(axis=1)
    last = plan[plan["Date"] == dates[-1]].set_index("Bun")
    sp, _n = sales_speed(sales, buns, t, int(cfg["lookback_days"]))
    piv["Stock now"] = [int(stock_now.get(b, 0)) for b in piv.index]
    piv["Stock at the end"] = [int(last.at[b, "Stock end of day"]) for b in piv.index]
    piv["Days at the end"] = [round(last.at[b, "Stock end of day"] / sp[b], 1) if sp.get(b) else None for b in piv.index]
    tot_row = piv.drop(columns=["Bun"]).sum(numeric_only=True)
    tot_row["Days at the end"] = None
    piv.loc["TOTAL"] = ["", *tot_row.values]
    day_cols = [c for c in piv.columns if c not in ("Bun", "Days at the end")]
    piv = piv[[bool((i == "TOTAL") or sp.get(i) or stock_now.get(i)) for i in piv.index]]   # hide buns not sold and not in stock
    for c in day_cols:
        piv[c] = ["" if (pd.isna(v) or v == 0) else f"{int(v):,}" for v in piv[c]]
    piv["Days at the end"] = ["" if pd.isna(v) else f"{v:.1f}" for v in piv["Days at the end"]]
    st.dataframe(piv, width="stretch")
    short_days = [b for b in buns if sp.get(b) and last.at[b, "Stock end of day"] / sp[b]
                  < int(cfg["target_days"].get(b, cfg["target_default"])) - 0.5]
    if short_days:
        need_total = sum(sp[b] * int(cfg["target_days"].get(b, cfg["target_default"])) for b in buns if sp.get(b))
        st.info(f"ℹ️ Keeping every bun at its target would need about **{int(need_total):,} pcs** in stock, more than the "
                f"**{int(cfg['max_total']):,}** limit — so these buns end below their target days: "
                + ", ".join(f"{b} ({last.at[b, 'Stock end of day'] / sp[b]:.1f} d)" for b in short_days)
                + ". Raise the limit or lower the target days in ⚙️ Settings to change this.")
    daily_total = plan.groupby("Date")["Stock end of day"].sum()
    over = daily_total[daily_total > float(cfg["max_total"])]
    tiles([("🏭 To produce", f"{int(plan['Produce'].sum()):,}", f"pcs in {days} days"),
           ("🧾 Expected sales", f"{int(plan['Expected sales'].sum()):,}", "pcs (same weekday average)"),
           ("📦 Highest total stock", f"{int(daily_total.max()):,}", f"limit {int(cfg['max_total']):,}"),
           ("📦 Stock now", f"{int(sum(stock_now.values())):,}", "pcs"),
           ("✅ Limit kept", "Yes" if over.empty else f"No ({len(over)} d)", "every day")])
    st.caption("How it is planned: each day, produce so that the stock at the end of the day covers the next "
               f"{cfg['target_days'].get('N1', 6)} selling days for N1/N2 and {cfg['target_default']} for the others "
               "(expected sales = the same weekday average of the last weeks). Days a bun is not produced are covered by "
               f"the day before. If the total would pass {int(cfg['max_total']):,} pcs, the other buns are lowered first "
               "and N1/N2 keep their days.")
    with st.expander("📈 Expected total stock per day"):
        st.line_chart(pd.DataFrame({"Stock end of day": daily_total, "Limit": float(cfg["max_total"])}))
    st.download_button("📥 Download the plan (Excel)", data=plan_excel(plan, buns, names, start, days, cfg),
                       file_name=f"Production_plan_{start:%Y-%m-%d}_{end:%Y-%m-%d}.xlsx",
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", type="primary")


def _bun_rows(cfg, buns, names):
    return [{"Bun": b, "Name": names.get(b, ""),
             "Target days": int(cfg["target_days"].get(b, cfg["target_default"])),
             **{EN_DAYS[i]: i in cfg["prod_days"].get(b, cfg["prod_days_default"]) for i in range(7)},
             "Shelf life (days)": int(cfg.get("shelf_by_bun", {}).get(b, cfg["shelf_days"]))} for b in buns]


def page_settings(cfg, me):
    st.subheader("⚙️ Settings")
    _p, _c, _a, sales, names, buns = get_data(cfg)
    show_flash("s_flash")
    n = st.session_state.get("set_n", 0)
    draft = st.session_state.get("set_draft")
    if draft is None or [r["Bun"] for r in draft] != buns:
        draft = _bun_rows(cfg, buns, names)
        st.session_state["set_draft"] = draft
    bar = st.container(border=True)                       # save bar at the top (filled at the end)
    t1, t2, t3, t4 = st.tabs(["🎯 Stock rules", "🧊 Rooms & crates", "📋 Tasks & names", "👥 Users & access"])

    with t1:
        st.markdown("#### 🎯 Stock target, production days and shelf life — per bun")
        st.caption("The table is what the app uses. Change any cell, or fill many buns at once with the buttons.")
        prio_now = [b for b in cfg.get("priority", PRIORITY_DEFAULT) if b in buns]
        q1, q2, q3, q4 = st.columns([1.3, 1, 1.3, 1])
        t_all = q1.number_input(f"Target days for every bun except {', '.join(prio_now) or '-'}", min_value=1,
                                max_value=30, value=int(cfg["target_default"]), key="set_t_all")
        q2.write("")
        if q2.button("⬇️ Apply to the table", key="set_t_apply", width="stretch"):
            cur = st.session_state.get(f"set_buns_{n}_rows") or draft
            for r in cur:
                if r["Bun"] not in prio_now:
                    r["Target days"] = int(t_all)
            st.session_state["set_draft"] = cur
            st.session_state["set_n"] = n + 1
            st.rerun()
        s_all = q3.number_input("Shelf life for every bun (days)", min_value=1, max_value=365,
                                value=int(cfg["shelf_days"]), key="set_s_all")
        q4.write("")
        if q4.button("⬇️ Apply to the table", key="set_s_apply", width="stretch"):
            cur = st.session_state.get(f"set_buns_{n}_rows") or draft
            for r in cur:
                r["Shelf life (days)"] = int(s_all)
            st.session_state["set_draft"] = cur
            st.session_state["set_n"] = n + 1
            st.rerun()
        ed = st.data_editor(pd.DataFrame(draft), hide_index=True, width="stretch", num_rows="fixed",
                            disabled=["Bun", "Name"], key=f"set_buns_{n}",
                            column_config={
                                "Target days": st.column_config.NumberColumn("🎯 Target days", min_value=1, max_value=30, step=1),
                                "Shelf life (days)": st.column_config.NumberColumn("🟤 Shelf life (days)", min_value=1,
                                                                                   max_value=365, step=1),
                                **{EN_DAYS[i]: st.column_config.CheckboxColumn(EN_DAYS[i] + " 🏭") for i in range(7)}})
        st.session_state[f"set_buns_{n}_rows"] = ed.to_dict("records")       # the buttons above keep your edits
        st.caption("🏭 ticked = this bun can be produced on that weekday. 🎯 = days of sales to keep in stock. "
                   "🟤 = a batch older than this is flagged 'sell first'.")
        st.markdown("#### 📦 Limits and planning")
        c1, c2, c3, c4 = st.columns(4)
        max_total = c1.number_input("Total stock limit (pcs)", min_value=1000, max_value=1_000_000, step=1000,
                                    value=int(cfg["max_total"]), key="set_max")
        look = c2.number_input("Sales history used (days)", min_value=7, max_value=90, value=int(cfg["lookback_days"]),
                               key="set_look")
        rnd = c3.number_input("Round planned pcs up to", min_value=1, max_value=1000, value=int(cfg["round_to"]),
                              key="set_rnd")
        capp = c4.number_input("Max production per day (0 = no limit)", min_value=0, max_value=500000, step=1000,
                               value=int(cfg.get("max_prod_per_day") or 0), key="set_cap")
        prio = st.multiselect("Keep these at their target first when the total limit is reached", buns,
                              default=prio_now, key="set_prio")
        places_txt = st.text_input("Freezers counted in the evening (separate with ;)",
                                   value="; ".join(cfg.get("places") or DEFAULT_SETTINGS["places"]), key="set_places")

    with t2:
        room_vals = rooms_settings(cfg, buns, names, n)

    with t3:
        task_vals = tasks_box(cfg)

    with t4:
        st.markdown("#### 👥 Who can use this app (Admin can always edit)")
        st.caption("Automatic by role: every account with role **staff** in the Supply Hub (operation staff) gets this "
                   "access by itself — also new staff added later. Change one person only if they must be different.")
        users = load_users()
        by_role = {**DEFAULT_SETTINGS["access_by_role"], **(cfg.get("access_by_role") or {})}
        rc = st.columns(3)
        new_by_role = {}
        for col, role in zip(rc, ["staff", "sales", "viewer"]):
            new_by_role[role] = col.selectbox(f"{ROLE_TITLES[role]} (role {role})", ["edit", "view", "hidden"],
                                              index=["edit", "view", "hidden"].index(by_role.get(role, "view")),
                                              key=f"set_role_{role}")
        ov = cfg.get("access_override") or {}
        urows = [{"User": u, "Name": r.get("staff_name", ""), "Role": r.get("role", ""),
                  "Access": ov.get(u, "auto"), "PIN": "✅" if r.get("pin") else "–"}
                 for u, r in sorted(users.items(), key=lambda x: ({"staff": 0, "sales": 1}.get(x[1].get("role"), 2), x[0]))
                 if r.get("role") != "admin" and r.get("active", True)]
        uacc = st.data_editor(pd.DataFrame(urows), hide_index=True, width="stretch", num_rows="fixed",
                              disabled=["User", "Name", "Role", "PIN"], key=f"set_users_{n}",
                              column_config={"Access": st.column_config.SelectboxColumn(
                                  "Access", options=["auto", "edit", "view", "hidden"], required=True,
                                  help="auto = by role (above)")}) if urows else None
        st.caption("The access above is saved with **💾 Save settings**. The boxes below save by themselves.")
        st.divider()
        users_box(cfg)

    def do_save():
        rows = ed.to_dict("records")
        changes = dict(max_total=int(max_total), target_default=int(t_all), shelf_days=int(s_all), lookback_days=int(look),
                       round_to=int(rnd), max_prod_per_day=int(capp), priority=list(prio),
                       places=[p.strip() for p in places_txt.split(";") if p.strip()] or DEFAULT_SETTINGS["places"],
                       # every bun saved with its own value: exactly what the table shows is what the app uses
                       target_days={r["Bun"]: int(r["Target days"]) for r in rows},
                       shelf_by_bun={r["Bun"]: int(r["Shelf life (days)"]) for r in rows},
                       prod_days={r["Bun"]: [i for i in range(7) if r[EN_DAYS[i]]] for r in rows},
                       access_by_role=new_by_role, **room_vals, **task_vals)
        if uacc is not None:
            changes["access_override"] = {r["User"]: r["Access"] for r in uacc.to_dict("records")
                                          if r["Access"] in ("hidden", "view", "edit")}

        def ch(cur):
            cur.update(changes)
            cur.pop("access", None)                      # old per-person list (replaced by automatic by role)
        try:
            update_settings(ch)
            audit("settings saved", "targets: " + ", ".join(f"{short(r['Bun'])} {int(r['Target days'])}d" for r in rows)
                  + f" | limit {int(max_total):,} | shelf {int(s_all)}d | {len(task_vals['tasks'])} tasks")
            st.session_state.pop("set_draft", None)
            st.session_state["set_n"] = n + 1
            st.session_state["s_flash"] = ("✅ Settings saved · targets: " + ", ".join(
                f"{short(r['Bun'])} {int(r['Target days'])}d" for r in rows))
            st.rerun()
        except Exception as e:
            st.error(f"Not saved: {e}")

    with bar:
        c1, c2 = st.columns([3, 1])
        c1.markdown("Change anything in the tabs below, then press **💾 Save settings** — "
                    "one button saves 🎯 🧊 📋 and the access table.")
        if c2.button("💾 Save settings", type="primary", key="set_save_top", width="stretch"):
            do_save()
    if st.button("💾 Save settings", type="primary", key="set_save", width="stretch"):
        do_save()


# ==========================================
# 🧊 3D ROOMS — your room grid: stacks of crates, IN at the back, OUT at the front (FIFO)
# ==========================================
DOOR_SPOTS = ["front-middle", "front-left", "front-right", "back-middle", "back-left", "back-right",
              "right-back", "right-front", "left-back", "left-front"]
DEFAULT_ROOMS = [{"name": "❄️ Cooling room", "cols": 10, "rows": 8, "high": 15, "blocked": "1:5-8=Cooling fan; 1:9-10",
                  "door_in": "right-back", "door_out": "front-middle", "h": 3.0},
                 {"name": "🧊 Freezer room", "cols": 9, "rows": 9, "high": 15, "blocked": "",
                  "door_in": "front-middle", "door_out": "front-middle", "h": 3.0}]
DEFAULT_CRATE = {"w": 44.0, "l": 63.0, "h": 14.6}                  # cm
DEFAULT_CRATE_PCS = {"N1": 48, "N2": 62, "N21": 52, "N22": 62, "N23": 62, "N3": 63, "N31": 63, "N32": 63, "N33": 63,
                     "N34": 63, "N4": 60, "N41": 60, "N42": 60, "N43": 60}
DEFAULT_ROOM_ORDER = ["N1", "N2", "N21", "N23", "N22", "N3", "N31", "N32", "N43", "N42", "N41", "N4", "N34", "N33"]
GRID_GAP = 0.02
CRATE_COLORS = {"N1": "#e8590c", "N2": "#1c7ed6", "N21": "#a0522d", "N22": "#6c757d", "N23": "#f08c00", "N3": "#4263eb",
                "N31": "#fab005", "N32": "#9c6644", "N34": "#ced4da", "N4": "#f1f3f5", "N41": "#ffd43b",
                "N42": "#ff8787", "N43": "#40c057"}
EXTRA_COLORS = ["#ae3ec9", "#0ca678", "#d6336c", "#5c940d", "#1098ad", "#7048e8", "#e67700"]


def parse_blocked(txt, rows, cols):
    """'1:5-8=Cooling fan; 1:9-10' -> {(row0, col0): label}. Row / column numbers start at 1 (row 1 = back)."""
    out = {}
    for part in str(txt or "").split(";"):
        part = part.strip()
        if not part or ":" not in part:
            continue
        spot, _, label = part.partition("=")
        r_txt, _, c_txt = spot.partition(":")
        try:
            r1, _, r2 = r_txt.strip().partition("-")
            c1, _, c2 = c_txt.strip().partition("-")
            for r in range(int(r1), int(r2 or r1) + 1):
                for c in range(int(c1), int(c2 or c1) + 1):
                    if 1 <= r <= rows and 1 <= c <= cols:
                        out[(r - 1, c - 1)] = label.strip()
        except ValueError:
            continue
    return out


def rooms_of(cfg):
    out = []
    for r in cfg.get("rooms") or DEFAULT_ROOMS:
        try:
            if "cols" not in r:                                  # an older room format: use the defaults
                continue
            out.append({"name": str(r["name"]).strip(), "cols": max(1, int(r["cols"])), "rows": max(1, int(r["rows"])),
                        "high": max(1, int(r.get("high") or 15)), "blocked": str(r.get("blocked") or ""),
                        "door_in": r.get("door_in") if r.get("door_in") in DOOR_SPOTS else "back-middle",
                        "door_out": r.get("door_out") if r.get("door_out") in DOOR_SPOTS else "front-middle",
                        "h": float(r.get("h") or 3.0)})
        except Exception:
            continue
    return [r for r in out if r["name"]] or [dict(x) for x in DEFAULT_ROOMS]


def crate_size(cfg):
    c = {**DEFAULT_CRATE, **(cfg.get("crate") or {})}
    return {k: max(5.0, float(c[k])) / 100 for k in ("w", "l", "h")}       # metres


def room_of_bun(cfg, b, rooms):
    names = [r["name"] for r in rooms]
    r = (cfg.get("bun_room") or {}).get(b)
    if r in names:
        return r
    return names[0]                                             # not set: the first room (full -> next room)


def crate_pcs(cfg, b):
    try:
        return max(1, int((cfg.get("crate_pcs") or {}).get(b) or DEFAULT_CRATE_PCS.get(b) or 60))
    except Exception:
        return 60


def room_order(cfg, b):
    o = (cfg.get("room_order") or {}).get(b)
    try:
        return float(o)
    except (TypeError, ValueError):
        return float(DEFAULT_ROOM_ORDER.index(b) + 1) if b in DEFAULT_ROOM_ORDER else 99.0


def room_geom(room, cr):
    blocked = parse_blocked(room["blocked"], room["rows"], room["cols"])
    high = max(1, min(room["high"], int((room["h"] - 0.15) // cr["h"])))
    places = room["rows"] * room["cols"] - len(blocked)
    return {"cols": room["cols"], "rows": room["rows"], "high": high, "places": places, "capacity": places * high,
            "blocked": blocked, "w": round(room["cols"] * (cr["w"] + GRID_GAP), 2),
            "l": round(room["rows"] * (cr["l"] + GRID_GAP), 2), "h": room["h"]}


def bun_crates(cfg, b, batches):
    """One entry (lot date, pcs) per crate, oldest first."""
    cp, out = crate_pcs(cfg, b), []
    for d in sorted(batches.get(b, {})):
        left = int(round(batches[b][d]))
        while left > 0:
            n = min(cp, left)
            out.append((d, n))
            left -= n
    return out


def split_for_room(cfg, g, lists, speed):
    """The room is too small: every bun keeps its OLDEST crates here, the same number of days of sales each
    (whole stacks); its NEWEST lots go on to the next room (freezer). Returns (keep, move)."""
    high, places = g["high"], g["places"]
    if sum(-(-len(v) // high) for v in lists.values()) <= places:
        return lists, {}

    def stacks_for(days):
        out = {}
        for b, v in lists.items():
            per_day = float(speed.get(b, 0)) / crate_pcs(cfg, b)
            out[b] = min(-(-len(v) // high), int(math.ceil(per_day * days / high)) if per_day > 0 else 0)
        return out
    lo, hi = 0.0, 60.0
    for _ in range(40):                                          # most days of sales that still fit
        mid = (lo + hi) / 2
        if sum(stacks_for(mid).values()) <= places:
            lo = mid
        else:
            hi = mid
    keep_st = stacks_for(lo)
    free = places - sum(keep_st.values())
    while free > 0:                                              # fill the last places: lowest days first
        cand = [b for b in lists if keep_st[b] < -(-len(lists[b]) // high)]
        if not cand:
            break
        b = min(cand, key=lambda x: keep_st[x] * high * crate_pcs(cfg, x) / max(float(speed.get(x, 0)), 0.1))
        keep_st[b] += 1
        free -= 1
    keep, move = {}, {}
    for b, v in lists.items():
        n = min(len(v), keep_st[b] * high)
        keep[b], move[b] = v[:n], v[n:]
    return keep, {b: v for b, v in move.items() if v}


def room_fill(cfg, g, lists):
    """Like your sheet: buns (in your order) fill the places column by column, from the IN side (back, row 1)
    to the OUT side (front). Inside each bun the oldest lot goes to the places nearest the OUT door."""
    spots = [(c, r) for c in range(g["cols"]) for r in range(g["rows"]) if (r, c) not in g["blocked"]]
    stacks, overflow, k = [], {}, 0
    for b in sorted(lists, key=lambda x: (room_order(cfg, x), x)):
        crates = lists[b]
        if not crates:
            continue
        need = -(-len(crates) // g["high"])
        mine_spots = spots[k:k + need]
        k += len(mine_spots)
        if len(mine_spots) < need:
            overflow[b] = len(crates) - len(mine_spots) * g["high"]
        mine_spots = sorted(mine_spots, key=lambda s: (-s[1], s[0]))   # front row first = oldest
        for i, (c, r) in enumerate(mine_spots):
            part = crates[i * g["high"]:(i + 1) * g["high"]]
            segs = []
            for d, n in reversed(part):                          # bottom = newer, top = older (taken first)
                if segs and segs[-1][0] == d:
                    segs[-1][1] += 1
                    segs[-1][2] += n
                else:
                    segs.append([d, 1, n])
            stacks.append({"c": c, "r": r, "b": b, "segs": segs, "first": i == 0})
    return stacks, overflow


def fill_rooms(cfg, rooms, geoms, buns, batches, speed):
    """Every room in turn; what does not fit in a room goes on to the next one (cooling full -> freezer)."""
    carry, res = {}, {}
    for i, r in enumerate(rooms):
        g = geoms[r["name"]]
        lists = {b: bun_crates(cfg, b, batches) for b in buns if room_of_bun(cfg, b, rooms) == r["name"]}
        for b, v in carry.items():                               # newest lots moved here from the room before
            lists[b] = sorted(lists.get(b, []) + v)
        lists = {b: v for b, v in lists.items() if v}
        last = i == len(rooms) - 1
        keep, move = (lists, {}) if last else split_for_room(cfg, g, lists, speed)
        stacks, overflow = room_fill(cfg, g, keep)
        for st_ in stacks:                                       # moved-in (newer) lots: take from the room before first
            if st_["b"] in carry:
                st_["first"] = False
        res[r["name"]] = {"stacks": stacks, "overflow": overflow, "moved_in": {b: len(v) for b, v in carry.items()},
                          "moved_out": {b: len(v) for b, v in move.items()}}
        carry = move
    return res


ROOM3D_HTML = r"""
<div id="w" style="font-family:system-ui,-apple-system,sans-serif;color:#dfe6ee;background:#0f1720;padding:8px;border-radius:12px">
 <div style="display:flex;gap:6px;flex-wrap:wrap;align-items:center;margin-bottom:6px">
  <span style="opacity:.8">Day</span><input id="day" type="range" min="0" max="0" value="0" style="flex:1;min-width:120px">
  <b id="dl" style="min-width:150px;font-family:ui-monospace,monospace"></b>
  <button id="play" class="b">▶ Play</button>
 </div>
 <div style="display:flex;gap:6px;flex-wrap:wrap;margin-bottom:6px">
  <select id="rm" class="b"></select>
  <button id="v3" class="b on">3D</button><button id="vt" class="b">Top</button>
  <button id="dm" class="b on">Dimensions</button>
  <button id="lb" class="b on">Label: lot date</button>
  <button id="cl" class="b on">Color: bun type</button>
  <select id="fb" class="b"><option value="">All buns</option></select>
 </div>
 <canvas id="c" style="width:100%;height:__H__px;touch-action:none;border-radius:10px;background:#141c26;display:block"></canvas>
 <div id="info" style="min-height:38px;margin-top:6px;padding:8px 10px;border-radius:8px;background:#1d2733;font-size:14px">
  👆 Tap a stack: bun, lot date, age, crates, pcs. Drag to turn · pinch / wheel to zoom.</div>
 <div id="lg" style="font-size:12px;margin-top:5px;opacity:.85;line-height:1.6"></div>
</div>
<style>.b{border:1px solid #33475b;background:#1d2733;color:#dfe6ee;border-radius:8px;padding:6px 10px;font-size:13px;cursor:pointer}
.b.on{background:#3bb3d6;color:#06202b;border-color:#3bb3d6}</style>
<script>
const D=__DATA__;
const cv=document.getElementById('c'),ctx=cv.getContext('2d'),info=document.getElementById('info');
const DPR=window.devicePixelRatio||1;const CW=D.crate.w,CL=D.crate.l,CH=D.crate.h,GAP=D.gap,PX=CW+GAP,PZ=CL+GAP;
let day=D.days.length-1,dims=true,lotLbl=true,colBun=true,only='',sel=null,roomSel=D.rooms.length>1?'__all__':D.rooms[0].name;
const BUN={};D.buns.forEach(b=>BUN[b.code]=b);
let off={},X=0;D.rooms.forEach(r=>{off[r.name]=X;X+=r.w+1.6;});      // rooms side by side
const rm=document.getElementById('rm');[['__all__','🏭 Both rooms']].concat(D.rooms.map(r=>[r.name,r.name])).forEach(([v,t])=>{
 const o=document.createElement('option');o.value=v;o.textContent=t;rm.appendChild(o);});rm.value=roomSel;
const fb=document.getElementById('fb');D.buns.forEach(b=>{const o=document.createElement('option');o.value=b.code;o.textContent=b.label;fb.appendChild(o);});
const sl=document.getElementById('day');sl.max=D.days.length-1;sl.value=day;
function shown(){return D.rooms.filter(r=>roomSel==='__all__'||r.name===roomSel);}
function bounds(){const rs=shown();let x0=1e9,x1=-1e9,l=0,h=0;rs.forEach(r=>{x0=Math.min(x0,off[r.name]);x1=Math.max(x1,off[r.name]+r.w);l=Math.max(l,r.l);h=Math.max(h,r.h);});
 return {x:(x0+x1)/2,y:h/5,z:l/2,R:Math.max(x1-x0,l)*1.05+1.2};}
let B=bounds(),yaw=-0.45,pitch=-0.7,dist=B.R,fm=1;
function shade(hex,f,a){const n=parseInt(hex.slice(1),16);let r=(n>>16)&255,g=(n>>8)&255,b=n&255;
 return `rgba(${Math.min(255,r*f|0)},${Math.min(255,g*f|0)},${Math.min(255,b*f|0)},${a})`;}
function size(){const r=cv.getBoundingClientRect();cv.width=r.width*DPR;cv.height=r.height*DPR;}
function cam(){const cy=Math.cos(yaw),sy=Math.sin(yaw),cp=Math.cos(pitch),sp=Math.sin(pitch);
 return {cy,sy,cp,sp,pos:{x:B.x-dist*cp*sy,y:B.y-dist*sp,z:B.z-dist*cp*cy}};}
function P(k,v){const px=v[0]-B.x,py=v[1]-B.y,pz=v[2]-B.z;const x1=px*k.cy-pz*k.sy,z1=px*k.sy+pz*k.cy;
 const y2=py*k.cp-z1*k.sp,z2=py*k.sp+z1*k.cp;const dep=Math.max(0.3,dist+z2),f=Math.min(cv.width,cv.height)*1.25*fm;
 return [cv.width/2+f*x1/dep,cv.height/2-f*y2/dep,dep];}
const FACES=[[[0,0,0],[0,0,1],[0,1,1],[0,1,0],[-1,0,0],.72],[[1,0,0],[1,1,0],[1,1,1],[1,0,1],[1,0,0],.72],
 [[0,1,0],[0,1,1],[1,1,1],[1,1,0],[0,1,0],1],[[0,0,0],[0,1,0],[1,1,0],[1,0,0],[0,0,-1],.86],[[0,0,1],[1,0,1],[1,1,1],[0,1,1],[0,0,1],.86]];
function addBox(L,k,x,y,z,w,h,d,fill,a,ref,lines){for(const f of FACES){const n=f[4];
 const cx=x+w*(n[0]>0?1:n[0]<0?0:.5),cy=y+h*(n[1]>0?1:n[1]<0?0:.5),cz=z+d*(n[2]>0?1:n[2]<0?0:.5);
 if(n[0]*(k.pos.x-cx)+n[1]*(k.pos.y-cy)+n[2]*(k.pos.z-cz)<=0)continue;
 const pts=f.slice(0,4).map(q=>P(k,[x+q[0]*w,y+q[1]*h,z+q[2]*d]));
 let ln=null;if(lines>1&&n[1]===0){ln=[];for(let i=1;i<lines;i++){const yy=y+h*i/lines;
  ln.push(f.slice(0,4).filter(q=>q[1]===0).map(q=>P(k,[x+q[0]*w,yy,z+q[2]*d])));}}
 L.push({pts,dep:Math.max(...pts.map(p=>p[2]))*0.6+pts.reduce((s,p)=>s+p[2],0)/4*0.4,col:shade(fill,f[5],a),ref,ln});}}
// grid place -> metres. Row 0 = back (IN side, far), last row = front (OUT side, near the viewer)
function XZ(r,c,row){return [off[r.name]+c*PX+GAP/2,(r.rows-1-row)*PZ+GAP/2];}
function age(lot){return Math.round((Date.parse(D.days[day].iso)-Date.parse(lot))/864e5);}
function ageCol(b,a){const s=D.shelf[b]||7;return a<=2?'#2f9e44':a<=s*0.6?'#fcc419':a<=s?'#fd7e14':'#e03131';}
function line(k,a,b,col,w){const p=P(k,a),q=P(k,b);ctx.beginPath();ctx.moveTo(p[0],p[1]);ctx.lineTo(q[0],q[1]);ctx.strokeStyle=col;ctx.lineWidth=(w||1)*DPR;ctx.stroke();}
function doorPts(r,spot){const o=off[r.name],W=r.w,Lr=r.l,d=1.0;const [side,pos]=spot.split('-');
 if(side==='front'||side==='back'){const z=side==='front'?0:Lr;const xc=pos==='left'?o+d/2+0.1:pos==='right'?o+W-d/2-0.1:o+W/2;return [[xc-d/2,z],[xc+d/2,z]];}
 const x=side==='left'?o:o+W;const zc=pos==='back'?Lr-d/2-0.1:d/2+0.1;return [[x,zc-d/2],[x,zc+d/2]];}
let drawn=[];
function draw(){const k=cam();ctx.setTransform(1,0,0,1,0,0);ctx.clearRect(0,0,cv.width,cv.height);
 const dd=D.days[day];document.getElementById('dl').textContent=dd.label;const L=[],labels=[];
 shown().forEach(r=>{const o=off[r.name];const quad=(x0,z0,x1,z1,col)=>{const ps=[[x0,z0],[x1,z0],[x1,z1],[x0,z1]].map(v=>P(k,[v[0],0,v[1]]));
   ctx.beginPath();ps.forEach((p,i)=>i?ctx.lineTo(p[0],p[1]):ctx.moveTo(p[0],p[1]));ctx.closePath();ctx.fillStyle=col;ctx.fill();};
  quad(o,0,o+r.w,r.l,'#26313d');
  for(let c=0;c<=r.cols;c++)line(k,[o+c*PX,0.001,0],[o+c*PX,0.001,r.l],'rgba(255,255,255,.07)',1);
  for(let q=0;q<=r.rows;q++)line(k,[o,0.001,q*PZ],[o+r.w,0.001,q*PZ],'rgba(255,255,255,.07)',1);
  const c4=[[o,0],[o+r.w,0],[o+r.w,r.l],[o,r.l]];for(let i=0;i<4;i++){const a=c4[i],b=c4[(i+1)%4];
   line(k,[a[0],0,a[1]],[b[0],0,b[1]],'#4dabf7',1.2);line(k,[a[0],r.h,a[1]],[b[0],r.h,b[1]],'rgba(77,171,247,.45)',1);line(k,[a[0],0,a[1]],[a[0],r.h,a[1]],'rgba(77,171,247,.45)',1);}
  (r.din===r.dout?[[r.din,'#ff922b','🚪 Door IN / OUT']]:[[r.din,'#69db7c','🟢 Door IN (new stock)'],[r.dout,'#ff922b','🟠 Door OUT (take first)']]).forEach(([spot,col,t],j)=>{
   const [a,b]=doorPts(r,spot);line(k,[a[0],0,a[1]],[b[0],0,b[1]],col,5);line(k,[a[0],2,a[1]],[b[0],2,b[1]],col,2);
   line(k,[a[0],0,a[1]],[a[0],2,a[1]],col,2);line(k,[b[0],0,b[1]],[b[0],2,b[1]],col,2);
   const mx=(a[0]+b[0])/2,mz=(a[1]+b[1])/2;labels.push({v:[mx,2.3,mz],t,c:col,fs:11,pr:3});});
  const rd=dd.rooms[r.name]||{stacks:[],used:0};
  labels.push({v:[o+r.w/2,r.h+0.4,r.l/2],t:r.name+' · '+rd.used.toLocaleString()+' / '+r.cap.toLocaleString()+' crates · '+rd.pcs.toLocaleString()+' pcs',c:'#e9ecef',fs:12,pr:4});
  if(dims){line(k,[o,0,-0.45],[o+r.w,0,-0.45],'#adb5bd',1);labels.push({v:[o+r.w/2,0,-0.75],t:r.cols+' stacks · '+r.w+' m',c:'#ced4da',fs:10,pr:2});
   line(k,[o-0.4,0,0],[o-0.4,0,r.l],'#adb5bd',1);labels.push({v:[o-0.8,0,r.l/2],t:r.rows+' deep · '+r.l+' m',c:'#ced4da',fs:10,pr:2});}
  r.blocked.forEach(([row,c,t])=>{const [x,z]=XZ(r,c,row);addBox(L,k,x,0,z,CW,1.4,CL,t?'#364fc7':'#e8590c',0.55,null,0);
   if(t&&t.trim())labels.push({v:[x+CW/2,1.6,z+CL/2],t,c:'#bac8ff',fs:10,pr:1});});
  rd.stacks.forEach(s=>{const [c,row,bun,segs,first]=s;const bn=BUN[bun];const dim=only&&bun!==only;const [x,z]=XZ(r,c,row);let lev=0;
   segs.forEach(([lot,n,pcs])=>{const a=age(D.lots[lot]);addBox(L,k,x,lev*CH,z,CW,n*CH-0.004,CL,colBun?bn.color:ageCol(bun,a),dim?0.12:1,
     {room:r.name,s,row,c,lot,n,pcs,a,bun,rows:r.rows},n);lev+=n;});
   if(!dim){const top=segs[segs.length-1];const lot=D.lots[top[0]];
    labels.push({v:[x+CW/2,lev*CH+0.12,z+CL/2],t:(first?'⭐ ':'')+(lotLbl?lot.slice(8,10)+'/'+lot.slice(5,7)+' ':'')+bun,c:'#fff',fs:9,bg:shade(bn.color,0.5,0.92),pr:first?2:0});}});
 });
 L.sort((a,b)=>b.dep-a.dep);drawn=L;
 for(const p of L){ctx.beginPath();p.pts.forEach((q,i)=>i?ctx.lineTo(q[0],q[1]):ctx.moveTo(q[0],q[1]));ctx.closePath();ctx.fillStyle=p.col;ctx.fill();
  const hi=sel&&p.ref&&sel.s===p.ref.s;ctx.lineWidth=(hi?2.5:0.6)*DPR;ctx.strokeStyle=hi?'#fff':'rgba(0,0,0,.45)';ctx.stroke();
  if(p.ln&&p.ln.length<20){ctx.lineWidth=0.5*DPR;ctx.strokeStyle='rgba(0,0,0,.3)';p.ln.forEach(e=>{if(e.length===2){ctx.beginPath();ctx.moveTo(e[0][0],e[0][1]);ctx.lineTo(e[1][0],e[1][1]);ctx.stroke();}});}}
 const used=[];labels.map(l=>({...l,p:P(k,l.v)})).sort((a,b)=>(b.pr-a.pr)||(a.p[2]-b.p[2])).forEach(l=>{const fs=l.fs*DPR;ctx.font=`600 ${fs}px system-ui,sans-serif`;
  const w=ctx.measureText(l.t).width+8*DPR,rc=[l.p[0]-w/2,l.p[1]-fs*0.7,w,fs*1.4];
  if(used.some(u=>rc[0]<u[0]+u[2]&&u[0]<rc[0]+rc[2]&&rc[1]<u[1]+u[3]&&u[1]<rc[1]+rc[3]))return;used.push(rc);
  if(l.bg){ctx.fillStyle=l.bg;ctx.fillRect(rc[0],rc[1],rc[2],rc[3]);}ctx.fillStyle=l.c;ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillText(l.t,l.p[0],l.p[1]);});
}
let raf=0;function redraw(){if(!raf)raf=requestAnimationFrame(()=>{raf=0;draw();});}
function inside(pt,poly){let c=false;for(let i=0,j=poly.length-1;i<poly.length;j=i++){const a=poly[i],b=poly[j];
 if(((a[1]>pt[1])!==(b[1]>pt[1]))&&(pt[0]<(b[0]-a[0])*(pt[1]-a[1])/(b[1]-a[1])+a[0]))c=!c;}return c;}
function pick(e){const r=cv.getBoundingClientRect(),pt=[(e.clientX-r.left)*DPR,(e.clientY-r.top)*DPR];
 for(let i=drawn.length-1;i>=0;i--){const p=drawn[i];if(p.ref&&inside(pt,p.pts))return p.ref;}return null;}
function describe(r){if(!r)return '👆 Tap a stack: bun, lot date, age, crates, pcs.';const b=BUN[r.bun],lot=D.lots[r.lot];
 const tot=r.s[3].reduce((a,x)=>a+x[2],0),cr=r.s[3].reduce((a,x)=>a+x[1],0);
 return `📦 ${r.room} · column ${r.c+1} · row ${r.row+1} (${r.rows-r.row}${r.rows-r.row===1?'st':'th'} from the OUT door) · <b>${b.label}</b> · lot <b>${lot.slice(8,10)}/${lot.slice(5,7)}</b>`+
  ` · ${r.a} d old · this lot ${r.n} crates ≈ ${r.pcs.toLocaleString()} pcs · whole stack ${cr} crates = ${tot.toLocaleString()} pcs`+(r.s[4]?' · ⭐ TAKE FIRST':'');}
let drag=null,pinch=null,moved=0;
cv.addEventListener('pointerdown',e=>{cv.setPointerCapture(e.pointerId);drag={x:e.clientX,y:e.clientY};moved=0;});
cv.addEventListener('pointermove',e=>{if(!drag||pinch)return;const dx=e.clientX-drag.x,dy=e.clientY-drag.y;moved+=Math.abs(dx)+Math.abs(dy);
 if(moved<6)return;
 if(fm>1){fm=1;dist=B.R;document.getElementById('vt').classList.remove('on');document.getElementById('v3').classList.add('on');}
 yaw+=dx*0.007;pitch=Math.max(-1.56,Math.min(-0.05,pitch+dy*0.005));drag={x:e.clientX,y:e.clientY};redraw();});
cv.addEventListener('pointerup',e=>{if(drag&&moved<6){sel=pick(e);info.innerHTML=describe(sel);redraw();}drag=null;});
const lim=v=>Math.max(B.R*0.12*fm,Math.min(B.R*3*fm,v));
cv.addEventListener('wheel',e=>{e.preventDefault();dist=lim(dist*(e.deltaY>0?1.1:0.9));redraw();},{passive:false});
cv.addEventListener('touchstart',e=>{if(e.touches.length===2){const a=e.touches[0],b=e.touches[1];pinch={d:Math.hypot(a.clientX-b.clientX,a.clientY-b.clientY),dist};}},{passive:true});
cv.addEventListener('touchmove',e=>{if(pinch&&e.touches.length===2){const a=e.touches[0],b=e.touches[1];
 dist=lim(pinch.dist*pinch.d/Math.hypot(a.clientX-b.clientX,a.clientY-b.clientY));redraw();}},{passive:true});
cv.addEventListener('touchend',e=>{if(e.touches.length<2)setTimeout(()=>pinch=null,50);},{passive:true});
const tg=(id,fn)=>{const el=document.getElementById(id);el.onclick=()=>{fn(el);redraw();};};
function set3d(){yaw=-0.45;pitch=-0.7;dist=B.R;fm=1;document.getElementById('v3').classList.add('on');document.getElementById('vt').classList.remove('on');}
function setTop(){yaw=0;pitch=-1.5707;dist=B.R*8;fm=8.6;document.getElementById('vt').classList.add('on');document.getElementById('v3').classList.remove('on');}
tg('v3',set3d);tg('vt',setTop);
tg('dm',el=>{dims=!dims;el.classList.toggle('on',dims);});
tg('lb',el=>{lotLbl=!lotLbl;el.classList.toggle('on',lotLbl);el.textContent=lotLbl?'Label: lot date':'Label: bun';});
tg('cl',el=>{colBun=!colBun;el.classList.toggle('on',colBun);el.textContent=colBun?'Color: bun type':'Color: age';legend();});
rm.onchange=()=>{roomSel=rm.value;B=bounds();fm>1?setTop():set3d();sel=null;redraw();};
fb.onchange=()=>{only=fb.value;sel=null;redraw();};
sl.oninput=()=>{day=+sl.value;sel=null;info.innerHTML=describe(null);redraw();};
let timer=null;document.getElementById('play').onclick=e=>{if(timer){clearInterval(timer);timer=null;e.target.textContent='▶ Play';return;}
 e.target.textContent='⏸ Pause';if(day>=D.days.length-1)day=0;sl.value=day;redraw();
 timer=setInterval(()=>{if(day>=D.days.length-1){clearInterval(timer);timer=null;e.target.textContent='▶ Play';return;}day++;sl.value=day;redraw();},1100);};
function legend(){document.getElementById('lg').innerHTML=(colBun?D.buns.map(b=>`<span style="white-space:nowrap"><b style="color:${b.color}">■</b> ${b.label}</span>`).join(' &nbsp;'):
 '<b style="color:#2f9e44">■</b> 0–2 days · <b style="color:#fcc419">■</b> fresh · <b style="color:#fd7e14">■</b> near shelf life · <b style="color:#e03131">■</b> past shelf life')+
 '<br>🟢 Door IN = new stock goes in at the back · 🟠 Door OUT = take from the front row first · ⭐ = oldest stack of each bun (take first)';}
window.addEventListener('resize',()=>{size();redraw();});legend();size();__START__draw();
</script>"""


def room_sheet_html(room, g, stacks, names):
    """Your Excel 'ស្តុកនំប្រចាំថ្ងៃ' layout: one cell per stack (lot date + bun / pcs), column totals, total."""
    cells = {(s["r"], s["c"]): s for s in stacks}
    bd = "border:1px solid #444;"
    h = [f"<div style='overflow-x:auto'><table style='border-collapse:collapse;font-size:13px;text-align:center;min-width:{g['cols'] * 78}px'>",
         f"<tr><td colspan='{g['cols']}' style='{bd}font-size:18px;font-weight:700;padding:6px'>ស្តុកនំប្រចាំថ្ងៃ · {room['name']}</td>"
         f"<td style='padding:4px 8px;font-size:12px'>{'Door in ⤵' if room['door_in'].startswith('right') else ''}</td></tr>"]
    col_tot = [0] * g["cols"]
    for r in range(g["rows"]):
        h.append("<tr>")
        c = 0
        while c < g["cols"]:
            if (r, c) in g["blocked"]:
                lab, span = g["blocked"][(r, c)], 1
                while c + span < g["cols"] and g["blocked"].get((r, c + span)) == lab and (r, c + span) in g["blocked"]:
                    span += 1
                bg = "#ED7D31" if not lab else "#fff"
                h.append(f"<td colspan='{span}' style='{bd}background:{bg};padding:6px'>{lab}</td>")
                c += span
                continue
            s = cells.get((r, c))
            if s:
                top = s["segs"][-1][0]
                pcs = sum(x[2] for x in s["segs"])
                col_tot[c] += pcs
                star = "⭐ " if s["first"] else ""
                h.append(f"<td style='{bd}background:{COLORS.get(s['b'], '#fff')};padding:4px 6px;min-width:70px'>"
                         f"{star}{top:%d/%m} {s['b']}<br><b>{pcs:,}</b></td>")
            else:
                h.append(f"<td style='{bd}padding:4px 6px;min-width:70px;color:#999'>–</td>")
            c += 1
        h.append("<td></td></tr>")
    tot = sum(col_tot)
    h.append("<tr>" + "".join(f"<td style='{bd}background:#FFF2CC;font-weight:700;text-align:right;padding:4px 6px'>{v:,}</td>"
                              for v in col_tot)
             + f"<td style='{bd}background:#FFF2CC;font-weight:700;padding:4px 8px'>{tot:,} នំសរុប</td></tr>")
    out_txt = "door out" if room["door_out"].startswith("front") else ""
    h.append(f"<tr><td colspan='{g['cols']}' style='padding:4px'>{out_txt}</td><td></td></tr></table></div>")
    return "".join(h), tot


def room_sheet_excel(room, g, stacks):
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
    wb = Workbook()
    ws = wb.active
    ws.title = "Room stock"
    thin = Side(style="thin", color="444444")
    box = Border(left=thin, right=thin, top=thin, bottom=thin)
    mid = Alignment(horizontal="center", vertical="center", wrap_text=True)
    ws.cell(1, 1, f"ស្តុកនំប្រចាំថ្ងៃ · {room['name']}").font = Font(bold=True, size=14)
    ws.merge_cells(start_row=1, start_column=1, end_row=1, end_column=g["cols"])
    ws.cell(1, 1).alignment = mid
    cells = {(s["r"], s["c"]): s for s in stacks}
    col_tot = [0] * g["cols"]
    for r in range(g["rows"]):
        for c in range(g["cols"]):
            top_cell, low_cell = ws.cell(2 + r * 2, 1 + c), ws.cell(3 + r * 2, 1 + c)
            for x in (top_cell, low_cell):
                x.border, x.alignment = box, mid
            if (r, c) in g["blocked"]:
                top_cell.value = g["blocked"][(r, c)] or None
                if not g["blocked"][(r, c)]:
                    top_cell.fill = PatternFill("solid", fgColor="ED7D31")
                continue
            s = cells.get((r, c))
            if s:
                pcs = sum(x[2] for x in s["segs"])
                col_tot[c] += pcs
                top_cell.value = f"{s['segs'][-1][0]:%d/%m} {s['b']}"
                low_cell.value = pcs
                fill = PatternFill("solid", fgColor=COLORS.get(s["b"], "#FFFFFF").lstrip("#"))
                top_cell.fill = low_cell.fill = fill
    tr = 2 + g["rows"] * 2
    for c, v in enumerate(col_tot):
        x = ws.cell(tr, 1 + c, v)
        x.number_format, x.font, x.border = "#,##0", Font(bold=True), box
        x.fill = PatternFill("solid", fgColor="FFF2CC")
    x = ws.cell(tr, 1 + g["cols"], sum(col_tot))
    x.number_format, x.font, x.fill = "#,##0", Font(bold=True), PatternFill("solid", fgColor="FFF2CC")
    ws.cell(tr, 2 + g["cols"], "នំសរុប")
    ws.cell(tr + 1, 1 + g["cols"] // 2, "door out")
    ws.cell(2, 1 + g["cols"], "Door in")
    from openpyxl.utils import get_column_letter
    for c in range(g["cols"] + 2):
        ws.column_dimensions[get_column_letter(c + 1)].width = 12
    bio = io.BytesIO()
    wb.save(bio)
    return bio.getvalue()


def page_rooms(cfg):
    st.subheader("🧊 3D FIFO rooms — cooling + freezer")
    prod, counts, adjs, sales, names, buns = get_data(cfg)
    t = today_kh()
    rooms, cr = rooms_of(cfg), crate_size(cfg)
    geoms = {r["name"]: room_geom(r, cr) for r in rooms}
    speed, _sn = sales_speed(sales, buns, t, int(cfg["lookback_days"]))
    is_admin = st.session_state.get("p_role") == "admin"
    if is_admin:                                         # sizes: Admin only (staff just look)
        with st.expander("📐 Adjust sizes — room grid, doors, crate, room / order / pcs per crate of each bun (Admin only)"):
            rn = st.session_state.get("room_n", 0)
            new_vals = rooms_settings(cfg, buns, names, rn, kp="rm")
            if st.button("💾 Save sizes", type="primary", key="rm_save"):
                try:
                    update_settings(new_vals)
                    audit("room sizes saved", " · ".join(
                        f"{r['name']} {r['cols']}×{r['rows']} stacks, {r['high']} high, blocked [{r['blocked']}], "
                        f"in {r['door_in']}, out {r['door_out']}" for r in new_vals["rooms"])
                        + " | crate " + "×".join(f"{v:g}" for v in new_vals["crate"].values()) + " cm")
                    st.session_state["room_n"] = rn + 1
                    st.session_state["room_flash"] = "✅ Sizes saved — the 3D view uses them now."
                    st.rerun()
                except Exception as e:
                    st.error(f"Not saved: {e}")
    show_flash("room_flash")
    c1, c2 = st.columns([1, 3])
    back = c1.selectbox("Days to replay", [7, 14, 3, 1], key="room_back", format_func=lambda n: f"last {n} days")
    days = [t - timedelta(days=i) for i in range(int(back) - 1, -1, -1)]
    lots, lot_i, out_days, today_stacks = [], {}, [], {}
    overflow_today, moved_today = {}, {}
    for d in days:
        batches, _s, _h, _nc = compute_stock(buns, prod, counts, adjs, sales, d)
        rd = {}
        filled = fill_rooms(cfg, rooms, geoms, buns, batches, speed)
        for r in rooms:
            stacks, overflow = filled[r["name"]]["stacks"], filled[r["name"]]["overflow"]
            for s in stacks:
                for seg in s["segs"]:
                    if seg[0] not in lot_i:
                        lot_i[seg[0]] = len(lots)
                        lots.append(seg[0].isoformat())
            rd[r["name"]] = {"stacks": [[s["c"], s["r"], s["b"], [[lot_i[x[0]], x[1], x[2]] for x in s["segs"]], s["first"]]
                                        for s in stacks],
                             "used": sum(x[1] for s in stacks for x in s["segs"]),
                             "pcs": int(sum(x[2] for s in stacks for x in s["segs"]))}
            if d == t:
                today_stacks[r["name"]] = stacks
                overflow_today[r["name"]] = overflow
                moved_today[r["name"]] = filled[r["name"]]["moved_out"]
        out_days.append({"iso": d.isoformat(), "label": ("Today · " if d == t else "") + f"{d:%a %d %b}", "rooms": rd})
    today = out_days[-1]["rooms"]
    tiles([(r["name"], f"{today[r['name']]['used']:,} / {geoms[r['name']]['capacity']:,}",
            f"crates · {geoms[r['name']]['places']} stacks × {geoms[r['name']]['high']} high · "
            f"{today[r['name']]['pcs']:,} pcs · {today[r['name']]['used'] / max(geoms[r['name']]['capacity'], 1) * 100:.0f}% full")
           for r in rooms])
    for i, r in enumerate(rooms[:-1]):
        mv = moved_today.get(r["name"]) or {}
        if mv:
            st.info(f"🔄 **{r['name']} is full** → the newest lots go to **{rooms[i + 1]['name']}**: "
                    + ", ".join(f"{short(b)} {n} crates" for b, n in mv.items())
                    + f" (total {sum(mv.values()):,} crates). {r['name']} keeps the oldest stock of every bun "
                      "(about the same days of sales each) to pick first.")
    parts = [f"**{r['name']}**: " + ", ".join(f"{short(b)} {n}" for b, n in overflow_today[r["name"]].items())
             for r in rooms if overflow_today.get(r["name"])]
    if parts:
        st.warning("⚠️ No place today for these crates — " + " · ".join(parts)
                   + ". Move a bun to the other room" + (", or adjust the room grid (📐)." if is_admin else "."))
    present = [b for b in buns if any(s["b"] == b for x in today_stacks.values() for s in x)]
    data = {"days": out_days, "lots": lots, "crate": cr, "gap": GRID_GAP,
            "rooms": [{"name": r["name"], "cols": geoms[r["name"]]["cols"], "rows": geoms[r["name"]]["rows"],
                       "w": geoms[r["name"]]["w"], "l": geoms[r["name"]]["l"], "h": geoms[r["name"]]["h"],
                       "cap": geoms[r["name"]]["capacity"], "din": r["door_in"], "dout": r["door_out"],
                       "blocked": [[k[0], k[1], v if v and (k[0], k[1] - 1) not in geoms[r["name"]]["blocked"]
                                    or v and geoms[r["name"]]["blocked"].get((k[0], k[1] - 1)) != v else ("" if not v else " ")]
                                   for k, v in sorted(geoms[r["name"]]["blocked"].items())]} for r in rooms],
            "buns": [{"code": b, "label": f"{b} {names.get(b, '')}".strip(), "color": CRATE_COLORS.get(b, EXTRA_COLORS[i % 7])}
                     for i, b in enumerate(present)],
            "shelf": {b: int(cfg.get("shelf_by_bun", {}).get(b, cfg.get("shelf_days", 10))) for b in buns}}
    h = 430 if st.session_state.get("phone_mode") else 600
    components.html(ROOM3D_HTML.replace("__DATA__", json.dumps(data, ensure_ascii=False)).replace("__H__", str(h))
                    .replace("__START__", ""), height=h + 190)

    st.markdown("#### 📋 Room sheet — your Excel layout (today)")
    pick = st.radio("Room sheet", [r["name"] for r in rooms], horizontal=True, key="room_sheet",
                    label_visibility="collapsed")
    room = next(r for r in rooms if r["name"] == pick)
    html, tot = room_sheet_html(room, geoms[pick], today_stacks.get(pick, []), names)
    st.markdown(html, unsafe_allow_html=True)
    st.download_button(f"⬇️ {pick} sheet (Excel)", room_sheet_excel(room, geoms[pick], today_stacks.get(pick, [])),
                       file_name=f"room_stock_{t}.xlsx",
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", key="room_xlsx")
    st.caption("FIFO: new crates go in from the 🟢 IN door at the back; take from the front row at the 🟠 OUT door first "
               "(⭐ = oldest stack of each bun). Buns fill the columns in the order set by Admin, like your sheet. "
               "The view follows the live stock — use the Day slider / ▶ Play to see how it moved.")


def rooms_settings(cfg, buns, names, n, kp="set"):
    """Room grid (stacks across × deep, blocked places, doors), crate size, and room / order / pcs per crate per bun."""
    if kp == "set":
        st.markdown("#### 🧊 Rooms and crates (for 🧊 3D rooms)")
    st.caption("A room = a grid of stack places like your sheet. Across = columns, Deep = rows (row 1 = back, at the IN "
               "side). Blocked = places with no stock, e.g. `1:5-8=Cooling fan; 1:9-10` (row:columns=name).")
    rdf = pd.DataFrame([{"Room": r["name"], "Stacks across": r["cols"], "Stacks deep": r["rows"], "Crates high": r["high"],
                         "Height (m)": r["h"], "Blocked places": r["blocked"], "Door IN": r["door_in"],
                         "Door OUT": r["door_out"]} for r in rooms_of(cfg)])
    red = st.data_editor(rdf, hide_index=True, width="stretch", num_rows="dynamic", key=f"{kp}_rooms3_{n}",
                         column_config={"Room": st.column_config.TextColumn("Room", required=True),
                                        **{c: st.column_config.NumberColumn(c, min_value=1, max_value=60, step=1, required=True)
                                           for c in ["Stacks across", "Stacks deep", "Crates high"]},
                                        "Height (m)": st.column_config.NumberColumn("Height (m)", min_value=1.0,
                                                                                    max_value=20.0, step=0.1, format="%.1f"),
                                        "Blocked places": st.column_config.TextColumn("Blocked places"),
                                        "Door IN": st.column_config.SelectboxColumn("🟢 Door IN", options=DOOR_SPOTS, required=True),
                                        "Door OUT": st.column_config.SelectboxColumn("🟠 Door OUT", options=DOOR_SPOTS, required=True)})
    rooms = []
    for r in red.to_dict("records"):
        if str(r.get("Room") or "").strip():
            try:
                rooms.append({"name": str(r["Room"]).strip(), "cols": int(r["Stacks across"]), "rows": int(r["Stacks deep"]),
                              "high": int(r["Crates high"]), "h": float(r.get("Height (m)") or 3.0),
                              "blocked": str(r.get("Blocked places") or ""), "door_in": r.get("Door IN") or "back-middle",
                              "door_out": r.get("Door OUT") or "front-middle"})
            except Exception:
                pass
    rooms = rooms or rooms_of(cfg)
    c = {**DEFAULT_CRATE, **(cfg.get("crate") or {})}
    a, b, d = st.columns(3)
    cw = a.number_input("Crate W (cm)", 10.0, 200.0, float(c["w"]), 0.5, key=f"{kp}_crw")
    cl = b.number_input("Crate L (cm)", 10.0, 200.0, float(c["l"]), 0.5, key=f"{kp}_crl")
    ch = d.number_input("Crate H (cm)", 3.0, 100.0, float(c["h"]), 0.1, key=f"{kp}_crh")
    cr = {"w": cw / 100, "l": cl / 100, "h": ch / 100}
    st.caption("Space: " + " · ".join(
        f"{r['name']} ≈ {g['w']} × {g['l']} m = {g['places']} stacks × {g['high']} high = {g['capacity']:,} crates"
        for r in rooms for g in [room_geom(r, cr)]))
    rn = [r["name"] for r in rooms]
    bdf = pd.DataFrame([{"Bun": x, "Name": names.get(x, ""), "Room": room_of_bun(cfg, x, rooms),
                         "Order": int(room_order(cfg, x)), "Pcs per crate": crate_pcs(cfg, x)} for x in buns])
    bed = st.data_editor(bdf, hide_index=True, width="stretch", num_rows="fixed", disabled=["Bun", "Name"],
                         key=f"{kp}_bunroom_{n}",
                         column_config={"Room": st.column_config.SelectboxColumn("Room", options=rn, required=True),
                                        "Order": st.column_config.NumberColumn("↔️ Order (1 = first column)", min_value=1,
                                                                               max_value=99, step=1, required=True),
                                        "Pcs per crate": st.column_config.NumberColumn("📦 Pcs per crate", min_value=1,
                                                                                       max_value=2000, step=1, required=True)})
    recs = bed.to_dict("records")
    return {"rooms": rooms, "crate": {"w": cw, "l": cl, "h": ch},
            "bun_room": {r["Bun"]: (r["Room"] if r["Room"] in rn else rn[0]) for r in recs},
            "room_order": {r["Bun"]: int(r["Order"] or 99) for r in recs},
            "crate_pcs": {r["Bun"]: int(r["Pcs per crate"] or 60) for r in recs}}


# ==========================================
# 📋 TASKS · 🕘 HISTORY · 👥 USERS
# ==========================================
USERNAME_RE = re.compile(r"^[a-z0-9._-]{3,30}$")
EASY_PINS = {"0000", "1111", "1234", "4321", "123456", "000000", "111111", "654321"}


def pw_problem(pw):
    if len(pw or "") < 8 or not re.search(r"[A-Za-z]", pw) or not re.search(r"[0-9]", pw):
        return "A password needs at least 8 characters, with letters and numbers."
    return ""


def pin_problem(a, b=None):
    if not PIN_RE.match(a or ""):
        return "A PIN is 4 to 6 numbers."
    if b is not None and a != b:
        return "The two PINs are different."
    if a in EASY_PINS or len(set(a)) == 1:
        return "Too easy to guess — choose another PIN."
    return ""


def staff_names(cfg, users=None):
    users = load_users() if users is None else users
    others = sorted({(r.get("staff_name") or u) for u, r in users.items() if r.get("active", True)}, key=str.lower)
    return list(dict.fromkeys(ops_names(cfg, users) + others))           # operation staff first


def task_list(cfg):
    out = []
    for t in cfg.get("tasks") or DEFAULT_TASKS:
        if isinstance(t, dict) and t.get("id") and t.get("name"):
            out.append({"id": str(t["id"]), "name": str(t["name"]), "due": str(t.get("due") or ""),
                        "who": list(t.get("who") or []), "auto": t.get("auto") or "",
                        "days": [int(x) for x in (t.get("days") if t.get("days") is not None else ALL_DAYS)]})
    return out


def _due_passed(day, due):
    try:
        hh, mm = [int(x) for x in due.split(":")]
    except Exception:
        return day < today_kh()
    n = now_kh()
    return day < today_kh() or (day == today_kh() and (n.hour, n.minute) >= (hh, mm))


def tasks_for_day(cfg, day, prod=None, counts=None, trows=None):
    """Each task of that day with its status: ✅ done · ⏳ to do · 🔴 late · ❌ missed."""
    if prod is None:
        prod, _ = read_csv(PROD_FILE, PROD_COLS)
    if counts is None:
        counts, _ = read_csv(COUNT_FILE, COUNT_COLS)
    if trows is None:
        trows, _ = read_csv(TASK_FILE, TASK_COLS)
    iso = day.isoformat()
    mine = trows[trows["Date"] == iso]
    out = []
    for t in task_list(cfg):
        if day.weekday() not in t["days"]:
            continue
        row = mine[mine["Task_Id"] == t["id"]]
        row = row.iloc[-1].to_dict() if len(row) else {}
        assigned = [x.strip() for x in str(row.get("Assigned") or "").split(";") if x.strip()] if row.get("Assigned") \
            else list(t["who"])
        done_by, done_at, how = str(row.get("Done_By") or ""), str(row.get("Done_At") or ""), "manual"
        if not done_by and t["auto"] in ("prod", "count"):
            df = prod if t["auto"] == "prod" else counts
            key = "Prod_Date" if t["auto"] == "prod" else "Count_Date"
            hit = df[(df[key].astype(str).str[:10] == iso) |
                     ((df["Saved_At"].astype(str).str[:10] == iso) if t["auto"] == "prod" else False)] \
                if len(df) else df
            if len(hit):
                hit = hit.sort_values("Saved_At")
                done_by = "; ".join(dict.fromkeys(hit["By"].astype(str)))
                done_at, how = str(hit["Saved_At"].iloc[0])[11:16], "auto"
        if done_by:
            status = "✅ Done"
        elif day < today_kh():
            status = "❌ Missed"
        elif _due_passed(day, t["due"]):
            status = "🔴 Late"
        else:
            status = "⏳ To do"
        out.append({**t, "assigned": assigned, "done_by": done_by, "done_at": done_at, "how": how,
                    "status": status, "note": str(row.get("Note") or "")})
    return out


def save_task_row(day, tid, **fields):
    iso, me = day.isoformat(), st.session_state.get("p_name", "")
    stamp = now_kh().strftime("%Y-%m-%d %H:%M:%S")

    def ch(df):
        m = (df["Date"] == iso) & (df["Task_Id"] == tid)
        if not m.any():
            df = pd.concat([df, pd.DataFrame([{"Date": iso, "Task_Id": tid}])], ignore_index=True)
            m = (df["Date"] == iso) & (df["Task_Id"] == tid)
        for k, v in {**fields, "Updated_At": stamp, "Updated_By": me}.items():
            df.loc[m, k] = v
        return df
    modify_csv(TASK_FILE, TASK_COLS, ch)


def my_tasks_banner(cfg, me):
    try:
        todo = [t for t in tasks_for_day(cfg, today_kh()) if me in t["assigned"] and not t["done_by"]]
    except Exception:
        return
    if todo:
        st.warning("📋 **Your tasks today:** " + " · ".join(
            f"{t['status'].split()[0]} {t['name']}" + (f" (before {t['due']})" if t["due"] else "") for t in todo))


GOTO = {"prod": "🏭 Log production", "count": "📦 Stock count"}


def page_tasks(cfg, can_edit, me):
    st.subheader("📋 Daily tasks")
    is_admin = st.session_state.get("p_role") == "admin"
    c1, c2 = st.columns([1, 2])
    day = c1.date_input("Day", value=today_kh(), max_value=today_kh() + timedelta(days=14), key="t_day")
    only_me = c2.toggle("Show only my tasks", value=not is_admin, key="t_mine")
    show_flash("t_flash")
    prod, _ = read_csv(PROD_FILE, PROD_COLS)
    counts, _ = read_csv(COUNT_FILE, COUNT_COLS)
    trows, _ = read_csv(TASK_FILE, TASK_COLS)
    rows = tasks_for_day(cfg, day, prod, counts, trows)
    if only_me:
        rows = [t for t in rows if me in t["assigned"] or not t["assigned"]]
    if not rows:
        st.info("No tasks for this day." + (" Admin adds tasks in ⚙️ Settings." if is_admin else ""))
    people = staff_names(cfg)
    done = sum(1 for t in rows if t["done_by"])
    if rows:
        st.progress(done / len(rows), text=f"{done} of {len(rows)} done")
    for t in rows:
        with st.container(border=True):
            a, b = st.columns([3, 2])
            a.markdown(f"**{t['status']} · {t['name']}**" + (f"  \n⏰ before {t['due']}" if t["due"] else ""))
            a.caption("👥 " + (", ".join(t["assigned"]) or "anyone")
                      + (f" · ✔️ by {t['done_by']} at {t['done_at']}" + (" (saved in the app)" if t["how"] == "auto" else "")
                         if t["done_by"] else "")
                      + (f" · 📝 {t['note']}" if t["note"] else ""))
            if t["auto"] in GOTO and not t["done_by"] and day == today_kh():
                if b.button(f"➡️ Go to {GOTO[t['auto']]}", key=f"t_go_{t['id']}", width="stretch"):
                    st.session_state["goto_page"] = GOTO[t["auto"]]
                    st.rerun()
            elif not t["done_by"] and can_edit and day <= today_kh():
                note = b.text_input("Note (optional)", key=f"t_note_{t['id']}_{day}", label_visibility="collapsed",
                                    placeholder="Note (optional)")
                if b.button("✅ Mark done", key=f"t_done_{t['id']}_{day}", type="primary", width="stretch"):
                    try:
                        save_task_row(day, t["id"], Done_By=me, Done_At=now_kh().strftime("%H:%M"), Note=note.strip())
                        audit("task done", f"{day:%d %b}: {t['name']}" + (f" · {note.strip()}" if note.strip() else ""))
                        st.session_state["t_flash"] = f"✅ {t['name']} — done"
                        st.rerun()
                    except Exception as e:
                        st.error(f"Not saved: {e}")
            elif t["done_by"] and t["how"] == "manual" and (is_admin or t["done_by"] == me):
                if b.button("↩️ Undo", key=f"t_undo_{t['id']}_{day}", width="stretch"):
                    save_task_row(day, t["id"], Done_By="", Done_At="", Note="")
                    audit("task undone", f"{day:%d %b}: {t['name']}")
                    st.rerun()
            if is_admin:
                with b.popover("👥 Assign", width="stretch"):
                    pick = st.multiselect("Who does it on this day", people,
                                          default=[p for p in t["assigned"] if p in people], key=f"t_as_{t['id']}_{day}")
                    if st.button("💾 Save", key=f"t_as_save_{t['id']}_{day}"):
                        save_task_row(day, t["id"], Assigned="; ".join(pick))
                        audit("task assigned", f"{day:%d %b}: {t['name']} → {', '.join(pick) or 'anyone'}")
                        st.session_state["t_flash"] = f"👥 {t['name']} → {', '.join(pick) or 'anyone'}"
                        st.rerun()
    st.markdown("#### 🗓️ Last 7 days")
    days = [today_kh() - timedelta(days=i) for i in range(6, -1, -1)]
    grid = {}
    for d in days:
        for t in tasks_for_day(cfg, d, prod, counts, trows):
            grid.setdefault(t["name"], {})[day_label(d)] = t["status"].split()[0] + (
                f" {t['done_by']}" if t["done_by"] else "")
    if grid:
        st.dataframe(pd.DataFrame(grid).T.reindex(columns=[day_label(d) for d in days]).fillna("–"), width="stretch")


def page_history(cfg, me):
    st.subheader("🕘 History — who did what")
    is_admin = st.session_state.get("p_role") == "admin"
    log, _ = read_csv(AUDIT_FILE, AUDIT_COLS, max_age=5)
    if log.empty:
        st.info("Nothing recorded yet. Every save, count, fix, sign-in and settings change will appear here.")
        return
    log = log.sort_values("Time", ascending=False)
    log["_d"] = log["Time"].astype(str).str[:10]
    c1, c2, c3, c4 = st.columns([1.3, 1.3, 1.3, 1.5])
    rng = c1.date_input("Period", value=(today_kh() - timedelta(days=6), today_kh()), key="h_rng")
    if isinstance(rng, (list, tuple)):
        d1, d2 = (rng[0], rng[-1]) if rng else (today_kh(), today_kh())
    else:
        d1 = d2 = rng
    log = log[(log["_d"] >= d1.isoformat()) & (log["_d"] <= d2.isoformat())]
    if is_admin:
        who = c2.multiselect("Person", sorted(set(log["Name"].astype(str)) - {""}), key="h_who")
        if who:
            log = log[log["Name"].isin(who)]
    else:
        log = log[log["Name"] == me]
        c2.caption(f"👤 Only your own actions ({me}).")
    acts = c3.multiselect("Action", sorted(set(log["Action"].astype(str))), key="h_act")
    if acts:
        log = log[log["Action"].isin(acts)]
    q = c4.text_input("Search", key="h_q", placeholder="bun, date, word…")
    if q.strip():
        log = log[log["Detail"].astype(str).str.contains(q.strip(), case=False, regex=False)]
    st.caption(f"{len(log):,} actions")
    show = log[["Time", "Name", "User", "Action", "Detail"]]
    st.dataframe(show, hide_index=True, width="stretch", height=min(600, 38 + 35 * max(len(show), 1)))
    st.download_button("⬇️ Download (CSV)", show.to_csv(index=False).encode("utf-8-sig"),
                       file_name=f"production_history_{d1}_{d2}.csv", mime="text/csv")


def users_box(cfg):
    """⚙️ Settings: new user, set someone's PIN / password, PINs for everybody (each box saves by itself)."""
    users = load_users()
    st.markdown("#### ➕ New user")
    with st.form("new_user", clear_on_submit=True):
        a, b, c = st.columns(3)
        uname = a.text_input("Username (small letters / numbers)").strip().lower()
        sname = b.text_input("Staff name (shown in the app)").strip()
        role = c.selectbox("Role", ["staff", "viewer", "sales", "admin"],
                           help="Same accounts as the Supply Hub: the role is also used there. "
                                "'staff' = operation staff (also gets the operation pages in the Supply Hub). "
                                "'viewer' = can only look in the Supply Hub.")
        d, e, f = st.columns(3)
        pin = d.text_input("🔢 PIN (4–6 numbers)", type="password", max_chars=6)
        pw = e.text_input("🔑 Password (optional, 8+ letters & numbers)", type="password")
        acc = f.selectbox("Production app access", ["auto", "edit", "view", "hidden"],
                          help="auto = by role (operation staff = edit)")
        ok = st.form_submit_button("➕ Create user", type="primary")
    if ok:
        err = ("Username: 3–30 small letters, numbers, . _ -" if not USERNAME_RE.match(uname)
               else "This username already exists." if uname in users
               else "Give a staff name." if not sname
               else "Give a PIN or a password." if not pin and not pw
               else (pin_problem(pin) if pin else "") or (pw_problem(pw) if pw else ""))
        if err:
            st.error(err)
        else:
            stamp = now_kh().strftime("%Y-%m-%d %H:%M:%S")
            rec = {"role": role, "active": True, "must_change": False, "created": stamp, "last_login": "",
                   "permissions": {}, "staff_name": sname, "pw_changed": stamp,
                   **_hash_pw(pw or pysecrets.token_urlsafe(18))}          # PIN-only: a random hidden password
            if pin:
                rec["pin"] = _pin_hash(pin)

            def add(us):
                if uname in us:
                    raise RuntimeError("This username already exists.")
                us[uname] = rec
            try:
                modify_users(add)
                if acc != "auto":
                    update_settings(lambda c: c.setdefault("access_override", {}).__setitem__(uname, acc))
                audit("user created", f"{uname} · {sname} · {role} · production {acc}")
                st.session_state["s_flash"] = (f"✅ {sname} ({uname}) created. Sign in: choose “{sname}” + "
                                               + ("the PIN." if pin else "the password."))
                st.rerun()
            except Exception as ex:
                st.error(f"Not created: {ex}")

    st.markdown("#### 🔢 Give / reset someone's PIN or password")
    others = sorted(users, key=lambda u: (users[u].get("staff_name") or u).lower())
    with st.form("reset_user", clear_on_submit=True):
        a, b, c = st.columns(3)
        who = a.selectbox("Person", others, index=None, placeholder="Choose",
                          format_func=lambda u: f"{users[u].get('staff_name') or u} ({u})"
                          + (" · 🔢" if users[u].get("pin") else ""))
        pin = b.text_input("New PIN (4–6 numbers)", type="password", max_chars=6)
        pw = c.text_input("New password (optional)", type="password")
        ok2 = st.form_submit_button("💾 Save")
    st.caption("🔢 after a name = already has a PIN. A new password signs that person out on their other phones.")
    if ok2:
        err = ("Choose a person." if not who else "Give a PIN or a password." if not pin and not pw
               else (pin_problem(pin) if pin else "") or (pw_problem(pw) if pw else ""))
        if err:
            st.error(err)
        else:
            try:
                if pin:
                    set_pin(who, pin)
                if pw:
                    change_password(who, pw)
                audit("PIN/password reset", f"{who}: " + " + ".join(x for x, y in (("PIN", pin), ("password", pw)) if y))
                st.session_state["s_flash"] = f"✅ Saved for {users[who].get('staff_name') or who}."
                st.rerun()
            except Exception as ex:
                st.error(f"Not saved: {ex}")

    no_pin = [u for u, r in users.items() if r.get("role") == "staff" and r.get("active", True) and not r.get("pin")]
    st.markdown("#### ⚡ PINs for all operation staff at once")
    shown = st.session_state.get("auto_pins")
    if shown:
        st.success(f"✅ {len(shown)} PINs made. Give each person their PIN (shown only now — they can change it "
                   "later with 🔑 PIN).")
        dfp = pd.DataFrame(shown)
        st.dataframe(dfp, hide_index=True, width="stretch")
        a, b = st.columns(2)
        a.download_button("⬇️ Download the PIN list (CSV)", dfp.to_csv(index=False).encode("utf-8-sig"),
                          file_name=f"staff_PINs_{today_kh()}.csv", mime="text/csv")
        if b.button("🙈 Hide the PIN list", key="auto_pin_hide"):
            st.session_state.pop("auto_pins", None)
            st.rerun()
    elif no_pin:
        st.caption(f"{len(no_pin)} operation staff have no PIN yet: "
                   + ", ".join(users[u].get("staff_name") or u for u in sorted(no_pin)))
        if st.button(f"⚡ Make a PIN for these {len(no_pin)} people", key="auto_pin"):
            made = {}
            for u in no_pin:
                while True:
                    pin = f"{pysecrets.randbelow(9000) + 1000}"
                    if not pin_problem(pin) and pin not in made.values():
                        break
                made[u] = pin

            def ch(us):
                for u, pin in made.items():
                    if u in us and not us[u].get("pin"):
                        us[u]["pin"] = _pin_hash(pin)
            try:
                modify_users(ch)
                audit("PINs made", ", ".join(sorted(made)))
                st.session_state["auto_pins"] = [{"Name": users[u].get("staff_name") or u, "Username": u, "PIN": pin}
                                                 for u, pin in sorted(made.items())]
                st.rerun()
            except Exception as ex:
                st.error(f"Not saved: {ex}")
    else:
        st.caption("✅ Every operation staff already has a PIN.")



def tasks_box(cfg):
    """⚙️ Settings: the 'Produced by' extra names and the daily task list. Returns the new values."""
    users = load_users()
    st.markdown("#### 👷 Names in “Produced by” (people without an account)")
    st.caption("All operation staff are already in the list by themselves — add here only helpers without an account.")
    ps = st.text_input("Separate with ;", value="; ".join(cfg.get("prod_staff") or []), key="set_pstaff")
    st.markdown("#### 📋 Daily tasks (checklist)")
    st.caption("auto **prod** = done by itself when production is saved for that day · auto **count** = done when the "
               "evening count is saved · empty = staff tap ✅. 'Who' = default people (Admin can change per day in 📋 Tasks).")
    people = staff_names(cfg, users)
    trs = [{"Task": t["name"], "Before": t["due"], "Auto": t["auto"] or "",
            "Who": "; ".join(t["who"]), **{EN_DAYS[i]: i in t["days"] for i in range(7)}, "_id": t["id"]}
           for t in task_list(cfg)]
    ted = st.data_editor(pd.DataFrame(trs, columns=["Task", "Before", "Auto", "Who", *EN_DAYS, "_id"]),
                         hide_index=True, width="stretch", num_rows="dynamic", key=f"set_tasks_{st.session_state.get('set_n', 0)}",
                         column_config={"_id": None,
                                        "Task": st.column_config.TextColumn("Task", required=True),
                                        "Before": st.column_config.TextColumn("⏰ Before (HH:MM)", validate=r"^([01]?\d|2[0-3]):[0-5]\d$"),
                                        "Auto": st.column_config.SelectboxColumn("Auto", options=["", "prod", "count"]),
                                        "Who": st.column_config.TextColumn("👥 Who (names, ;)", help="; ".join(people)),
                                        **{EN_DAYS[i]: st.column_config.CheckboxColumn(EN_DAYS[i]) for i in range(7)}})
    st.caption("Names: " + ", ".join(people))
    tasks = []
    for r in ted.to_dict("records"):
        if not str(r.get("Task") or "").strip():
            continue
        tid = r.get("_id") if isinstance(r.get("_id"), str) and r.get("_id") else uuid.uuid4().hex[:8]
        tasks.append({"id": tid, "name": str(r["Task"]).strip(), "due": str(r.get("Before") or "").strip(),
                      "auto": r.get("Auto") or "", "who": [x.strip() for x in str(r.get("Who") or "").split(";") if x.strip()],
                      "days": [i for i in range(7) if r.get(EN_DAYS[i]) is True or r.get(EN_DAYS[i]) == 1]})
    return {"prod_staff": [x.strip() for x in ps.split(";") if x.strip()], "tasks": tasks}


# ==========================================
# MAIN
# ==========================================
st.markdown(CSS, unsafe_allow_html=True)
if not st.session_state.get("p_user") and not restore_login():
    login_box()
if st.session_state.get("p_tok") and (st.session_state.pop("p_cookie_set", False)
                                      or time.time() - st.session_state.get("p_cookie_t", 0) > 600):
    _js(_js_set_cookie(st.session_state["p_tok"]))           # written again every 10 min (iPhone Safari keeps it fresh)
    st.session_state["p_cookie_t"] = time.time()
cfg, _srev = load_settings()
me_user, me_role = st.session_state["p_user"], st.session_state.get("p_role", "staff")
me = st.session_state.get("p_name") or me_user
level = access_of(me_user, me_role, cfg)
if level == "hidden":
    st.error("You do not have access to the Production app. Ask Admin.")
    if st.button("Sign out"):
        sign_out()
        st.rerun()
    st.stop()
can_edit = level == "edit"

top1, top2 = st.columns([4, 1])
top1.markdown(f"### 🏭 Production & Live Stock · នំប៉ាវហុងកុង")
with top2:
    st.caption(f"👤 {me} · {'✏️ edit' if can_edit else '👁️ view'}")
    b1, b2 = st.columns(2)
    with b1.popover("🔑 PIN", width="stretch"):
        my_pin_password_box(me_user)
    if b2.button("Sign out", key="signout", width="stretch"):
        sign_out()
        st.rerun()
if st.session_state.get("p_must_change"):
    st.info("🔢 Choose your own PIN now (tap 🔑 PIN at the top) — next time just pick your name and type it.")
my_tasks_banner(cfg, me)
pages = ["📊 Live stock", "🏭 Log production", "📦 Stock count", "🧊 3D rooms", "📋 Tasks", "📅 Next week plan",
         "🕘 History"]
if me_role == "admin":
    pages.append("⚙️ Settings")
if st.session_state.get("goto_page") in pages:
    st.session_state["page"] = st.session_state.pop("goto_page")
try:
    want = st.query_params.get("p", "")
    if "page" not in st.session_state and want in pages:
        st.session_state["page"] = want
except Exception:
    pass
if "phone_mode" not in st.session_state:
    try:
        _ua = st.context.headers.get("User-Agent", "") or ""
    except Exception:
        _ua = ""
    st.session_state["phone_mode"] = bool(re.search(r"Mobi|Android|iPhone|iPad", _ua))
page = st.radio("Page", pages, horizontal=True, key="page", label_visibility="collapsed")
st.toggle("📱 Phone mode (big boxes, one at a time)", key="phone_mode")
if st.session_state.get("phone_mode"):
    st.markdown(PHONE_CSS, unsafe_allow_html=True)
try:
    st.query_params["p"] = page
except Exception:
    pass
if not USE_DROPBOX:
    st.caption(f"💻 Local mode: data files in {LOCAL_DIR}")

try:
    if page == "📊 Live stock":
        live = st.toggle("🔄 Update by itself every 60 s", value=True, key="live_on")
        frag = st.fragment(run_every=60)(page_live) if live else st.fragment(page_live)
        frag(cfg, can_edit)
    elif page == "🏭 Log production":
        st.fragment(page_production)(cfg, can_edit, me)
    elif page == "📦 Stock count":
        st.fragment(page_count)(cfg, can_edit, me)
    elif page == "📅 Next week plan":
        st.fragment(page_plan)(cfg, can_edit)
    elif page == "🧊 3D rooms":
        st.fragment(page_rooms)(cfg)
    elif page == "📋 Tasks":
        page_tasks(cfg, can_edit, me)
    elif page == "🕘 History":
        st.fragment(page_history)(cfg, me)
    else:
        page_settings(cfg, me)
except Exception as err:          # a broken file must not blank the whole app
    st.error(f"⚠️ This page could not load: {err}. Press **R** or refresh the page; your saved data is safe. "
             "If it keeps happening, tell Admin.")
    if me_role == "admin":
        with st.expander("Details for Admin"):
            st.exception(err)
