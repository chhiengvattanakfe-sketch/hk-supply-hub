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
import os
import re
import threading
import time
import uuid
from datetime import date, datetime, timedelta

import pandas as pd
import streamlit as st

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
JOURNAL_PATTERN = "*_Sale_Jou*.xlsx"
JOURNAL_SHEET = "DAILY SALE JOUNAL"
BUN_RE = re.compile(r"^N\d+$")
MONTHS = ["JAN", "FEB", "MAR", "APR", "MAY", "JUN", "JUL", "AUG", "SEP", "OCT", "NOV", "DEC"]
KH_DAYS = ["ច័ន្ទ", "អង្គារ", "ពុធ", "ព្រហស្បតិ៍", "សុក្រ", "សៅរ៍", "អាទិត្យ"]
EN_DAYS = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

PROD_COLS = ["Saved_At", "Prod_Date", "Bun", "Pcs", "By", "Note", "Entry_Id"]
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
    "access": {},                   # username -> hidden / view / edit (Admin always edit)
    "access_default": "view",
    "places": ["ស្តុកនំក្នុងទូរ", "ស្តុកទូរកក"],   # freezers counted every evening (one tab each)
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
    try:
        if rev:
            day_copy = f"{DROPBOX_FOLDER}/backups/{today_kh():%Y-%m-%d}_{name}"
            try:
                _dbx().files_copy_v2(path, day_copy)       # first save of the day keeps yesterday's version
            except Exception:
                pass
        md = _dbx().files_upload(data, path, mode=mode, mute=True, autorename=False)
    except dropbox.exceptions.ApiError as e:
        if "conflict" in str(e).lower():
            raise Conflict(name) from e
        raise
    m = _mem()
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


def save_settings(new):
    for attempt in range(4):
        _old, rev = read_bytes(SETTINGS_FILE, max_age=0)
        try:
            write_bytes(SETTINGS_FILE, json.dumps(new, ensure_ascii=False, indent=1).encode("utf-8"), rev)
            return
        except Conflict:
            time.sleep(0.4)
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


def _check_pw(password, rec):
    try:
        dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), bytes.fromhex(rec["salt"]), int(rec["iter"]))
        return hmac.compare_digest(dk.hex(), rec["hash"])
    except Exception:
        return False


def access_of(username, role, settings):
    if role == "admin":
        return "edit"
    return settings.get("access", {}).get(username, settings.get("access_default", "view"))


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
    with st.form("login"):
        u = st.text_input("Username").strip().lower()
        p = st.text_input("Password", type="password")
        ok = st.form_submit_button("Sign in", type="primary")
    st.caption("Use the same username and password as the Supply Hub app.")
    if ok:
        rec = users.get(u)
        if rec and rec.get("active", True) and _check_pw(p, rec):
            st.session_state.update(p_user=u, p_role=rec.get("role", "staff"), p_name=rec.get("staff_name") or u)
            st.rerun()
        time.sleep(1)
        st.error("Wrong username or password.")
    st.stop()


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
    p["_n"] = p["Pcs"].map(_num)
    a = adjs.copy()
    a["_d"] = a["Date"].map(_day)
    a["_pd"] = a["Prod_Date"].map(_day)
    a["_n"] = a["Pcs"].map(_num)
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
    p_today = prod[prod["Prod_Date"].map(_day) == t]["Pcs"].map(_num).sum()
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
    data = [{"Production date": d, **{short(b): (int(v[b]) if v.get(b) else None) for b in buns}} for d, v in rows]
    df = pd.DataFrame(data, columns=["Production date"] + [short(b) for b in buns])
    df["Production date"] = pd.to_datetime(df["Production date"])
    for b in buns:                    # digits as text: an empty cell stays really empty (no grey 'None')
        df[short(b)] = ["" if v is None or pd.isna(v) else str(int(v)) for v in df[short(b)]]
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
    flash = st.session_state.pop("p_flash", None)
    if flash:
        st.success(flash)
    if can_edit:
        st.markdown("Type the pcs produced like in your Excel sheet — **one row per production date** "
                    "(add a row with ＋ for another day). Empty = 0.")
        n = st.session_state.get("prod_grid_n", 0)
        ed = _grid([(today_kh(), {})], show, key=f"prod_grid_{n}", height=120, max_date=today_kh() + timedelta(days=1))
        got = [(d, v) for d, v in _grid_values(ed, show) if v]
        if got:
            st.markdown(excel_html("ផលិតថ្មី (not saved yet)", [(day_label(d), v) for d, v in got], show),
                        unsafe_allow_html=True)
        c1, c2 = st.columns([3, 1])
        note = c1.text_input("Note (optional)", max_chars=120, key="prod_note")
        c2.write("")
        if c2.button("💾 Save production", type="primary", width="stretch", disabled=not got):
            stamp, eid = now_kh().strftime("%Y-%m-%d %H:%M:%S"), uuid.uuid4().hex[:10]
            new = pd.DataFrame([{"Saved_At": stamp, "Prod_Date": d.isoformat(), "Bun": b, "Pcs": str(int(v)),
                                 "By": me, "Note": note.strip(), "Entry_Id": eid} for d, vals in got for b, v in vals.items()])
            try:
                modify_csv(PROD_FILE, PROD_COLS, lambda df: pd.concat([df, new], ignore_index=True))
                st.session_state["p_flash"] = (f"✅ Saved {int(new['Pcs'].astype(int).sum()):,} pcs · "
                                               + ", ".join(f"{d:%d %b}" for d, _v in got))
                st.session_state["prod_grid_n"] = n + 1           # empty sheet for the next entry
                _rerun_here()
            except Exception as e:
                st.error(f"Not saved: {e}")
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
    view = view.assign(_n=view["Pcs"].map(_num))
    by_day = view.groupby(["_d", "Bun"])["_n"].sum()
    rows = [(day_label(d), {b: by_day.get((d, b), 0) for b in show}) for d in sorted(set(view["_d"]))]
    st.markdown(excel_html(f"ផលិត ({d_from:%d.%m} – {d_to:%d.%m.%Y})", rows, show), unsafe_allow_html=True)
    with st.expander(f"✏️ Fix or delete a saved line ({len(view)} lines)"):
        mine = view if st.session_state.get("p_role") == "admin" else view[view["By"] == me]
        if not can_edit or mine.empty:
            st.caption("Only your own lines (Admin: all) can be changed here.")
            return
        ed = st.data_editor(mine[["Saved_At", "Prod_Date", "Bun", "Pcs", "By", "Note", "Entry_Id"]].assign(Delete=False),
                            hide_index=True, width="stretch", key="prod_fix",
                            disabled=["Saved_At", "By", "Entry_Id", "Bun"],
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


def page_count(cfg, can_edit, me):
    st.subheader("📦 Evening stock count")
    prod, counts, adjs, sales, names, buns = get_data(cfg)
    places = list(cfg.get("places") or DEFAULT_SETTINGS["places"])
    flash = st.session_state.pop("c_flash", None)
    if flash:
        st.success(flash)
    c1, c2 = st.columns([1, 2])
    cd = c1.date_input("Count date (stock at the END of this day)", value=today_kh(), max_value=today_kh(), key="cnt_date")
    expected, _short, _h, _nc = compute_stock(buns, prod, counts, adjs, sales, cd)
    show = active_buns(buns, sales, expected)
    lastp = last_place_counts(counts, places)
    c2.caption("Count every freezer in the evening, after the last delivery. Each tab is one freezer, laid out like your "
               "Excel sheet. It starts filled in — **only change the numbers that are different**, add a row (＋) for a "
               "date that is missing, clear a cell that is empty in the freezer.")
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
    tabs = st.tabs([f"🧊 {pl}" for pl in places] + ["✅ Check & save"])
    counted = {}
    for pl, tab in zip(places, tabs):
        with tab:
            ed = _grid(start_rows[pl], show, key=f"cnt_{pl}_{cd}_{mode[:2]}_{st.session_state.get('cnt_n', 0)}",
                       max_date=cd)
            counted[pl] = _grid_values(ed, show)
            st.markdown(excel_html(f"{pl} ({cd:%d.%m.%Y})", [(day_label(d), v) for d, v in sorted(counted[pl])], show),
                        unsafe_allow_html=True)
    with tabs[-1]:
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
            if st.button(f"💾 Save the evening count ({int(sum(tot_c.values())):,} pcs)", type="primary", key="cnt_save"):
                cid, stamp = uuid.uuid4().hex[:10], now_kh().strftime("%Y-%m-%d %H:%M:%S")
                new = [{"Saved_At": stamp, "Count_Date": cd.isoformat(), "Bun": b, "Prod_Date": d.isoformat(),
                        "Pcs": str(int(n)), "By": me, "Count_Id": cid, "Place": pl}
                       for pl in places for d, v in counted[pl] for b, n in v.items()]
                have = {r["Bun"] for r in new}
                new += [{"Saved_At": stamp, "Count_Date": cd.isoformat(), "Bun": b, "Prod_Date": cd.isoformat(), "Pcs": "0",
                         "By": me, "Count_Id": cid, "Place": places[0]} for b in buns if b not in have]   # counted empty
                try:
                    modify_csv(COUNT_FILE, COUNT_COLS, lambda df: pd.concat([df, pd.DataFrame(new)], ignore_index=True))
                    st.session_state["c_flash"] = f"✅ Evening count saved for {cd:%d %b %Y}: {int(sum(tot_c.values())):,} pcs"
                    st.session_state["cnt_n"] = st.session_state.get("cnt_n", 0) + 1
                    _rerun_here()
                except Exception as e:
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
            try:
                modify_csv(ADJ_FILE, ADJ_COLS, lambda df: pd.concat([df, pd.DataFrame([row])], ignore_index=True))
                st.session_state["c_flash"] = f"✅ Adjustment saved: {kind[2:]} {n:,} pcs {b}"
                _rerun_here()
            except Exception as e:
                st.error(f"Not saved: {e}")
    if not adjs.empty:
        st.dataframe(adjs.sort_values("Saved_At", ascending=False).head(50)[["Date", "Bun", "Prod_Date", "Pcs", "Reason", "By"]],
                     hide_index=True, width="stretch")


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
    flash = st.session_state.pop("s_flash", None)
    if flash:
        st.success(flash)
    n = st.session_state.get("set_n", 0)
    draft = st.session_state.get("set_draft")
    if draft is None or [r["Bun"] for r in draft] != buns:
        draft = _bun_rows(cfg, buns, names)
        st.session_state["set_draft"] = draft

    st.markdown("#### 🎯 Stock target, production days and shelf life — per bun")
    st.caption("The table below is what the app uses. Change any cell, or fill many buns at once with the buttons, "
               "then press **💾 Save settings**.")
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
    rnd = c3.number_input("Round planned pcs up to", min_value=1, max_value=1000, value=int(cfg["round_to"]), key="set_rnd")
    capp = c4.number_input("Max production per day (0 = no limit)", min_value=0, max_value=500000, step=1000,
                           value=int(cfg.get("max_prod_per_day") or 0), key="set_cap")
    prio = st.multiselect("Keep these at their target first when the total limit is reached", buns, default=prio_now,
                          key="set_prio")
    places_txt = st.text_input("Freezers counted in the evening (separate with ;)",
                               value="; ".join(cfg.get("places") or DEFAULT_SETTINGS["places"]), key="set_places")

    st.markdown("#### 👥 Who can use this app (Admin can always edit)")
    users = load_users()
    urows = [{"User": u, "Name": r.get("staff_name", ""), "Role": r.get("role", ""),
              "Access": cfg.get("access", {}).get(u, cfg.get("access_default", "view"))}
             for u, r in sorted(users.items()) if r.get("role") != "admin"]
    uacc = st.data_editor(pd.DataFrame(urows), hide_index=True, width="stretch", num_rows="fixed",
                          disabled=["User", "Name", "Role"], key=f"set_users_{n}",
                          column_config={"Access": st.column_config.SelectboxColumn(
                              "Access", options=["hidden", "view", "edit"], required=True)}) if urows else None
    dflt = st.selectbox("New / other users", ["view", "hidden", "edit"],
                        index=["view", "hidden", "edit"].index(cfg.get("access_default", "view")), key="set_dflt")

    if st.button("💾 Save settings", type="primary", key="set_save"):
        new = dict(cfg)
        rows = ed.to_dict("records")
        new.update(max_total=int(max_total), target_default=int(t_all), shelf_days=int(s_all), lookback_days=int(look),
                   round_to=int(rnd), max_prod_per_day=int(capp), priority=list(prio), access_default=dflt,
                   places=[p.strip() for p in places_txt.split(";") if p.strip()] or DEFAULT_SETTINGS["places"],
                   # every bun saved with its own value: exactly what the table shows is what the app uses
                   target_days={r["Bun"]: int(r["Target days"]) for r in rows},
                   shelf_by_bun={r["Bun"]: int(r["Shelf life (days)"]) for r in rows},
                   prod_days={r["Bun"]: [i for i in range(7) if r[EN_DAYS[i]]] for r in rows})
        if uacc is not None:
            new["access"] = {r["User"]: r["Access"] for r in uacc.to_dict("records")}
        try:
            save_settings(new)
            st.session_state.pop("set_draft", None)
            st.session_state["set_n"] = n + 1
            st.session_state["s_flash"] = ("✅ Settings saved · targets: " + ", ".join(
                f"{short(r['Bun'])} {int(r['Target days'])}d" for r in rows))
            st.rerun()
        except Exception as e:
            st.error(f"Not saved: {e}")


# ==========================================
# MAIN
# ==========================================
st.markdown(CSS, unsafe_allow_html=True)
if not st.session_state.get("p_user"):
    login_box()
cfg, _srev = load_settings()
me_user, me_role = st.session_state["p_user"], st.session_state.get("p_role", "staff")
me = st.session_state.get("p_name") or me_user
level = access_of(me_user, me_role, cfg)
if level == "hidden":
    st.error("You do not have access to the Production app. Ask Admin.")
    if st.button("Sign out"):
        st.session_state.clear()
        st.rerun()
    st.stop()
can_edit = level == "edit"

top1, top2 = st.columns([4, 1])
top1.markdown(f"### 🏭 Production & Live Stock · នំប៉ាវហុងកុង")
with top2:
    st.caption(f"👤 {me} · {'✏️ edit' if can_edit else '👁️ view'}")
    if st.button("Sign out", key="signout"):
        st.session_state.clear()
        st.rerun()
pages = ["📊 Live stock", "🏭 Log production", "📦 Stock count", "📅 Next week plan"]
if me_role == "admin":
    pages.append("⚙️ Settings")
try:
    want = st.query_params.get("p", "")
    if "page" not in st.session_state and want in pages:
        st.session_state["page"] = want
except Exception:
    pass
page = st.radio("Page", pages, horizontal=True, key="page", label_visibility="collapsed")
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
    else:
        page_settings(cfg, me)
except Exception as err:          # a broken file must not blank the whole app
    st.error(f"Something went wrong on this page: {err}")
    st.exception(err)
