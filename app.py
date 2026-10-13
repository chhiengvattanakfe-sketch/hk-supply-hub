# ============================================================
#  នំប៉ាវហុងកុង Supply Chain Hub  -  CLOUD VERSION WITH INVOICE
# ============================================================
import streamlit as st
import pandas as pd
import os
import io
import re
import csv
import time
import dropbox
import hmac
import traceback
from datetime import datetime, date
from zoneinfo import ZoneInfo

if not hasattr(st, "fragment"):
    def _fragment_shim(func=None, **kwargs):
        return func if func is not None else (lambda f: f)
    st.fragment = _fragment_shim

# ==========================================
# SECRETS & CONFIGURATION
# ==========================================
def get_secret(key, default=""):
    try: return st.secrets[key]
    except Exception: return default

DBX_APP_KEY = get_secret("DROPBOX_APP_KEY")
DBX_APP_SECRET = get_secret("DROPBOX_APP_SECRET")
DBX_REFRESH_TOKEN = get_secret("DROPBOX_REFRESH_TOKEN")
ADMIN_PASSWORD = get_secret("ADMIN_PASSWORD", "hk2026")
TEAM_PASSWORD = get_secret("TEAM_PASSWORD", "staff2026")

# Dropbox paths
DBX_EXCEL_PATH = "/dropbox/4- Sale Jounal/10_Sale_Journal_OCT_2026.xlsx"
DBX_DATA_PATH = "/dropbox/4- Sale Jounal/daily_delivery_expenses.csv"
DBX_PACKING_PATH = "/dropbox/4- Sale Jounal/daily_packing_progress.csv"

SHEET_NAME = "Master List"
JOURNAL_SHEET = "DAILY SALE JOUNAL"
COLUMN_NAME = "Customer Name"
JOURNAL_HEADER_TEXT = "ឈ្មោះអតិថិជន"
JOURNAL_CASES_HEADER = "កេស"          

TZ = ZoneInfo("Asia/Phnom_Penh")
DAYFIRST = True                        

LOCAL_DRIVERS = ["ងិន វុទ្ធា", "អួន តួ"]
OPS_STAFF = ["ឆែម សំណុក", "សាយ ប៊ុនលី", "ប៉ៅ រីណា", "ពេជ រដ្ឋា", "រ៉ូ សុវណ្ណាឌែន", "ហេង រតនា", "កង សៀន", "ណាត ផានិត"]
FOR_SALE_TEAM = ["For Sale (Team 1)", "For Sale (Team 2)"]

DISPATCH_COLS = ["Date", "Handled_By", "Customer", "Cases", "Local_Driver",
                 "Taxi_Station", "Phnom_Penh_Expense", "Taxi_Expense", "Note", "Verified_By"]
DISPATCH_NUM_COLS = ["Cases", "Phnom_Penh_Expense", "Taxi_Expense"]
PACKING_COLS = ["Date", "Prepared_By", "Customer", "Cases_Packed", "Status"]
PACKING_NUM_COLS = ["Cases_Packed"]
NUM_COLS_ALL = set(DISPATCH_NUM_COLS + PACKING_NUM_COLS)
STATUS_RANK = {"✅ Sent": 1, "🔵 Partial": 2, "🟡 Ready for Delivery": 3, "🟠 Packing": 4, "⏳ Pending": 5}

# ==========================================
# DROPBOX CONNECTION
# ==========================================
@st.cache_resource(show_spinner=False)
def get_dbx():
    if not DBX_REFRESH_TOKEN:
        st.error("Missing Dropbox API credentials in Streamlit Secrets.")
        st.stop()
    return dropbox.Dropbox(
        app_key=DBX_APP_KEY,
        app_secret=DBX_APP_SECRET,
        oauth2_refresh_token=DBX_REFRESH_TOKEN
    )

dbx = get_dbx()

def download_csv_from_dbx(dbx_path, cols):
    try:
        _, res = dbx.files_download(dbx_path)
        df = pd.read_csv(io.BytesIO(res.content), dtype=str, keep_default_na=False, encoding="utf-8-sig")
    except dropbox.exceptions.ApiError:
        df = pd.DataFrame(columns=cols)
    except Exception as e:
        st.warning(f"Error reading {dbx_path}: {e}")
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
        dbx.files_upload(
            csv_str.encode('utf-8-sig'), 
            dbx_path, 
            mode=dropbox.files.WriteMode("overwrite")
        )
    except Exception as e:
        st.error(f"Error saving to Dropbox: {e}")

def append_row_to_dbx(dbx_path, cols, row):
    df = download_csv_from_dbx(dbx_path, cols)
    ordered_row = {c: row.get(c, "-" if c not in NUM_COLS_ALL else 0) for c in cols}
    df = pd.concat([df, pd.DataFrame([ordered_row])], ignore_index=True)
    upload_csv_to_dbx(df, dbx_path)

@st.cache_data(ttl=60, show_spinner=False)
def get_excel_from_dbx(dbx_path):
    try:
        _, res = dbx.files_download(dbx_path)
        excel_bytes = io.BytesIO(res.content)
        df_cust = pd.read_excel(excel_bytes, sheet_name=SHEET_NAME)
        customers = sorted({str(x).strip() for x in df_cust[COLUMN_NAME].dropna() if str(x).strip()})
        excel_bytes.seek(0)
        df_journal = pd.read_excel(excel_bytes, sheet_name=JOURNAL_SHEET, header=None)
        return customers, df_journal, None
    except Exception as e:
        return [], None, str(e)

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
    if bad.any():
        out.loc[bad] = pd.to_datetime(s[bad].map(parse_dt), errors="coerce")
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

def rows_for_day(df, target_date):
    if df.empty or "_dt" not in df.columns: return df.iloc[0:0].copy()
    mask = df["_dt"].dt.normalize() == pd.Timestamp(target_date)
    out = df[mask].copy()
    out["Time"] = out["_dt"].dt.strftime("%I:%M %p")
    return out

# ==========================================
# UI HELPERS & FORMS
# ==========================================
def show_df(df, height=None, key=None, selectable=False):
    base = {"hide_index": True}
    if height: base["height"] = height
    sel = dict(on_select="rerun", selection_mode="single-row", key=key) if selectable else {}
    for width_kw in ({"width": "stretch"}, {"use_container_width": True}):
        try: return st.dataframe(df, **base, **width_kw, **sel)
        except Exception: continue
    st.dataframe(df, **base)
    return None

def flash_and_refresh(msg):
    st.session_state["flash"] = msg
    st.session_state["clear_sel"] = True
    st.rerun()

def admin_editor(dbx_path, cols, num_cols, key, label_cols):
    entered = st.text_input("🔑 Enter Admin Password to unlock edit tools:", type="password", key=f"pw_{key}")
    if entered == "": return
    if not hmac.compare_digest(entered.encode(), ADMIN_PASSWORD.encode()):
        st.error("❌ Incorrect Password.")
        return
    try:
        df = download_csv_from_dbx(dbx_path, cols)
        df_today = rows_for_day(df, today_kh())
        if df_today.empty:
            st.info("No entries logged for today.")
            return
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
                if pd.isna(parse_dt(new_vals["Date"])): st.error("❌ Date format is invalid.")
                else:
                    for c in cols: df.loc[row_idx, c] = new_vals[c]
                    upload_csv_to_dbx(df, dbx_path)
                    flash_and_refresh("Record updated")
            if col_del.form_submit_button("🗑️ Delete Wrong Entry"):
                upload_csv_to_dbx(df.drop(row_idx), dbx_path)
                flash_and_refresh("Record deleted")
    except Exception as e:
        st.warning(f"Could not load admin panel: {e}")

def dispatch_form(form_key, cust_list, fixed_customer=None, default_cases=1, verify=False):
    k = form_key
    with st.form(form_key, clear_on_submit=True):
        st.markdown("#### Order Details")
        dispatched_by = st.selectbox("Dispatched By:", ["-- Select Staff --"] + OPS_STAFF + FOR_SALE_TEAM, key=f"{k}_by")
        if fixed_customer is None:
            customer_name = st.selectbox("Customer Name / ID:", ["-- Select a Customer --"] + cust_list, key=f"{k}_cust")
        else:
            customer_name = fixed_customer
            st.markdown(f"**Customer:** {fixed_customer}")
        cases = st.number_input("ចំនួនកេស (Number of Cases):", min_value=0, step=1, value=int(default_cases), key=f"{k}_cases")
        if verify: verified_by = st.selectbox("✅ Cases verified by:", ["-- Select Staff --"] + OPS_STAFF + FOR_SALE_TEAM, key=f"{k}_vby")
        else: verified_by = st.selectbox("Cases verified by (optional):", ["-"] + OPS_STAFF + FOR_SALE_TEAM, key=f"{k}_vby")

        st.markdown("---")
        st.markdown("#### Transportation Details")
        local_driver = st.selectbox("Local Driver (Phnom Penh):", ["None (Grab/TukTuk)"] + LOCAL_DRIVERS, key=f"{k}_drv")
        taxi_station = st.text_input("Taxi Station Name (Leave blank if purely local):", key=f"{k}_taxi")
        delivery_note = st.text_input("📝 Note:", key=f"{k}_note")

        st.markdown("#### Expenses (៛ Riel)")
        pp_expense = st.number_input("1. Phnom Penh Expense (៛):", min_value=0, step=500, key=f"{k}_pp")
        taxi_expense = st.number_input("2. Taxi Expense (៛):", min_value=0, step=500, key=f"{k}_te")

        if st.form_submit_button("💾 Save Dispatch & Expenses"):
            if dispatched_by == "-- Select Staff --": st.error("❌ Please select who dispatched this order.")
            elif customer_name == "-- Select a Customer --": st.error("❌ Please select a valid Customer Name.")
            elif cases == 0: st.error("❌ Number of cases must be at least 1.")
            elif verify and verified_by == "-- Select Staff --": st.error("❌ Please select who verified the number of cases.")
            elif local_driver == "None (Grab/TukTuk)" and pp_expense == 0: st.error("❌ Please enter the Phnom Penh Expense.")
            elif taxi_station.strip() != "" and taxi_expense == 0: st.error("❌ Please enter the Taxi Expense.")
            else:
                handler_local = local_driver if local_driver != "None (Grab/TukTuk)" else "Grab/TukTuk"
                append_row_to_dbx(DBX_DATA_PATH, DISPATCH_COLS, {
                    "Date": now_str(), "Handled_By": dispatched_by, "Customer": customer_name.strip(),
                    "Cases": cases, "Local_Driver": handler_local, "Taxi_Station": taxi_station.strip() or "-",
                    "Phnom_Penh_Expense": pp_expense, "Taxi_Expense": taxi_expense, "Note": delivery_note.strip() or "-",
                    "Verified_By": verified_by,
                })
                flash_and_refresh(f"Dispatched by {dispatched_by}: {customer_name} | {cases} កេស")

def packing_form(form_key, cust_list, fixed_customer=None, default_cases=1):
    k = form_key
    with st.form(form_key, clear_on_submit=True):
        if fixed_customer is None:
            customer = st.selectbox("Customer Name / ID:", ["-- Select a Customer --"] + cust_list, key=f"{k}_cust")
        else:
            customer = fixed_customer
            st.markdown(f"**Customer:** {fixed_customer}")
        prepared_by = st.selectbox("Prepared / Packed By:", ["-- Select Staff --"] + OPS_STAFF + FOR_SALE_TEAM, key=f"{k}_by")

        col1, col2 = st.columns(2)
        with col1: cases_packed = st.number_input("ចំនួនកេស (Cases Packed):", min_value=0, step=1, value=int(default_cases), key=f"{k}_cases")
        with col2: pack_status = st.radio("Status:", ["In Progress (កំពុងធ្វើ)", "Completed (រួចរាល់)"], key=f"{k}_status")

        if st.form_submit_button("💾 Save Packing Progress"):
            if prepared_by == "-- Select Staff --": st.error("❌ Please select who is preparing this order.")
            elif customer == "-- Select a Customer --": st.error("❌ Please select a valid Customer Name.")
            elif cases_packed == 0: st.error("❌ Number of cases must be at least 1.")
            else:
                append_row_to_dbx(DBX_PACKING_PATH, PACKING_COLS, {
                    "Date": now_str(), "Prepared_By": prepared_by, "Customer": customer.strip(),
                    "Cases_Packed": cases_packed, "Status": pack_status,
                })
                flash_and_refresh(f"Packing logged: {customer} | {cases_packed} cases | {pack_status}")


# ==========================================
# APP SETUP & LOGIN SYSTEM
# ==========================================
st.set_page_config(page_title="Delivery Operations", page_icon="🚚", layout="wide")

if "logged_in" not in st.session_state:
    st.session_state["logged_in"] = False

if not st.session_state["logged_in"]:
    st.title("🔒 នំប៉ាវហុងកុង Login")
    st.info("Please log in to access the Supply Chain Hub.")
    
    with st.form("login_form"):
        user_name = st.selectbox("👤 User / Role:", ["-- Select Name --", "👨‍💻 Admin (Manager)"] + OPS_STAFF + LOCAL_DRIVERS + FOR_SALE_TEAM)
        password = st.text_input("🔑 Password:", type="password")
        submitted = st.form_submit_button("Log In")
        
        if submitted:
            if user_name == "-- Select Name --":
                st.error("Please select your name or role.")
            elif user_name == "👨‍💻 Admin (Manager)" and password == ADMIN_PASSWORD:
                st.session_state["logged_in"] = True
                st.session_state["user_name"] = "Admin"
                st.rerun()
            elif user_name != "-- Select Name --" and password == TEAM_PASSWORD:
                st.session_state["logged_in"] = True
                st.session_state["user_name"] = user_name
                st.rerun()
            else:
                st.error("❌ Incorrect Password.")
    st.stop()

# ==========================================
# MAIN APP LAYOUT
# ==========================================
st.title("🚚 នំប៉ាវហុងកុង Supply Chain Hub")

_flash = st.session_state.pop("flash", None)
if _flash: st.toast(_flash, icon="✅")

CUSTOMER_LIST, df_journal, EXCEL_ERROR = get_excel_from_dbx(DBX_EXCEL_PATH)

c_head, c_live = st.columns([4, 1])
with c_head:
    st.caption(f"🕒 {now_kh():%Y-%m-%d %I:%M %p} | ☁️ Connected to Dropbox | 👤 Logged in as: {st.session_state['user_name']}")
with c_live:
    if st.button("🚪 Logout"):
        st.session_state["logged_in"] = False
        st.rerun()

tab1, tab2, tab3 = st.tabs(["📦 1. Packing", "🚚 2. Dispatch", "📊 3. Live Dashboard"])

with tab1:
    st.markdown("### 📦 Bun Preparation & Packing")
    packing_form("packing_form", CUSTOMER_LIST)
    with st.expander("🛠️ Admin: Fix or Edit Today's Packing"):
        admin_editor(DBX_PACKING_PATH, PACKING_COLS, PACKING_NUM_COLS, "pack", ["Customer", "Cases_Packed", "Status"])
    
    st.markdown("---")
    st.subheader("📋 Today's Packing Log")
    df_pack_today = rows_for_day(download_csv_from_dbx(DBX_PACKING_PATH, PACKING_COLS), today_kh())
    if not df_pack_today.empty:
        show_df(df_pack_today[PACKING_COLS])
    else: st.info("No packing progress logged today yet.")

with tab2:
    st.markdown("### 🚚 Log Delivery Slip")
    dispatch_form("expense_form", CUSTOMER_LIST)
    with st.expander("🛠️ Admin: Fix or Edit Today's Dispatches"):
        admin_editor(DBX_DATA_PATH, DISPATCH_COLS, DISPATCH_NUM_COLS, "disp", ["Customer", "Cases"])
    
    st.markdown("---")
    st.subheader("📊 Today's Operations Log")
    df_disp_today = rows_for_day(download_csv_from_dbx(DBX_DATA_PATH, DISPATCH_COLS), today_kh())
    total_expense = int(df_disp_today["Phnom_Penh_Expense"].sum() + df_disp_today["Taxi_Expense"].sum()) if not df_disp_today.empty else 0
    m1, m2, m3 = st.columns(3)
    m1.metric("Total Slips Today", len(df_disp_today))
    m2.metric("Total Cases Dispatched", int(df_disp_today["Cases"].sum()) if not df_disp_today.empty else 0)
    m3.metric("Total Expenses Today (៛)", f"{total_expense:,}")
    if not df_disp_today.empty:
        show_df(df_disp_today[["Handled_By", "Customer", "Cases", "Note", "Local_Driver", "Taxi_Station", "Phnom_Penh_Expense", "Taxi_Expense", "Verified_By"]])
    else: st.info("No deliveries logged today yet.")

with tab3:
    c_live2, c_space = st.columns([1, 4])
    with c_live2:
        _live = st.checkbox(f"🔄 Auto-Refresh Dashboard", value=False, key="live_mode")
    if _live:
        try:
            from streamlit_autorefresh import st_autorefresh
            st_autorefresh(interval=30_000, key="dash_refresh")
        except ImportError: pass

    st.markdown("### 📊 Master Status Board")
    c_date, c_view = st.columns([1, 1])
    with c_date: selected_date = st.date_input("Select Report Date:", value=today_kh(), key="dash_date")
    with c_view: view_mode = st.radio("Layout Mode:", ["🖥️ Desktop Screen", "📱 Mobile Phone"], horizontal=True, key="dash_view")

    if EXCEL_ERROR: st.warning(f"Dropbox Error: {EXCEL_ERROR}")

    # Build the report and extract Invoice Number from Column 0
    scheduled = {}
    invoice_mapping = {}
    if df_journal is not None:
        cases_col = None
        for r in range(min(15, len(df_journal))):
            for c in range(df_journal.shape[1]):
                val = str(df_journal.iloc[r, c])
                if JOURNAL_CASES_HEADER in val:
                    cases_col = c
            if cases_col is not None: break
            
        for r in range(len(df_journal)):
         d = cell_to_date(df_journal.iloc[r, 0])
         if d == selected_date:
             name = str(df_journal.iloc[r, 1]).strip()
             if name and name != JOURNAL_HEADER_TEXT and name != "nan":
                 qty = pd.to_numeric(df_journal.iloc[r, cases_col], errors="coerce") if cases_col is not None else None

                 # Smart search: Automatically find the cell in this row that starts with "NP"
                 inv = "-"
                 for c_idx in range(df_journal.shape[1]):
                     val_str = str(df_journal.iloc[r, c_idx]).strip()
                     if val_str.startswith("NP") or val_str.startswith("np"):
                         inv = val_str
                         break
                 if inv == "-":
                     # Fallback if no "NP" prefix is found, try column 4 or 5
                     if df_journal.shape[1] > 4:
                         inv = str(df_journal.iloc[r, 4]).strip()

                 if inv in ("", "nan", "None", "ណាត", "NaT"): inv = "-"
                 scheduled[name] = int(qty) if pd.notna(qty) else None
                 invoice_mapping[name] = inv

    df_pack_all = download_csv_from_dbx(DBX_PACKING_PATH, PACKING_COLS)
    df_disp_all = download_csv_from_dbx(DBX_DATA_PATH, DISPATCH_COLS)
    
    pack_info, sent_info = {}, {}
    for cust, g in rows_for_day(df_pack_all, selected_date).groupby("Customer", sort=False):
        pack_info[cust] = {"cases": int(g["Cases_Packed"].sum()), "by": g["Prepared_By"].iloc[-1], "status": str(g["Status"].iloc[-1])}
    for cust, g in rows_for_day(df_disp_all, selected_date).groupby("Customer", sort=False):
        last = g.iloc[-1]
        station = str(last["Taxi_Station"]).strip()
        driver = f"{last['Local_Driver']} ➡️ {station}" if station not in ("-", "") else str(last["Local_Driver"])
        sent_info[cust] = {"cases": int(g["Cases"].sum()), "driver": driver, "note": str(last["Note"]), "by": str(last["Handled_By"]), "verified": str(last["Verified_By"]), "time": last["Time"]}

    rows = []
    for cust in set(scheduled) | set(pack_info) | set(sent_info):
        p, s = pack_info.get(cust), sent_info.get(cust)
        packed, sent = p["cases"] if p else 0, s["cases"] if s else 0
        ordered = scheduled.get(cust)
        target = packed if packed > 0 else (ordered or 0)
        invoice_num = invoice_mapping.get(cust, "-")
        
        if s: status = "🔵 Partial" if (target > 0 and sent < target) else "✅ Sent"
        elif p: status = "🟠 Packing" if "In Progress" in p["status"] else "🟡 Ready for Delivery"
        else: status = "⏳ Pending"
        
        rows.append({
            "Invoice": invoice_num, "Customer": cust, "Status": status, "កេស": ordered, "Packed Cases": packed, "Prepared By": p["by"] if p else "-",
            "Sent Cases": sent, "Handled By": s["by"] if s else "-", "Verified By": s["verified"] if s else "-",
            "Driver/Station": s["driver"] if s else "-", "Note": s["note"] if s else "-", "Time": s["time"] if s else "-",
            "Source": "Journal" if cust in scheduled else "⚠️ Not in journal",
        })
        
    df_report = pd.DataFrame(rows)
    if not df_report.empty:
        df_report["កេស"] = pd.array(df_report["កេស"].tolist(), dtype="Int64")
        df_report["_r"] = df_report["Status"].map(STATUS_RANK)
        df_report = df_report.sort_values(by=["_r", "Customer"]).drop(columns=["_r"]).reset_index(drop=True)

        counts = df_report["Status"].value_counts()
        k1, k2, k3, k4, k5 = st.columns(5)
        k1.metric("⏳ Pending", int(counts.get("⏳ Pending", 0)))
        k2.metric("🟠 Packing", int(counts.get("🟠 Packing", 0)))
        k3.metric("🟡 Ready", int(counts.get("🟡 Ready for Delivery", 0)))
        k4.metric("🔵 Partial", int(counts.get("🔵 Partial", 0)))
        k5.metric("✅ Sent", int(counts.get("✅ Sent", 0)))

        st.markdown("---")
        
        search_query = st.text_input("🔍 Search Customer or Invoice:", placeholder="Type a name or invoice number (e.g., NP312578) to filter...")
        if search_query:
            mask = df_report["Customer"].str.contains(search_query, case=False, na=False) | df_report["Invoice"].str.contains(search_query, case=False, na=False)
            df_report = df_report[mask].reset_index(drop=True)

        if st.session_state.pop("clear_sel", False): st.session_state.pop("dash_table", None)

        if view_mode == "🖥️ Desktop Screen": col_table, col_edit = st.columns([1.6, 1.4]) 
        else:
            col_table = st.container()
            st.markdown("<br>", unsafe_allow_html=True)
            col_edit = st.container() 

        with col_table:
            table_height = 550 if view_mode == "🖥️ Desktop Screen" else 350
            event = show_df(df_report, height=table_height, key="dash_table", selectable=True)
            if event:
                rows_sel = event.selection.rows
                if rows_sel: st.session_state["sel_cust"] = df_report.iloc[rows_sel[0]]["Customer"]
                else: st.session_state.pop("sel_cust", None)

        with col_edit:
            selected = st.session_state.get("sel_cust")
            if selected not in set(df_report["Customer"]): selected = None
            if selected:
                st.markdown(f"### ✏️ Quick Update")
                st.success(f"**Selected:** {selected}")
                if selected_date != today_kh(): st.info("⚠️ Updates can only be saved for today.")
                else:
                    p_row = df_report[df_report["Customer"] == selected].iloc[0]
                    ordered_n = int(p_row["កេស"]) if pd.notna(p_row["កេស"]) else None
                    packed_n, sent_n = int(p_row["Packed Cases"]), int(p_row["Sent Cases"])
                    target_n = packed_n if packed_n > 0 else (ordered_n or 0)

                    st.caption(f"**Invoice:** {p_row['Invoice']} | **Status:** {p_row['Status']}")
                    st.caption(f"**Ordered:** {ordered_n if ordered_n is not None else '-'} កេស | **Packed:** {packed_n} | **Sent:** {sent_n}")

                    pack_default = max((ordered_n or 0) - packed_n, 0) or 1
                    send_default = (target_n - sent_n) if (target_n - sent_n) > 0 else 1

                    t_pack, t_send = st.tabs(["📦 Step 1: Pack Buns", "🚚 Step 2: Send & Verify"])
                    with t_pack: packing_form(f"dash_pack_{selected}", CUSTOMER_LIST, fixed_customer=selected, default_cases=pack_default)
                    with t_send: dispatch_form(f"dash_send_{selected}", CUSTOMER_LIST, fixed_customer=selected, default_cases=send_default, verify=True)
            else:
                if view_mode == "🖥️ Desktop Screen": st.info("👈 **Click on any customer in the table** to update.")
                else: st.info("👆 **Click on any customer in the table above** to update.")
    else:
        st.info(f"📅 No orders scheduled or found in the journal for {selected_date}.")
