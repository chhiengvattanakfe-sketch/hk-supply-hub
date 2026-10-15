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
