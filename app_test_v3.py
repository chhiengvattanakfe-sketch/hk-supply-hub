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
import csv
import json
import traceback
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

# ==========================================
# 🌐 ENGLISH / ខ្មែរ — the screen text only (data, files and codes stay as they are)
# ==========================================
KM = {
    # --- pages, top bar, sign in ---------------------------------------------------------------
    "Production & Live Stock": "ផលិតកម្ម និង ស្តុកបច្ចុប្បន្ន",
    "Production & Stock": "ផលិតកម្ម និង ស្តុក",
    "📊 Live stock": "📊 ស្តុកបច្ចុប្បន្ន",
    "🏭 Log production": "🏭 កត់ត្រាការផលិត",
    "🏭 Log today's production": "🏭 កត់ត្រាការផលិតថ្ងៃនេះ",
    "📦 Stock count": "📦 រាប់ស្តុក",
    "🧊 3D rooms": "🧊 បន្ទប់ 3D",
    "📋 Tasks": "📋 ការងារ",
    "📅 Next week plan": "📅 ផែនការសប្តាហ៍ក្រោយ",
    "🕘 History": "🕘 ប្រវត្តិ",
    "🤖 Bot": "🤖 បូត",
    "⚙️ Settings": "⚙️ ការកំណត់",
    "📱 Phone mode (big boxes, one at a time)": "📱 របៀបទូរស័ព្ទ (ប្រអប់ធំ ម្តងមួយៗ)",
    "🔄 Update by itself every 60 s": "🔄 ធ្វើបច្ចុប្បន្នភាពដោយខ្លួនឯង រៀងរាល់ 60 វិនាទី",
    "Sign out": "ចាកចេញ",
    "Sign in": "ចូល",
    "✏️ edit": "✏️ កែបាន",
    "👁️ view": "👁️ មើលតែប៉ុណ្ណោះ",
    "🔑 PIN": "🔑 PIN",
    "👤 My name + PIN": "👤 ឈ្មោះខ្ញុំ + PIN",
    "🔑 Username + password": "🔑 ឈ្មោះអ្នកប្រើ + ពាក្យសម្ងាត់",
    "🔢 My PIN": "🔢 PIN របស់ខ្ញុំ",
    "🔑 My password": "🔑 ពាក្យសម្ងាត់របស់ខ្ញុំ",
    "👤 Your name": "👤 ឈ្មោះរបស់អ្នក",
    "Tap to choose your name": "ចុចដើម្បីជ្រើសឈ្មោះរបស់អ្នក",
    "Keep me signed in on this phone / computer": "ចងចាំខ្ញុំនៅលើទូរស័ព្ទ / កុំព្យូទ័រនេះ",
    "Keep me signed in on this phone": "ចងចាំខ្ញុំនៅលើទូរស័ព្ទនេះ",
    "days)": "ថ្ងៃ)",
    "Username (small letters / numbers)": "ឈ្មោះអ្នកប្រើ (អក្សរតូច / លេខ)",
    "Username": "ឈ្មោះអ្នកប្រើ",
    "Password": "ពាក្យសម្ងាត់",
    "Wrong username or password.": "ឈ្មោះអ្នកប្រើ ឬពាក្យសម្ងាត់មិនត្រឹមត្រូវ។",
    "Wrong PIN.": "PIN មិនត្រឹមត្រូវ។",
    "Too many wrong PINs. Wait 10 minutes, or sign in with your password.":
        "វាយ PIN ខុសច្រើនដងពេក។ រង់ចាំ 10 នាទី ឬចូលដោយពាក្យសម្ងាត់។",
    "Choose your name first.": "សូមជ្រើសឈ្មោះរបស់អ្នកជាមុនសិន។",
    "The same username and password as the Supply Hub app.": "ឈ្មោះអ្នកប្រើ និងពាក្យសម្ងាត់ដូចកម្មវិធី Supply Hub។",
    "No PIN yet? Sign in once with your password (other tab), then tap 🔑 PIN at the top to choose one. Or ask Admin to give you one.":
        "មិនទាន់មាន PIN? ចូលម្តងដោយពាក្យសម្ងាត់ (ផ្ទាំងមួយទៀត) រួចចុច 🔑 PIN ខាងលើដើម្បីជ្រើសរើស។ ឬសុំ Admin ឲ្យ។",
    "You have no PIN yet — sign in with your password once, then choose a PIN.":
        "អ្នកមិនទាន់មាន PIN — ចូលដោយពាក្យសម្ងាត់ម្តង រួចជ្រើសរើស PIN។",
    "Local test mode: no accounts file — you are signed in as admin.": "របៀបសាកល្បង: គ្មានឯកសារគណនី — អ្នកបានចូលជា admin។",
    "Cannot read the accounts (users.json) in the Dropbox folder. Check the app Secrets.":
        "មិនអាចអានគណនី (users.json) ក្នុង Dropbox បានទេ។ សូមពិនិត្យ Secrets របស់កម្មវិធី។",
    "You do not have access to the Production app. Ask Admin.": "អ្នកមិនមានសិទ្ធិប្រើកម្មវិធីផលិតកម្មទេ។ សូមសួរ Admin។",
    "🔢 Choose your own PIN now (tap 🔑 PIN at the top) — next time just pick your name and type it.":
        "🔢 សូមជ្រើស PIN ផ្ទាល់ខ្លួនឥឡូវនេះ (ចុច 🔑 PIN ខាងលើ) — លើកក្រោយគ្រាន់តែជ្រើសឈ្មោះ ហើយវាយ PIN។",
    "💻 Local mode: data files in": "💻 របៀបក្នុងម៉ាស៊ីន: ឯកសារទិន្នន័យនៅ",
    "Type the PIN again": "វាយ PIN ម្តងទៀត",
    "💾 Save my PIN": "💾 រក្សាទុក PIN របស់ខ្ញុំ",
    "Current password": "ពាក្យសម្ងាត់បច្ចុប្បន្ន",
    "New password (8+ characters, letters and numbers)": "ពាក្យសម្ងាត់ថ្មី (8 តួអក្សរឡើង មានអក្សរ និងលេខ)",
    "Type the new password again": "វាយពាក្យសម្ងាត់ថ្មីម្តងទៀត",
    "💾 Change my password": "💾 ប្តូរពាក្យសម្ងាត់",
    "A password needs at least 8 characters, with letters and numbers.": "ពាក្យសម្ងាត់ត្រូវមានយ៉ាងតិច 8 តួ មានអក្សរ និងលេខ។",
    "A PIN is 4 to 6 numbers.": "PIN ជាលេខ 4 ដល់ 6 ខ្ទង់។",
    "The two PINs are different.": "PIN ទាំងពីរមិនដូចគ្នា។",
    "Too easy to guess — choose another PIN.": "ងាយទាយពេក — សូមជ្រើស PIN ផ្សេង។",
    "The current password is wrong.": "ពាក្យសម្ងាត់បច្ចុប្បន្នមិនត្រឹមត្រូវ។",
    "The two new passwords are different.": "ពាក្យសម្ងាត់ថ្មីទាំងពីរមិនដូចគ្នា។",
    "✅ Password changed (also for the Supply Hub).": "✅ បានប្តូរពាក្យសម្ងាត់ (ក៏សម្រាប់ Supply Hub ដែរ)។",
    "✅ PIN saved. Next time: choose your name + type this PIN.": "✅ បានរក្សាទុក PIN។ លើកក្រោយ: ជ្រើសឈ្មោះ + វាយ PIN នេះ។",
    "Account not found.": "រកមិនឃើញគណនី។",

    # --- common words ---------------------------------------------------------------------------
    "❄️ Cooling room": "❄️ ទូរត្រជាក់",
    "🧊 Freezer room": "🧊 ទូរកក",
    "🧊 Frozen room": "🧊 ទូរកក",
    "Cooling room": "ទូរត្រជាក់",
    "cooling room": "ទូរត្រជាក់",
    "Freezer room": "ទូរកក",
    "Frozen room": "ទូរកក",
    "frozen room": "ទូរកក",
    "🧊 Freezer": "🧊 ទូរកក",
    "Frozen AEON": "AEON កក",
    "🛒 AEON line": "🛒 ជួរ AEON",
    "AEON line": "ជួរ AEON",
    "AEON orders only": "សម្រាប់ការបញ្ជាទិញ AEON តែប៉ុណ្ណោះ",
    "only for AEON orders": "សម្រាប់តែការបញ្ជាទិញ AEON",
    "Raw material (keep empty)": "វត្ថុធាតុដើម (ទុកទំនេរ)",
    "Raw material": "វត្ថុធាតុដើម",
    "🚶 Walkway (keep free)": "🚶 ផ្លូវដើរ (ទុកទំនេរ)",
    "🚶 Walkway": "🚶 ផ្លូវដើរ",
    "walkway": "ផ្លូវដើរ",
    "Cooling fan": "កង្ហារត្រជាក់",
    "Door IN": "ទ្វារចូល",
    "Door OUT": "ទ្វារចេញ",
    "Door in": "ទ្វារចូល",
    "door out": "ទ្វារចេញ",
    "FRONT · take here first · door out": "ខាងមុខ · យកពីនេះមុន · ទ្វារចេញ",
    "Production date": "ថ្ងៃផលិត",
    "production date": "ថ្ងៃផលិត",
    "production dates": "ថ្ងៃផលិត",
    "oldest production date first": "ថ្ងៃផលិតចាស់ជាងគេមុន",
    "oldest date first": "ថ្ងៃចាស់ជាងគេមុន",
    "Oldest batch": "ឡូតិ៍ចាស់ជាងគេ",
    "Bun(s) of this lane": "នំក្នុងជួរនេះ",
    "Bun(s)": "នំ",
    "Bun": "នំ",
    "Name": "ឈ្មោះ",
    "Date": "ថ្ងៃ",
    "Day": "ថ្ងៃ",
    "Pcs": "គ្រាប់",
    "pcs": "គ្រាប់",
    "Crates": "កេស",
    "crates": "កេស",
    "crate": "កេស",
    "cr": "កេស",
    "stacks": "ជង់",
    "stack": "ជង់",
    "Places": "កន្លែង",
    "places": "កន្លែង",
    "lanes": "ជួរ",
    "Lane": "ជួរ",
    "lane": "ជួរ",
    "Column": "ជួរឈរ",
    "front": "ខាងមុខ",
    "2nd": "ទី2",
    "3rd": "ទី3",
    "4th": "ទី4",
    "5th": "ទី5",
    "6th": "ទី6",
    "FRONT": "ខាងមុខ",
    "BACK": "ខាងក្រោយ",
    "Stock": "ស្តុក",
    "Status": "ស្ថានភាព",
    "Total stock": "ស្តុកសរុប",
    "Room": "បន្ទប់",
    "Note (optional)": "កំណត់ចំណាំ (មិនចាំបាច់)",
    "Note": "កំណត់ចំណាំ",
    "Time": "ម៉ោង",
    "User": "អ្នកប្រើ",
    "Action": "សកម្មភាព",
    "Detail": "ព័ត៌មានលម្អិត",
    "Person": "បុគ្គល",
    "Role": "តួនាទី",
    "Access": "សិទ្ធិ",
    "Search": "ស្វែងរក",
    "Period": "រយៈពេល",
    "Type": "ប្រភេទ",
    "Reason": "មូលហេតុ",
    "Delete": "លុប",
    "Count": "រាប់",
    "Counted": "បានរាប់",
    "App expected": "កម្មវិធីរំពឹង",
    "Difference": "ខុសគ្នា",
    "Expected sales": "ការលក់រំពឹងទុក",
    "Produce": "ផលិត",
    "Target days": "ថ្ងៃគោលដៅ",
    "Shelf life (days)": "អាយុកាលប្រើប្រាស់ (ថ្ងៃ)",
    "🎯 Target days": "🎯 ថ្ងៃគោលដៅ",
    "🟤 Shelf life (days)": "🟤 អាយុកាលប្រើប្រាស់ (ថ្ងៃ)",
    "Order": "លំដាប់",
    "Pcs per crate": "គ្រាប់ក្នុងមួយកេស",
    "📦 Pcs per crate": "📦 គ្រាប់ក្នុងមួយកេស",
    "Pcs / crate": "គ្រាប់ / កេស",
    "Limit": "កម្រិត",
    "Task": "ការងារ",
    "Before": "មុនម៉ោង",
    "Auto": "ស្វ័យប្រវត្តិ",
    "Who": "អ្នកណា",
    "Error": "កំហុស",
    "Where": "កន្លែង",
    "Result": "លទ្ធផល",
    "Today": "ថ្ងៃនេះ",
    "today": "ថ្ងៃនេះ",
    "tomorrow": "ថ្ងៃស្អែក",
    "never counted yet": "មិនទាន់ធ្លាប់រាប់",
    "never counted": "មិនទាន់ធ្លាប់រាប់",
    "last count": "រាប់ចុងក្រោយ",
    "Last count": "រាប់ចុងក្រោយ",
    "Now (app)": "ឥឡូវ (កម្មវិធី)",
    "new production comes here": "ការផលិតថ្មីចូលទីនេះ",
    "💾 Save": "💾 រក្សាទុក",
    "✅ Saved": "✅ បានរក្សាទុក",
    "✅ Saved:": "✅ បានរក្សាទុក:",
    "✅ Done": "✅ រួចរាល់",
    "↩️ Undo": "↩️ មិនធ្វើវិញ",
    "↩️ Undo last save": "↩️ លុបការរក្សាទុកចុងក្រោយ",
    "↩️ Undone:": "↩️ បានលុបវិញ:",
    "Not undone:": "មិនបានលុបវិញ:",
    "Not saved:": "មិនបានរក្សាទុក:",
    "⚠️ Not saved:": "⚠️ មិនបានរក្សាទុក:",
    "Not changed:": "មិនបានផ្លាស់ប្តូរ:",
    "Not deleted:": "មិនបានលុប:",
    "Not created:": "មិនបានបង្កើត:",
    "📝 Not saved yet": "📝 មិនទាន់រក្សាទុក",
    "not saved yet": "មិនទាន់រក្សាទុក",
    "⬅️ Back": "⬅️ ថយក្រោយ",
    "➡️ Go to": "➡️ ទៅកាន់",
    "From": "ពី",
    "To": "ដល់",
    "Choose": "ជ្រើសរើស",
    "Type numbers only.": "វាយតែលេខប៉ុណ្ណោះ។",
    "Type at least one number to save.": "វាយយ៉ាងហោចណាស់លេខមួយដើម្បីរក្សាទុក។",
    "🕘 Your last save": "🕘 ការរក្សាទុកចុងក្រោយរបស់អ្នក",
    "— saved something wrong? You can undo it for": "— រក្សាទុកខុស? អ្នកអាចលុបវិញបានក្នុងរយៈពេល",
    "minutes.": "នាទី។",
    "Someone else is saving the same file right now. Please press Save again.": "មានអ្នកផ្សេងកំពុងរក្សាទុកឯកសារនេះ។ សូមចុចរក្សាទុកម្តងទៀត។",
    "No connection to Dropbox — check the internet and press Save again. Your numbers are still on the screen.":
        "មិនអាចភ្ជាប់ Dropbox — ពិនិត្យអ៊ីនធឺណិត ហើយចុចរក្សាទុកម្តងទៀត។ លេខរបស់អ្នកនៅលើអេក្រង់នៅឡើយ។",
    "The file was being saved by someone else. Try again.": "មានអ្នកផ្សេងកំពុងរក្សាទុកឯកសារ។ សូមព្យាយាមម្តងទៀត។",
    "⚠️ This part could not load:": "⚠️ ផ្នែកនេះមិនអាចបើកបាន:",
    ". The 🤖 bot already tried to repair it and kept the error for Admin. Your saved data is safe — try again in a minute.":
        "។ 🤖 បូតបានព្យាយាមជួសជុល ហើយរក្សាកំហុសទុកឲ្យ Admin។ ទិន្នន័យរបស់អ្នកមានសុវត្ថិភាព — សូមព្យាយាមម្តងទៀតក្នុងមួយនាទី។",
    "🤖 A problem was found — the bot repaired the data and is trying again…": "🤖 រកឃើញបញ្ហា — បូតបានជួសជុលទិន្នន័យ ហើយកំពុងព្យាយាមម្តងទៀត…",

    # --- live stock ------------------------------------------------------------------------------
    "📦 Total stock": "📦 ស្តុកសរុប",
    "🏭 Produced today": "🏭 ផលិតថ្ងៃនេះ",
    "pcs logged": "គ្រាប់ បានកត់ត្រា",
    "🧾 Sold today": "🧾 លក់ថ្ងៃនេះ",
    "pcs in the sale journal": "គ្រាប់ ក្នុងបញ្ជីលក់",
    "🔴 Buns too low": "🔴 នំតិចពេក",
    "🟤 Old pcs": "🟤 គ្រាប់ចាស់",
    "older than shelf life": "ហួសអាយុកាលប្រើប្រាស់",
    "% of the limit) · sales speed from the last": "% នៃកម្រិត) · ល្បឿនលក់ពី",
    "selling days · updated": "ថ្ងៃលក់ចុងក្រោយ · បច្ចុប្បន្នភាព",
    "In stock (pcs)": "ក្នុងស្តុក (គ្រាប់)",
    "Sold / day": "លក់ / ថ្ងៃ",
    "Days of stock": "ស្តុកគ្រប់ (ថ្ងៃ)",
    "Sold today": "លក់ថ្ងៃនេះ",
    "🔴 Out of stock": "🔴 អស់ស្តុក",
    "⚪ No recent sales": "⚪ មិនមានការលក់ថ្មីៗ",
    "🔴 Too low": "🔴 តិចពេក",
    "🟡 A bit low": "🟡 តិចបន្តិច",
    "🟠 Too much": "🟠 ច្រើនពេក",
    "🟢 OK": "🟢 ល្អ",
    "🗓️ Stock by production date (oldest at the top = sell first)": "🗓️ ស្តុកតាមថ្ងៃផលិត (ចាស់នៅលើ = លក់មុន)",
    "📈 Total stock per day (last 21 days)": "📈 ស្តុកសរុបប្រចាំថ្ងៃ (21 ថ្ងៃចុងក្រោយ)",
    ") — calculated now": ") — គណនាឥឡូវនេះ",
    ") — all 3 stocks": ") — ស្តុកទាំង 3",
    "Older than": "ចាស់ជាង",
    "days = check / sell first.": "ថ្ងៃ = ពិនិត្យ / លក់មុន។",
    "No stock yet. Start with the evening stock count in 📦 Stock count.": "មិនទាន់មានស្តុក។ ចាប់ផ្តើមដោយរាប់ស្តុកពេលល្ងាចក្នុង 📦 រាប់ស្តុក។",
    "No stock count yet for:": "មិនទាន់រាប់ស្តុកសម្រាប់:",
    "No stock count yet for": "មិនទាន់រាប់ស្តុកសម្រាប់",
    ". Enter one in": "។ សូមបញ្ចូលក្នុង",
    "— until then their stock only counts production logged here.": "— រហូតដល់ពេលនោះ ស្តុកគិតតែការផលិតដែលកត់ត្រានៅទីនេះ។",
    "pcs is above the": "គ្រាប់ លើស",
    "limit": "កម្រិត",
    "produce less / sell first": "ផលិតតិចជាងមុន / លក់ជាមុន",
    "pcs is close to the": "គ្រាប់ ជិតដល់",
    "pcs older than": "គ្រាប់ ចាស់ជាង",
    "days — sell first / check quality": "ថ្ងៃ — លក់មុន / ពិនិត្យគុណភាព",
    ": the journal sold": ": បញ្ជីលក់បានលក់",
    "pcs more than the stock (production not logged, or the stock count is missing)":
        "គ្រាប់ ច្រើនជាងស្តុក (មិនបានកត់ត្រាការផលិត ឬខ្វះការរាប់ស្តុក)",
    ": out of stock": ": អស់ស្តុក",
    "Room for new production": "កន្លែងសម្រាប់ការផលិតថ្មី",
    "free stacks": "ជង់ទំនេរ",
    "needed every day:": "ត្រូវការរៀងរាល់ថ្ងៃ:",
    "for new production (green 📥 places at the back of each bun's lanes) — needed every day:":
        "សម្រាប់ការផលិតថ្មី (កន្លែងបៃតង 📥 នៅខាងក្រោយជួររបស់នំនីមួយៗ) — ត្រូវការរៀងរាល់ថ្ងៃ:",
    "— ⚠️ not enough. This evening's 🚚 move list (📦 Stock count) frees space by moving old crates to the cooling room.":
        "— ⚠️ មិនគ្រប់។ បញ្ជី 🚚 ផ្ទេរល្ងាចនេះ (📦 រាប់ស្តុក) នឹងទុកកន្លែងទំនេរ ដោយផ្ទេរកេសចាស់ទៅទូរត្រជាក់។",
    "— ⚠️ not enough for:": "— ⚠️ មិនគ្រប់សម្រាប់:",
    "stacks — use this evening's 🚚 move list.": "ជង់ — សូមប្រើបញ្ជី 🚚 ផ្ទេរល្ងាចនេះ។",
    "stacks for": "ជង់សម្រាប់",
    "% full": "% ពេញ",

    # --- production ------------------------------------------------------------------------------
    "📅 Production date": "📅 ថ្ងៃផលិត",
    "— pcs (numbers only)": "— គ្រាប់ (តែលេខ)",
    "Type the pcs produced for each bun. Empty = 0.": "វាយចំនួនគ្រាប់ដែលផលិតសម្រាប់នំនីមួយៗ។ ទទេ = 0។",
    "Type the pcs produced like in your Excel sheet —": "វាយចំនួនគ្រាប់ដែលផលិតដូចក្នុង Excel —",
    "one row per production date": "មួយជួរ សម្រាប់មួយថ្ងៃផលិត",
    "(add a row with ＋ for another day). Empty = 0.": "(បន្ថែមជួរដោយ ＋ សម្រាប់ថ្ងៃផ្សេង)។ ទទេ = 0។",
    "👷 Produced by": "👷 ផលិតដោយ",
    "Everyone who made these buns (Admin adds names in ⚙️ Settings).": "អ្នកទាំងអស់ដែលធ្វើនំទាំងនេះ (Admin បន្ថែមឈ្មោះក្នុង ⚙️ ការកំណត់)។",
    "Choose who produced these buns (👷 Produced by).": "សូមជ្រើសអ្នកដែលផលិតនំទាំងនេះ (👷 ផលិតដោយ)។",
    "💾 Save production": "💾 រក្សាទុកការផលិត",
    "👁️ View only — ask Admin for edit access to log production.": "👁️ មើលតែប៉ុណ្ណោះ — សុំ Admin សិទ្ធិកែ ដើម្បីកត់ត្រាការផលិត។",
    "📋 Production logged": "📋 ការផលិតដែលបានកត់ត្រា",
    "Nothing logged in these dates.": "មិនមានការកត់ត្រាក្នុងថ្ងៃទាំងនេះ។",
    "✏️ Fix or delete a saved line": "✏️ កែ ឬលុបជួរដែលបានរក្សាទុក",
    "lines)": "ជួរ)",
    "💾 Save fixes": "💾 រក្សាទុកការកែ",
    "✅ Fixes saved": "✅ បានរក្សាទុកការកែ",
    "Only your own lines (Admin: all) can be changed here.": "អ្នកអាចកែបានតែជួររបស់អ្នក (Admin: ទាំងអស់)។",
    "📝 Your numbers from before are still here — they are NOT saved yet.": "📝 លេខរបស់អ្នកពីមុននៅទីនេះនៅឡើយ — មិនទាន់បានរក្សាទុកទេ។",
    "— saving now adds these pcs. If it is the same production, do not save again.":
        "— ការរក្សាទុកឥឡូវនឹងបន្ថែមគ្រាប់ទាំងនេះ។ បើជាការផលិតដដែល សូមកុំរក្សាទុកម្តងទៀត។",
    "— saving now": "— ការរក្សាទុកឥឡូវ",
    "adds": "បន្ថែម",
    "these pcs. If it is the same production, do not save again.": "គ្រាប់ទាំងនេះ។ បើជាការផលិតដដែល សូមកុំរក្សាទុកម្តងទៀត។",
    "ℹ️ Already saved before:": "ℹ️ បានរក្សាទុករួចពីមុន:",
    "✅ This was already saved a moment ago — it is not saved twice.": "✅ នេះបានរក្សាទុករួចមុននេះបន្តិច — មិនរក្សាទុកពីរដងទេ។",
    "✅ Already saved a moment ago — it is not saved twice.": "✅ បានរក្សាទុករួចមុននេះបន្តិច — មិនរក្សាទុកពីរដងទេ។",
    "✅ Already saved a moment ago — not saved twice.": "✅ បានរក្សាទុករួចមុននេះបន្តិច — មិនរក្សាទុកពីរដងទេ។",
    "Right pcs": "គ្រាប់ត្រឹមត្រូវ",
    "Right bun": "នំត្រឹមត្រូវ",
    "Right date": "ថ្ងៃត្រឹមត្រូវ",
    "Choose the bun": "ជ្រើសនំ",

    # --- stock count + moves ----------------------------------------------------------------------
    "📦 Evening stock count": "📦 រាប់ស្តុកពេលល្ងាច",
    "Count date (stock at the END of this day)": "ថ្ងៃរាប់ (ស្តុកនៅចុងថ្ងៃនេះ)",
    "Evening: first": "ពេលល្ងាច: ដំបូង",
    "what the cooling room needs for tomorrow, then count each stock.": "អ្វីដែលទូរត្រជាក់ត្រូវការសម្រាប់ថ្ងៃស្អែក រួចរាប់ស្តុកនីមួយៗ។",
    "Each stock is saved by itself": "ស្តុកនីមួយៗរក្សាទុកដាច់ដោយឡែក",
    "— count and save one, the others keep their last count. The sheets start with what the app expects: only change what is different.":
        "— រាប់ ហើយរក្សាទុកមួយ ស្តុកផ្សេងទៀតរក្សាការរាប់ចុងក្រោយ។ តារាងចាប់ផ្តើមពីអ្វីដែលកម្មវិធីរំពឹង: កែតែអ្វីដែលខុសប៉ុណ្ណោះ។",
    "Start the sheets from": "ចាប់ផ្តើមតារាងពី",
    "🧮 What the app expects (recommended)": "🧮 អ្វីដែលកម្មវិធីរំពឹង (ណែនាំ)",
    "⬜ Empty sheets": "⬜ តារាងទទេ",
    "🚚 Move frozen → cooling": "🚚 ផ្ទេរពីទូរកក → ទូរត្រជាក់",
    "📊 All stock": "📊 ស្តុកទាំងអស់",
    "Part": "ផ្នែក",
    "✅ Counted · next ➡️": "✅ បានរាប់ · បន្ទាប់ ➡️",
    "✅ Counted (last date)": "✅ បានរាប់ (ថ្ងៃចុងក្រោយ)",
    "— type what you see. Empty = 0.": "— វាយអ្វីដែលអ្នកឃើញ។ ទទេ = 0។",
    "➕ Add a production date that is missing": "➕ បន្ថែមថ្ងៃផលិតដែលខ្វះ",
    "➕ Add this date": "➕ បន្ថែមថ្ងៃនេះ",
    "🎉 All dates counted — check the total and press 💾 Save below.": "🎉 រាប់គ្រប់ថ្ងៃហើយ — ពិនិត្យសរុប ហើយចុច 💾 រក្សាទុក ខាងក្រោម។",
    "🔍 Check: counted vs what the app expected in": "🔍 ពិនិត្យ: បានរាប់ ធៀបនឹងអ្វីដែលកម្មវិធីរំពឹងក្នុង",
    "👁️ View only — ask Admin for edit access to save a count.": "👁️ មើលតែប៉ុណ្ណោះ — សុំ Admin សិទ្ធិកែ ដើម្បីរក្សាទុកការរាប់។",
    "was already counted for": "បានរាប់រួចសម្រាប់",
    ". Saving again replaces that count.": "។ ការរក្សាទុកម្តងទៀតនឹងជំនួសការរាប់នោះ។",
    "replaces": "ជំនួស",
    ". Check once more (a missing date? a typo? buns moved without 🚚?).": "។ ពិនិត្យម្តងទៀត (ខ្វះថ្ងៃ? វាយខុស? ផ្ទេរនំដោយគ្មាន 🚚?)។",
    "⚠️ Big difference from what the app expected:": "⚠️ ខុសគ្នាច្រើនពីអ្វីដែលកម្មវិធីរំពឹង:",
    "✔️ I checked these numbers — they are right": "✔️ ខ្ញុំបានពិនិត្យលេខទាំងនេះ — ត្រឹមត្រូវ",
    "📥 Count sheets for printing (Excel, your layout)": "📥 តារាងរាប់សម្រាប់បោះពុម្ព (Excel តាមទម្រង់របស់អ្នក)",
    "📝 Your count from before is still here — it is NOT saved yet.": "📝 ការរាប់របស់អ្នកពីមុននៅទីនេះនៅឡើយ — មិនទាន់បានរក្សាទុកទេ។",
    "production dates counted in": "ថ្ងៃផលិតបានរាប់ក្នុង",
    "🚚 Moves are made for today's evening — choose today's date above.": "🚚 ការផ្ទេរធ្វើសម្រាប់ល្ងាចថ្ងៃនេះ — សូមជ្រើសថ្ងៃនេះខាងលើ។",
    "✅ Already moved today:": "✅ បានផ្ទេររួចថ្ងៃនេះ:",
    "pcs — the list below already counts them.": "គ្រាប់ — បញ្ជីខាងក្រោមបានគិតរួចហើយ។",
    "Move from": "ផ្ទេរពី",
    "— the app suggests it by itself: enough for": "— កម្មវិធីណែនាំដោយខ្លួនឯង: គ្រប់សម្រាប់",
    "of sales (tomorrow": "នៃការលក់ (ថ្ងៃស្អែក",
    "whole crates, oldest production date first": "កេសពេញ ថ្ងៃផលិតចាស់ជាងគេមុន",
    "✅ We moved these — save": "✅ យើងបានផ្ទេររួច — រក្សាទុក",
    "✅ Nothing to move — the cooling room already has enough for tomorrow.": "✅ គ្មានអ្វីត្រូវផ្ទេរ — ទូរត្រជាក់មានគ្រប់សម្រាប់ថ្ងៃស្អែកហើយ។",
    "❄️ Cooling now (pcs)": "❄️ ទូរត្រជាក់ឥឡូវ (គ្រាប់)",
    "Needed (pcs)": "ត្រូវការ (គ្រាប់)",
    "🧊 Frozen now (pcs)": "🧊 ទូរកកឥឡូវ (គ្រាប់)",
    "🚚 Move (crates)": "🚚 ផ្ទេរ (កេស)",
    "Take these dates": "យកថ្ងៃទាំងនេះ",
    "Change it if you moved a different number of crates": "កែវា បើអ្នកបានផ្ទេរចំនួនកេសខុសពីនេះ",
    "= pcs (suggested)": "= គ្រាប់ (ណែនាំ)",
    "🚚 Move": "🚚 ផ្ទេរ",
    "crates =": "កេស =",
    "🚚 Step by step — take from the FRONT, push in at the BACK": "🚚 មួយជំហានម្តងៗ — យកពីខាងមុខ រុញចូលនៅខាងក្រោយ",
    ": take from the front of": ": យកពីខាងមុខនៃ",
    "push in at the back of": "រុញចូលនៅខាងក្រោយនៃ",
    "⚠️ these (": "⚠️ កេសទាំងនេះ (",
    ") are OLDER than the": ") ចាស់ជាង",
    "crates already in": "កេសដែលមានរួចក្នុង",
    ": take that lane out, put these in where 🆕 shows (oldest at the FRONT), push the rest back in behind":
        ": យកជួរនោះចេញ ដាក់កេសទាំងនេះនៅកន្លែង 🆕 (ចាស់នៅខាងមុខ) ហើយរុញកេសផ្សេងចូលវិញនៅខាងក្រោយ",
    "L = lane, counted from the left of the room (the lane names are on the maps). Do one bun at a time; never put a bun in another bun's lane.":
        "L = ជួរ រាប់ពីខាងឆ្វេងនៃបន្ទប់ (ឈ្មោះជួរមាននៅលើផែនទី)។ ធ្វើម្តងមួយនំ; កុំដាក់នំក្នុងជួររបស់នំផ្សេង។",
    "🔄 Today the frozen room has": "🔄 ថ្ងៃនេះទូរកកមាននំ",
    "older": "ចាស់ជាង",
    "bread than the cooling room for:": "ទូរត្រជាក់ សម្រាប់:",
    ". FIFO = oldest out first, so these lanes must be re-stacked once (oldest at the front). When the old stock is used up, the moved crates are always the newest and just go in at the back.":
        "។ FIFO = ចាស់ចេញមុន ដូច្នេះជួរទាំងនេះត្រូវរៀបម្តងទៀតម្តង (ចាស់នៅខាងមុខ)។ ពេលស្តុកចាស់អស់ កេសដែលផ្ទេរនឹងថ្មីជាងគេជានិច្ច ហើយគ្រាន់តែដាក់នៅខាងក្រោយ។",
    "now — where to take the crates": "ឥឡូវ — យកកេសពីណា",
    "🚚 = take this many crates": "🚚 = យកកេសចំនួននេះ",
    "— the oldest, at the FRONT of the bun's lanes.": "— ចាស់ជាងគេ នៅខាងមុខជួររបស់នំ។",
    "after the move — where to put the crates": "ក្រោយការផ្ទេរ — ដាក់កេសនៅណា",
    "🆕 = put the moved crates here": "🆕 = ដាក់កេសដែលផ្ទេរនៅទីនេះ",
    "(normally at the BACK of the bun's own lane; 🔄 = older crates: at the front). The oldest crates are always at the":
        "(ជាធម្មតានៅខាងក្រោយជួររបស់នំនោះ; 🔄 = កេសចាស់ជាង: នៅខាងមុខ)។ កេសចាស់ជាងគេតែងតែនៅ",
    "(⭐ = take first). Every bun always has the same lane — the name is under each column. Places used:":
        "(⭐ = យកមុន)។ នំនីមួយៗមានជួរដដែលជានិច្ច — ឈ្មោះនៅក្រោមជួរឈរនីមួយៗ។ កន្លែងបានប្រើ:",
    "⬇️ This map (Excel)": "⬇️ ផែនទីនេះ (Excel)",
    "⚠️ Their cooling lanes are full — the list was made smaller so the crates fit:": "⚠️ ជួរក្នុងទូរត្រជាក់ពេញ — បញ្ជីត្រូវបានបន្ថយ ដើម្បីឲ្យកេសដាក់ចុះ:",
    "— only what the frozen room has is counted. Count the frozen room?": "— គិតតែអ្វីដែលទូរកកមាន។ រាប់ទូរកកឬ?",
    "⚠️ More crates than the frozen room has:": "⚠️ កេសច្រើនជាងអ្វីដែលទូរកកមាន:",
    "— move fewer crates.": "— ផ្ទេរកេសតិចជាងនេះ។",
    "⚠️ No place for:": "⚠️ គ្មានកន្លែងសម្រាប់:",
    "🚚 includes extra old crates moved only to make room for tomorrow's production:": "🚚 រួមទាំងកេសចាស់បន្ថែម ដែលផ្ទេរដើម្បីទុកកន្លែងសម្រាប់ការផលិតថ្ងៃស្អែក:",
    "📥 After this move the frozen room has": "📥 ក្រោយការផ្ទេរនេះ ទូរកកមាន",
    "for tomorrow's production — needed:": "សម្រាប់ការផលិតថ្ងៃស្អែក — ត្រូវការ:",
    "⚠️ Not enough even after moving for:": "⚠️ នៅតែមិនគ្រប់ក្រោយការផ្ទេរ សម្រាប់:",
    "stacks — their cooling lanes are full too: produce less of these tomorrow, or sell / move stock elsewhere.":
        "ជង់ — ជួរក្នុងទូរត្រជាក់ក៏ពេញដែរ: ផលិតនំទាំងនេះតិចជាងមុនថ្ងៃស្អែក ឬលក់ / ផ្ទេរស្តុកទៅកន្លែងផ្សេង។",
    "➕➖ Adjustment": "➕➖ កែតម្រូវ",
    "— buns that leave or enter stock without a sale invoice (damaged, samples, staff meals, returned...).":
        "— នំដែលចេញ ឬចូលស្តុក ដោយគ្មានវិក្កយបត្រលក់ (ខូច គំរូ អាហារបុគ្គលិក ត្រឡប់មកវិញ...)។",
    "➖ Remove": "➖ ដកចេញ",
    "➕ Add": "➕ បន្ថែម",
    "Batch production date (optional)": "ថ្ងៃផលិតនៃឡូតិ៍ (មិនចាំបាច់)",
    "Damaged / broken": "ខូច / បែក",
    "Expired / old": "ផុតកំណត់ / ចាស់",
    "Sample / FOC not in journal": "គំរូ / FOC មិនមានក្នុងបញ្ជីលក់",
    "Staff meal": "អាហារបុគ្គលិក",
    "Returned by customer": "អតិថិជនប្រគល់មកវិញ",
    "Other": "ផ្សេងៗ",
    "💾 Save adjustment": "💾 រក្សាទុកការកែតម្រូវ",
    "✅ Adjustment saved:": "✅ បានរក្សាទុកការកែតម្រូវ:",
    "✅ This adjustment was already saved a moment ago — it is not saved twice.": "✅ ការកែតម្រូវនេះបានរក្សាទុករួចមុននេះបន្តិច — មិនរក្សាទុកពីរដងទេ។",
    "🗑️ Delete a wrong adjustment": "🗑️ លុបការកែតម្រូវខុស",
    "(your own lines)": "(ជួររបស់អ្នក)",
    "🗑️ Delete": "🗑️ លុប",
    "🗑️ Deleted": "🗑️ បានលុប",
    "adjustment line(s)": "ជួរកែតម្រូវ",
    "line(s)": "ជួរ",
    "Auto (cooling first)": "ស្វ័យប្រវត្តិ (ទូរត្រជាក់មុន)",

    # --- plan ------------------------------------------------------------------------------------
    "📅 Next week production plan": "📅 ផែនការផលិតសប្តាហ៍ក្រោយ",
    "Plan from": "ផែនការពី",
    "Plan until": "ផែនការដល់",
    "The plan starts from the stock you have now. Plan from tomorrow so the days before next week are counted too.":
        "ផែនការចាប់ផ្តើមពីស្តុកដែលអ្នកមានឥឡូវ។ សូមធ្វើផែនការពីថ្ងៃស្អែក ដើម្បីគិតថ្ងៃមុនសប្តាហ៍ក្រោយផងដែរ។",
    "📥 Download the plan (Excel)": "📥 ទាញយកផែនការ (Excel)",
    "Stock end of day": "ស្តុកចុងថ្ងៃ",
    "📈 Expected total stock per day": "📈 ស្តុកសរុបរំពឹងទុកប្រចាំថ្ងៃ",
    "🏭 To produce": "🏭 ត្រូវផលិត",
    "🧾 Expected sales": "🧾 ការលក់រំពឹងទុក",
    "pcs (same weekday average)": "គ្រាប់ (មធ្យមថ្ងៃដូចគ្នាក្នុងសប្តាហ៍)",
    "📦 Highest total stock": "📦 ស្តុកសរុបខ្ពស់បំផុត",
    "📦 Stock now": "📦 ស្តុកឥឡូវ",
    "✅ Limit kept": "✅ មិនលើសកម្រិត",
    "Stock now": "ស្តុកឥឡូវ",
    "Stock at the end": "ស្តុកនៅចុងបញ្ចប់",
    "Days at the end": "ថ្ងៃនៅចុងបញ្ចប់",

    # --- 3D rooms --------------------------------------------------------------------------------
    "🧊 3D FIFO rooms — cooling + freezer": "🧊 បន្ទប់ FIFO 3D — ទូរត្រជាក់ + ទូរកក",
    "Days to replay": "ចំនួនថ្ងៃដើម្បីមើលឡើងវិញ",
    "📋 Room sheet — your Excel layout (today)": "📋 តារាងបន្ទប់ — ទម្រង់ Excel របស់អ្នក (ថ្ងៃនេះ)",
    "Room sheet": "តារាងបន្ទប់",
    "sheet (Excel)": "តារាង (Excel)",
    "📤 Tomorrow's take-out": "📤 យកចេញសម្រាប់ថ្ងៃស្អែក",
    "Expected sales for tomorrow → the crates to take,": "ការលក់រំពឹងទុកថ្ងៃស្អែក → កេសដែលត្រូវយក,",
    "(L = lane from the left · front = at the door). '(of 15)' = take only part of that stack; the rest stays at the front.":
        "(L = ជួរពីខាងឆ្វេង · ខាងមុខ = ជិតទ្វារ)។ '(of 15)' = យកតែមួយផ្នែកនៃជង់នោះ; ដែលនៅសល់ទុកនៅខាងមុខ។",
    "📤 Take-out order": "📤 លំដាប់យកចេញ",
    "For each bun: take the stacks in this order —": "សម្រាប់នំនីមួយៗ: យកជង់តាមលំដាប់នេះ —",
    "(L = lane, counted from the left; front = the stack at the door). 1 stack = 1 bun + 1 production date.":
        "(L = ជួរ រាប់ពីខាងឆ្វេង; ខាងមុខ = ជង់ជិតទ្វារ)។ 1 ជង់ = 1 នំ + 1 ថ្ងៃផលិត។",
    "Tomorrow (pcs)": "ថ្ងៃស្អែក (គ្រាប់)",
    "Take in this order (lane · place · date × crates)": "យកតាមលំដាប់នេះ (ជួរ · កន្លែង · ថ្ងៃ × កេស)",
    "⚠️ Short": "⚠️ ខ្វះ",
    "— take from the frozen room": "— យកពីទូរកក",
    "No sales expected tomorrow.": "មិនរំពឹងការលក់ថ្ងៃស្អែកទេ។",
    "No stock in this room today.": "គ្មានស្តុកក្នុងបន្ទប់នេះថ្ងៃនេះ។",
    "① first": "① មុនគេ",
    "② then": "② បន្ទាប់",
    "③ then": "③ បន្ទាប់",
    "④ then": "④ បន្ទាប់",
    "first)": "មុន)",
    "(move": "(ផ្ទេរ",
    "stack of": "ជង់នៃ",
    "⚠️ not its lane": "⚠️ មិនមែនជួររបស់វា",
    "⚠️ other place": "⚠️ កន្លែងផ្សេង",
    "⚠️ no lane": "⚠️ គ្មានជួរ",
    "— spare": "— ទំនេរ",
    "FIFO lanes:": "ជួរ FIFO:",
    "1 lane = 1 bun, always the same lane": "1 ជួរ = 1 នំ ជួរដដែលជានិច្ច",
    "(name under each column). Take only from the": "(ឈ្មោះនៅក្រោមជួរឈរនីមួយៗ)។ យកតែពី",
    "of the lane (⭐ = oldest, take first); push new crates in at the": "នៃជួរ (⭐ = ចាស់ជាងគេ យកមុន); រុញកេសថ្មីចូលនៅ",
    "of the bun's own lane — never in front of older crates, never in another bun's lane. A bun with 2+ lanes: every lane has its oldest at the front. 🧺 = a lane shared by 2–3 small buns: still 1 stack = 1 bun. Use the Day slider / ▶ Play to see how it moved.":
        "នៃជួររបស់នំនោះ — កុំដាក់នៅមុខកេសចាស់ កុំដាក់ក្នុងជួរនំផ្សេង។ នំដែលមាន 2+ ជួរ: ជួរនីមួយៗមានកេសចាស់នៅខាងមុខ។ 🧺 = ជួររួមសម្រាប់នំតូចៗ 2–3: នៅតែ 1 ជង់ = 1 នំ។ ប្រើរំកិលថ្ងៃ / ▶ លេង ដើម្បីមើលការផ្លាស់ប្តូរ។",
    "Which room: ❄️ cooling stock → the first room · 🧊 frozen stock → the second room · 🛒 AEON stock → its own line on the right of the frozen room (from the evening counts and 🚚 moves).":
        "បន្ទប់ណា: ❄️ ស្តុកត្រជាក់ → បន្ទប់ទីមួយ · 🧊 ស្តុកកក → បន្ទប់ទីពីរ · 🛒 ស្តុក AEON → ជួររបស់វាខាងស្តាំទូរកក (ពីការរាប់ពេលល្ងាច និង 🚚 ការផ្ទេរ)។",
    "🔒 The lanes are set": "🔒 ជួរត្រូវបានកំណត់",
    "automatically from sales": "ដោយស្វ័យប្រវត្តិតាមការលក់",
    "right now. Admin: open 📐 Adjust sizes →": "ឥឡូវនេះ។ Admin: បើក 📐 កែទំហំ →",
    "and press 💾 Save, so every bun keeps the": "ហើយចុច 💾 រក្សាទុក ដើម្បីឲ្យនំនីមួយៗមាន",
    "same lane every day": "ជួរដដែលរៀងរាល់ថ្ងៃ",
    "Their lanes in": "ជួររបស់ពួកវាក្នុង",
    "are full": "ពេញ",
    "→ the newest crates are shown in": "→ កេសថ្មីជាងគេបង្ហាញក្នុង",
    "crates). The oldest crates stay at the front of each lane.": "កេស)។ កេសចាស់ជាងគេនៅខាងមុខជួរនីមួយៗ។",
    "⚠️ No place today for these crates —": "⚠️ គ្មានកន្លែងថ្ងៃនេះសម្រាប់កេសទាំងនេះ —",
    ". Move a bun to the other room": "។ ផ្ទេរនំទៅបន្ទប់ផ្សេង",
    ", or adjust the room grid (📐).": " ឬកែក្រឡាបន្ទប់ (📐)។",
    "📐 Adjust sizes — room grid, doors, crate, room / order / pcs per crate of each bun (Admin only)":
        "📐 កែទំហំ — ក្រឡាបន្ទប់ ទ្វារ កេស បន្ទប់ / លំដាប់ / គ្រាប់ក្នុងមួយកេសរបស់នំនីមួយៗ (Admin តែប៉ុណ្ណោះ)",
    "💾 Save sizes": "💾 រក្សាទុកទំហំ",
    "✅ Sizes saved — the 3D view uses them now.": "✅ បានរក្សាទុកទំហំ — ទិដ្ឋភាព 3D ប្រើវាឥឡូវនេះ។",
    "🧊 Rooms and crates (for 🧊 3D rooms)": "🧊 បន្ទប់ និងកេស (សម្រាប់ 🧊 បន្ទប់ 3D)",
    "A room = a grid of stack places like your sheet. Across = columns, Deep = rows (row 1 = back, at the IN side). Blocked = places with no stock, e.g.":
        "បន្ទប់ = ក្រឡាកន្លែងជង់ ដូចតារាងរបស់អ្នក។ ទទឹង = ជួរឈរ, ជម្រៅ = ជួរដេក (ជួរ 1 = ខាងក្រោយ ខាងទ្វារចូល)។ បិទ = កន្លែងគ្មានស្តុក ឧ.",
    "(row:columns=name).": "(ជួរ:ជួរឈរ=ឈ្មោះ)។",
    "Stacks across": "ជង់តាមទទឹង",
    "Stacks deep": "ជង់តាមជម្រៅ",
    "Crates high": "កេសតាមកម្ពស់",
    "📏 Crates high": "📏 កេសតាមកម្ពស់",
    "How many crates in one stack: 12 or 15": "កេសប៉ុន្មានក្នុងមួយជង់: 12 ឬ 15",
    "🛒 AEON line high": "🛒 កម្ពស់ជួរ AEON",
    "Crates in one stack in the AEON line: 12 or 15": "កេសក្នុងមួយជង់នៃជួរ AEON: 12 ឬ 15",
    "Height (m)": "កម្ពស់ (m)",
    "Empty at back (m)": "ទុកទំនេរខាងក្រោយ (m)",
    "Kept free at the back (row 1 side), e.g. 1.6 m for raw material": "ទុកទំនេរនៅខាងក្រោយ (ខាងជួរ 1) ឧ. 1.6 m សម្រាប់វត្ថុធាតុដើម",
    "🛒 AEON line places": "🛒 កន្លែងជួរ AEON",
    "Right-hand line for the AEON stock with the crates turned (e.g. 11). 0 = no AEON line in this room":
        "ជួរខាងស្តាំសម្រាប់ស្តុក AEON ដោយបង្វិលកេស (ឧ. 11)។ 0 = គ្មានជួរ AEON ក្នុងបន្ទប់នេះ",
    "🚶 Walkway before AEON (m)": "🚶 ផ្លូវដើរមុនជួរ AEON (m)",
    "Free path between the frozen lanes and the AEON line (whole stack columns, ~0.49 m each). 0 = none":
        "ផ្លូវទំនេររវាងជួរនំកក និងជួរ AEON (គិតជាជួរឈរពេញ ~0.49 m ម្តង)។ 0 = គ្មាន",
    "Blocked places": "កន្លែងបិទ",
    "🟢 Door IN": "🟢 ទ្វារចូល",
    "🟠 Door OUT": "🟠 ទ្វារចេញ",
    "↔️ Order (1 = first column)": "↔️ លំដាប់ (1 = ជួរឈរទីមួយ)",
    "Crate W (cm)": "កេស ទទឹង (cm)",
    "Crate L (cm)": "កេស បណ្តោយ (cm)",
    "Crate H (cm)": "កេស កម្ពស់ (cm)",
    "Space:": "ទំហំ:",
    "m before the AEON line)": "m មុនជួរ AEON)",
    "m kept empty)": "m ទុកទំនេរ)",
    "Lanes — 1 lane (column) = 1 bun, the same every day": "ជួរ — 1 ជួរ (ជួរឈរ) = 1 នំ ដដែលរៀងរាល់ថ្ងៃ",
    "Staff take only from the FRONT of a lane and push new crates in at the BACK. Type the bun of each lane: one code (e.g.":
        "បុគ្គលិកយកតែពីខាងមុខជួរ ហើយរុញកេសថ្មីចូលនៅខាងក្រោយ។ វាយនំនៃជួរនីមួយៗ: កូដមួយ (ឧ.",
    "; a big seller can have 2–3 lanes side by side), or small buns sharing one 🧺 lane joined with + (e.g.":
        "; នំលក់ច្រើនអាចមាន 2–3 ជួរជាប់គ្នា) ឬនំតូចៗចែករំលែកជួរ 🧺 មួយ ភ្ជាប់ដោយ + (ឧ.",
    "), or empty = spare. Press 💾 Save to fix the lanes.": ") ឬទទេ = ទំនេរ។ ចុច 💾 រក្សាទុក ដើម្បីកំណត់ជួរ។",
    "↺ Lanes automatic from sales": "↺ ជួរស្វ័យប្រវត្តិតាមការលក់",
    "· ✅ saved": "· ✅ បានរក្សាទុក",
    "· ⚙️ automatic (not saved yet)": "· ⚙️ ស្វ័យប្រវត្តិ (មិនទាន់រក្សាទុក)",
    "N1 · or N22+N23 for a shared 🧺 lane · empty = spare": "N1 · ឬ N22+N23 សម្រាប់ជួររួម 🧺 · ទទេ = ទំនេរ",
    "⚠️ Unknown bun code:": "⚠️ កូដនំមិនស្គាល់:",
    "⚠️ No lane for:": "⚠️ គ្មានជួរសម្រាប់:",
    "— add them to a lane (e.g.": "— បន្ថែមពួកវាទៅក្នុងជួរ (ឧ.",
    "places used · 1 bun per place · crates turned · front (OUT) first": "កន្លែងបានប្រើ · 1 នំ ក្នុង 1 កន្លែង · កេសបង្វិល · ខាងមុខ (ចេញ) មុន",
    "🛒 AEON line (front / OUT first)": "🛒 ជួរ AEON (ខាងមុខ / ចេញមុន)",
    "📥 new": "📥 ថ្មី",
    "put": "ដាក់",
    "take": "យក",
    "of": "នៃ",

    # --- tasks / history / settings / bot ---------------------------------------------------------
    "📋 Daily tasks": "📋 ការងារប្រចាំថ្ងៃ",
    "Show only my tasks": "បង្ហាញតែការងាររបស់ខ្ញុំ",
    "🗓️ Last 7 days": "🗓️ 7 ថ្ងៃចុងក្រោយ",
    "📋 Your tasks today:": "📋 ការងាររបស់អ្នកថ្ងៃនេះ:",
    "No tasks for this day.": "គ្មានការងារសម្រាប់ថ្ងៃនេះ។",
    "Admin adds tasks in ⚙️ Settings.": "Admin បន្ថែមការងារក្នុង ⚙️ ការកំណត់។",
    "✅ Mark done": "✅ សម្គាល់ថារួចរាល់",
    "👥 Assign": "👥 ចាត់តាំង",
    "Who does it on this day": "អ្នកណាធ្វើនៅថ្ងៃនេះ",
    "⏰ before": "⏰ មុន",
    "❌ Missed": "❌ ខកខាន",
    "🔴 Late": "🔴 យឺត",
    "— done": "— រួចរាល់",
    "🕘 History — who did what": "🕘 ប្រវត្តិ — អ្នកណាធ្វើអ្វី",
    "bun, date, word…": "នំ ថ្ងៃ ពាក្យ…",
    "⬇️ Download (CSV)": "⬇️ ទាញយក (CSV)",
    "Nothing recorded yet. Every save, count, fix, sign-in and settings change will appear here.":
        "មិនទាន់មានកំណត់ត្រា។ រាល់ការរក្សាទុក ការរាប់ ការកែ ការចូល និងការកែការកំណត់ នឹងបង្ហាញនៅទីនេះ។",
    "👤 Only your own actions": "👤 តែសកម្មភាពរបស់អ្នក",
    "🎯 Stock rules": "🎯 ច្បាប់ស្តុក",
    "🧊 Rooms & crates": "🧊 បន្ទប់ និងកេស",
    "📋 Tasks & names": "📋 ការងារ និងឈ្មោះ",
    "👥 Users & access": "👥 អ្នកប្រើ និងសិទ្ធិ",
    "💾 Save settings": "💾 រក្សាទុកការកំណត់",
    "✅ Settings saved": "✅ បានរក្សាទុកការកំណត់",
    "Change anything in the tabs below, then press": "កែអ្វីក៏បានក្នុងផ្ទាំងខាងក្រោម រួចចុច",
    "— one button saves 🎯 🧊 📋 and the access table.": "— ប៊ូតុងតែមួយរក្សាទុក 🎯 🧊 📋 និងតារាងសិទ្ធិ។",
    "🎯 Stock target, production days and shelf life — per bun": "🎯 គោលដៅស្តុក ថ្ងៃផលិត និងអាយុកាលប្រើប្រាស់ — តាមនំ",
    "The table is what the app uses. Change any cell, or fill many buns at once with the buttons.":
        "តារាងនេះគឺជាអ្វីដែលកម្មវិធីប្រើ។ កែក្រឡាណាក៏បាន ឬបំពេញនំច្រើនក្នុងពេលតែមួយដោយប៊ូតុង។",
    "Target days for every bun except": "ថ្ងៃគោលដៅសម្រាប់នំទាំងអស់ លើកលែង",
    "⬇️ Apply to the table": "⬇️ អនុវត្តទៅតារាង",
    "Shelf life for every bun (days)": "អាយុកាលប្រើប្រាស់សម្រាប់នំទាំងអស់ (ថ្ងៃ)",
    "📦 Limits and planning": "📦 កម្រិត និងការធ្វើផែនការ",
    "Total stock limit (pcs)": "កម្រិតស្តុកសរុប (គ្រាប់)",
    "Sales history used (days)": "ប្រវត្តិលក់ដែលប្រើ (ថ្ងៃ)",
    "Round planned pcs up to": "បង្គត់គ្រាប់ក្នុងផែនការឡើងដល់",
    "Max production per day (0 = no limit)": "ការផលិតអតិបរមាក្នុងមួយថ្ងៃ (0 = គ្មានកម្រិត)",
    "Keep these at their target first when the total limit is reached": "រក្សានំទាំងនេះតាមគោលដៅមុន ពេលដល់កម្រិតសរុប",
    "🧊 The 3 stocks (each counted and saved by itself)": "🧊 ស្តុកទាំង 3 (រាប់ និងរក្សាទុកដាច់ដោយឡែក)",
    "❄️ Cooling room keeps (days of sales)": "❄️ ទូរត្រជាក់រក្សាទុក (ថ្ងៃនៃការលក់)",
    "The evening 🚚 move list fills the cooling room up to this many days.": "បញ្ជី 🚚 ផ្ទេរពេលល្ងាចបំពេញទូរត្រជាក់ដល់ចំនួនថ្ងៃនេះ។",
    "🧊 Frozen room keeps space for new production (pcs per day)": "🧊 ទូរកកទុកកន្លែងសម្រាប់ការផលិតថ្មី (គ្រាប់ក្នុងមួយថ្ងៃ)",
    "Checked every day; the 🚚 move list frees space when needed.": "ពិនិត្យរៀងរាល់ថ្ងៃ; បញ្ជី 🚚 ផ្ទេរនឹងទុកកន្លែងពេលចាំបាច់។",
    "New production goes to 🧊 the frozen room. Orders from customers with “AEON” in the name are taken from 🛒 the AEON stock (when it is empty: from the normal stock). Other orders: ❄️ cooling room first, then 🧊 frozen room.":
        "ការផលិតថ្មីចូល 🧊 ទូរកក។ ការបញ្ជាទិញពីអតិថិជនដែលមាន “AEON” ក្នុងឈ្មោះ យកពី 🛒 ស្តុក AEON (ពេលអស់: យកពីស្តុកធម្មតា)។ ការបញ្ជាទិញផ្សេង: ❄️ ទូរត្រជាក់មុន រួច 🧊 ទូរកក។",
    "👥 Who can use this app (Admin can always edit)": "👥 អ្នកណាអាចប្រើកម្មវិធីនេះ (Admin កែបានជានិច្ច)",
    "➕ New user": "➕ អ្នកប្រើថ្មី",
    "➕ Create user": "➕ បង្កើតអ្នកប្រើ",
    "🔢 PIN (4–6 numbers)": "🔢 PIN (លេខ 4–6 ខ្ទង់)",
    "🔑 Password (optional, 8+ letters & numbers)": "🔑 ពាក្យសម្ងាត់ (មិនចាំបាច់ 8+ អក្សរ និងលេខ)",
    "Production app access": "សិទ្ធិកម្មវិធីផលិតកម្ម",
    "New PIN (4–6 numbers)": "PIN ថ្មី (លេខ 4–6 ខ្ទង់)",
    "New password (optional)": "ពាក្យសម្ងាត់ថ្មី (មិនចាំបាច់)",
    "⚡ Make a PIN for these": "⚡ បង្កើត PIN សម្រាប់អ្នកទាំងនេះ",
    "✅ Every operation staff already has a PIN.": "✅ បុគ្គលិកប្រតិបត្តិការទាំងអស់មាន PIN រួចហើយ។",
    "⬇️ Download the PIN list (CSV)": "⬇️ ទាញយកបញ្ជី PIN (CSV)",
    "🙈 Hide the PIN list": "🙈 លាក់បញ្ជី PIN",
    "Staff name (shown in the app)": "ឈ្មោះបុគ្គលិក (បង្ហាញក្នុងកម្មវិធី)",
    "⏰ Before (HH:MM)": "⏰ មុនម៉ោង (HH:MM)",
    "👥 Who (names, ;)": "👥 អ្នកណា (ឈ្មោះ, ;)",
    "Separate with ;": "បំបែកដោយ ;",
    "🤖 Auto-fix bot": "🤖 បូតជួសជុលស្វ័យប្រវត្តិ",
    "The bot checks the data files by itself every 15 minutes and whenever a page breaks. It repairs safe problems at once (always keeping a backup first) and lists here what needs a person.":
        "បូតពិនិត្យឯកសារទិន្នន័យដោយខ្លួនឯងរៀងរាល់ 15 នាទី និងពេលទំព័រមានបញ្ហា។ វាជួសជុលបញ្ហាដែលមានសុវត្ថិភាពភ្លាមៗ (តែងរក្សាទុកច្បាប់ចម្លងមុន) ហើយរាយនៅទីនេះនូវអ្វីដែលត្រូវការមនុស្ស។",
    "🔍 Check now": "🔍 ពិនិត្យឥឡូវ",
    "Checking every file…": "កំពុងពិនិត្យឯកសារទាំងអស់…",
    "✅ Nothing needs you — all data files are fine.": "✅ គ្មានអ្វីត្រូវការអ្នក — ឯកសារទិន្នន័យទាំងអស់ល្អ។",
    "No page errors. 👍": "គ្មានកំហុសទំព័រ។ 👍",
    "🧹 Clear the error list": "🧹 សម្អាតបញ្ជីកំហុស",
    "🧹 Error list cleared.": "🧹 បានសម្អាតបញ្ជីកំហុស។",
    "⚠️ Page errors kept by the bot": "⚠️ កំហុសទំព័រដែលបូតរក្សាទុក",
    "🔧 What the bot repaired": "🔧 អ្វីដែលបូតបានជួសជុល",
    "🙋 Needs a person": "🙋 ត្រូវការមនុស្ស",
    "✅ Fix": "✅ ជួសជុល",
    "🗑️ Delete line": "🗑️ លុបជួរ",
    "Details for Admin": "ព័ត៌មានលម្អិតសម្រាប់ Admin",
    "Correct line": "ជួរត្រឹមត្រូវ",
    "data problem(s) need you": "បញ្ហាទិន្នន័យត្រូវការអ្នក",
    "page error(s) today — open": "កំហុសទំព័រថ្ងៃនេះ — បើក",
    "The first check runs within a minute of opening the app — or press 🔍 Check now.":
        "ការពិនិត្យដំបូងដំណើរការក្នុងមួយនាទីបន្ទាប់ពីបើកកម្មវិធី — ឬចុច 🔍 ពិនិត្យឥឡូវ។",

    # --- more words / sentences --------------------------------------------------------------------
    "high": "ជាន់",
    "days": "ថ្ងៃ",
    "day": "ថ្ងៃ",
    "days (target": "ថ្ងៃ (គោលដៅ",
    "Too low": "តិចពេក",
    "A bit low": "តិចបន្តិច",
    "Too much": "ច្រើនពេក",
    "Out of stock": "អស់ស្តុក",
    "No recent sales": "មិនមានការលក់ថ្មីៗ",
    "Item": "មុខទំនិញ",
    "counted": "បានរាប់",
    "last": "ចុងក្រោយ",
    "edit": "កែបាន",
    "view": "មើល",
    "hidden": "លាក់",
    "auto": "ស្វ័យប្រវត្តិ",
    "anyone": "អ្នកណាក៏បាន",
    "staff": "បុគ្គលិក",
    "viewer": "អ្នកមើល",
    "sales": "ការលក់",
    "back": "ខាងក្រោយ",
    "rows": "ជួរដេក",
    "buns": "នំ",
    "stock": "ស្តុក",
    "from": "ពី",
    "to": "ទៅ",
    "move": "ផ្ទេរ",
    "by": "ដោយ",
    "in": "ក្នុង",
    "Lanes": "ជួរ",
    "Yes": "បាទ/ចាស",
    "every day": "រៀងរាល់ថ្ងៃ",
    "Empty = 0.": "ទទេ = 0។",
    "Empty": "ទទេ",
    "Type the pcs produced for each bun.": "វាយចំនួនគ្រាប់ដែលផលិតសម្រាប់នំនីមួយៗ។",
    "actions": "សកម្មភាព",
    "move saved": "បានរក្សាទុកការផ្ទេរ",
    "count saved": "បានរក្សាទុកការរាប់",
    "evening count saved": "បានរក្សាទុកការរាប់ពេលល្ងាច",
    "production saved": "បានរក្សាទុកការផលិត",
    "production fixed": "បានកែការផលិត",
    "settings saved": "បានរក្សាទុកការកំណត់",
    "room sizes saved": "បានរក្សាទុកទំហំបន្ទប់",
    "sign in": "ចូល",
    "adjustment": "កែតម្រូវ",
    "task done": "ការងាររួចរាល់",
    "Last check": "ពិនិត្យចុងក្រោយ",
    "fixed": "បានជួសជុល",
    "need you": "ត្រូវការអ្នក",
    "✅ Done —": "✅ រួចរាល់ —",
    "line deleted.": "បានលុបជួរ។",
    "fixed.": "បានជួសជុល។",
    "⏳ To do": "⏳ ត្រូវធ្វើ",
    "due": "ត្រូវធ្វើ",
    "(before": "(មុន",
    "Operation staff": "បុគ្គលិកប្រតិបត្តិការ",
    "operation staff": "បុគ្គលិកប្រតិបត្តិការ",
    "Sales": "ផ្នែកលក់",
    "Viewer": "អ្នកមើល",
    "(role": "(តួនាទី",
    "Today ·": "ថ្ងៃនេះ ·",
    "TOTAL": "សរុប",
    "Code": "កូដ",
    "Stock end": "ស្តុកចុងថ្ងៃ",
    "Targets:": "គោលដៅ:",
    "days, others": "ថ្ងៃ, នំផ្សេង",
    "total stock": "ស្តុកសរុប",
    "made": "បានធ្វើ",
    "How it is planned: each day, produce so that the stock at the end of the day covers the next":
        "របៀបធ្វើផែនការ: រៀងរាល់ថ្ងៃ ផលិតឲ្យស្តុកនៅចុងថ្ងៃ គ្រប់សម្រាប់",
    "selling days for N1/N2 and": "ថ្ងៃលក់បន្ទាប់សម្រាប់ N1/N2 និង",
    "for the others (expected sales = the same weekday average of the last weeks). Days a bun is not produced are covered by the day before. If the total would pass":
        "សម្រាប់នំផ្សេង (ការលក់រំពឹងទុក = មធ្យមថ្ងៃដូចគ្នាក្នុងសប្តាហ៍ពីសប្តាហ៍មុនៗ)។ ថ្ងៃដែលមិនផលិតនំណាមួយ ត្រូវបានគ្របដោយថ្ងៃមុន។ បើសរុបលើស",
    "pcs, the other buns are lowered first and N1/N2 keep their days.": "គ្រាប់ នំផ្សេងត្រូវបន្ថយមុន ហើយ N1/N2 រក្សាថ្ងៃរបស់វា។",
    "ℹ️ Keeping every bun at its target would need about": "ℹ️ ដើម្បីរក្សានំទាំងអស់តាមគោលដៅ ត្រូវការប្រហែល",
    "in stock, more than the": "ក្នុងស្តុក ច្រើនជាង",
    "limit — so these buns end below their target days:": "កម្រិត — ដូច្នេះនំទាំងនេះនៅក្រោមថ្ងៃគោលដៅ:",
    ". Raise the limit or lower the target days in ⚙️ Settings to change this.": "។ បង្កើនកម្រិត ឬបន្ថយថ្ងៃគោលដៅក្នុង ⚙️ ការកំណត់ ដើម្បីផ្លាស់ប្តូរ។",
    "— the plan treats their stock as 0.": "— ផែនការគិតស្តុករបស់ពួកវាជា 0។",
    "🔢 Give / reset someone's PIN or password": "🔢 ផ្តល់ / កំណត់ PIN ឬពាក្យសម្ងាត់ឡើងវិញ",
    "🔢 after a name = already has a PIN. A new password signs that person out on their other phones.":
        "🔢 ក្រោយឈ្មោះ = មាន PIN រួចហើយ។ ពាក្យសម្ងាត់ថ្មីនឹងចាកចេញអ្នកនោះពីទូរស័ព្ទផ្សេងទៀត។",
    "⚡ PINs for all operation staff at once": "⚡ PIN សម្រាប់បុគ្គលិកប្រតិបត្តិការទាំងអស់ក្នុងពេលតែមួយ",
    "operation staff have no PIN yet:": "បុគ្គលិកប្រតិបត្តិការមិនទាន់មាន PIN:",
    "people": "នាក់",
    "PINs made. Give each person their PIN (shown only now — they can change it later with 🔑 PIN).":
        "បានបង្កើត PIN។ ផ្តល់ PIN ឲ្យម្នាក់ៗ (បង្ហាញតែឥឡូវនេះ — ពួកគេអាចប្តូរពេលក្រោយដោយ 🔑 PIN)។",
    "👷 Names in “Produced by” (people without an account)": "👷 ឈ្មោះក្នុង “ផលិតដោយ” (អ្នកគ្មានគណនី)",
    "All operation staff are already in the list by themselves — add here only helpers without an account.":
        "បុគ្គលិកប្រតិបត្តិការទាំងអស់មានក្នុងបញ្ជីដោយស្វ័យប្រវត្តិ — បន្ថែមនៅទីនេះតែអ្នកជួយដែលគ្មានគណនី។",
    "📋 Daily tasks (checklist)": "📋 ការងារប្រចាំថ្ងៃ (បញ្ជីត្រួតពិនិត្យ)",
    "auto prod = done by itself when production is saved for that day · auto count = done when the evening count is saved · empty = staff tap ✅. 'Who' = default people (Admin can change per day in 📋 Tasks).":
        "auto prod = រួចរាល់ដោយខ្លួនឯង ពេលរក្សាទុកការផលិតថ្ងៃនោះ · auto count = រួចរាល់ពេលរក្សាទុកការរាប់ពេលល្ងាច · ទទេ = បុគ្គលិកចុច ✅។ 'អ្នកណា' = អ្នកលំនាំដើម (Admin អាចប្តូរតាមថ្ងៃក្នុង 📋 ការងារ)។",
    "done by itself when production is saved for that day": "រួចរាល់ដោយខ្លួនឯង ពេលរក្សាទុកការផលិតថ្ងៃនោះ",
    "done when the evening count is saved": "រួចរាល់ពេលរក្សាទុកការរាប់ពេលល្ងាច",
    "staff tap": "បុគ្គលិកចុច",
    "default people (Admin can change per day in": "អ្នកលំនាំដើម (Admin អាចប្តូរតាមថ្ងៃក្នុង",
    "Names:": "ឈ្មោះ:",
    "🏭 ticked = this bun can be produced on that weekday. 🎯 = days of sales to keep in stock. 🟤 = a batch older than this is flagged 'sell first'.":
        "🏭 ធីក = នំនេះអាចផលិតនៅថ្ងៃនោះ។ 🎯 = ចំនួនថ្ងៃលក់ដែលត្រូវរក្សាក្នុងស្តុក។ 🟤 = ឡូតិ៍ចាស់ជាងនេះត្រូវសម្គាល់ 'លក់មុន'។",
    "ticked": "ធីក",
    "this bun can be produced on that weekday": "នំនេះអាចផលិតនៅថ្ងៃនោះ",
    "days of sales to keep in stock": "ចំនួនថ្ងៃលក់ដែលត្រូវរក្សាក្នុងស្តុក",
    "a batch older than this is flagged 'sell first'": "ឡូតិ៍ចាស់ជាងនេះត្រូវសម្គាល់ 'លក់មុន'",
    "Automatic by role: every account with role staff in the Supply Hub (operation staff) gets this access by itself — also new staff added later. Change one person only if they must be different.":
        "ស្វ័យប្រវត្តិតាមតួនាទី: គណនីទាំងអស់ដែលមានតួនាទី staff ក្នុង Supply Hub (បុគ្គលិកប្រតិបត្តិការ) ទទួលសិទ្ធិនេះដោយខ្លួនឯង — ទាំងបុគ្គលិកថ្មីដែលបន្ថែមពេលក្រោយ។ កែតែម្នាក់ៗ បើត្រូវខុសគ្នា។",
    "Automatic by role": "ស្វ័យប្រវត្តិតាមតួនាទី",
    "every account with role": "គណនីទាំងអស់ដែលមានតួនាទី",
    "in the Supply Hub (operation staff) gets this access by itself": "ក្នុង Supply Hub (បុគ្គលិកប្រតិបត្តិការ) ទទួលសិទ្ធិនេះដោយខ្លួនឯង",
    "also new staff added later": "ទាំងបុគ្គលិកថ្មីដែលបន្ថែមពេលក្រោយ",
    "Change one person only if they must be different": "កែតែម្នាក់ៗ បើត្រូវខុសគ្នា",
    "The access above is saved with": "សិទ្ធិខាងលើត្រូវរក្សាទុកដោយ",
    "The boxes below save by themselves": "ប្រអប់ខាងក្រោមរក្សាទុកដោយខ្លួនឯង",
    "Same accounts as the Supply Hub: the role is also used there. 'staff' = operation staff (also gets the operation pages in the Supply Hub). 'viewer' = can only look in the Supply Hub.":
        "គណនីដូច Supply Hub: តួនាទីក៏ប្រើនៅទីនោះដែរ។ 'staff' = បុគ្គលិកប្រតិបត្តិការ (ទទួលទំព័រប្រតិបត្តិការក្នុង Supply Hub ផងដែរ)។ 'viewer' = អាចមើលតែក្នុង Supply Hub។",
    "auto = by role (operation staff = edit)": "ស្វ័យប្រវត្តិ = តាមតួនាទី (បុគ្គលិកប្រតិបត្តិការ = កែបាន)",
    "auto = by role (above)": "ស្វ័យប្រវត្តិ = តាមតួនាទី (ខាងលើ)",
    "Errors the bot cannot repair by itself are mistakes in the program — send this list (or a screenshot) to get the program fixed. Tick them off below when solved.":
        "កំហុសដែលបូតមិនអាចជួសជុលដោយខ្លួនឯង គឺជាកំហុសក្នុងកម្មវិធី — ផ្ញើបញ្ជីនេះ (ឬរូបថតអេក្រង់) ដើម្បីឲ្យកែកម្មវិធី។ ធីកចេញពេលដោះស្រាយរួច។",
    "Put \"quotes\" around a number with a comma (e.g. \"1,200\") or remove the comma.": "ដាក់ \"សញ្ញាសម្រង់\" ជុំវិញលេខដែលមានក្បៀស (ឧ. \"1,200\") ឬលុបក្បៀសចេញ។",
    "The line has": "ជួរនេះមាន",
    "columns — it needs": "ជួរឈរ — វាត្រូវការ",
    "Columns:": "ជួរឈរ:",
    "Give a staff name.": "សូមដាក់ឈ្មោះបុគ្គលិក។",
    "Choose a person.": "សូមជ្រើសបុគ្គល។",
    "This username already exists.": "ឈ្មោះអ្នកប្រើនេះមានរួចហើយ។",
    "Give a PIN or a password.": "សូមដាក់ PIN ឬពាក្យសម្ងាត់។",
    "Username: 3–30 small letters, numbers, . _ -": "ឈ្មោះអ្នកប្រើ: អក្សរតូច លេខ . _ - ចំនួន 3–30",
    "✅ Saved for": "✅ បានរក្សាទុកសម្រាប់",
    "created. Sign in: choose “": "បានបង្កើត។ ចូល: ជ្រើស “",
    "the PIN.": "PIN។",
    "the password.": "ពាក្យសម្ងាត់។",
    "no PIN yet": "មិនទាន់មាន PIN",
    "pcs is not a number": "គ្រាប់ មិនមែនជាលេខ",
    "unknown bun code": "កូដនំមិនស្គាល់",
    "date cannot be read": "មិនអាចអានថ្ងៃ",
    "date is empty": "ថ្ងៃទទេ",
    "pcs is below 0": "គ្រាប់ តិចជាង 0",
    "✅ Settings saved · targets:": "✅ បានរក្សាទុកការកំណត់ · គោលដៅ:",
    "targets:": "គោលដៅ:",
    "settings file is broken — the app uses the default settings": "ឯកសារការកំណត់ខូច — កម្មវិធីប្រើការកំណត់លំនាំដើម",
    "Open ⚙️ Settings and press 💾 Save settings to write a good file again.": "បើក ⚙️ ការកំណត់ ហើយចុច 💾 រក្សាទុកការកំណត់ ដើម្បីសរសេរឯកសារល្អឡើងវិញ។",
    "The settings file cannot be read — nothing was changed.": "មិនអាចអានឯកសារការកំណត់ — គ្មានអ្វីត្រូវបានផ្លាស់ប្តូរ។",
    "Settings were being saved by someone else. Try again.": "មានអ្នកផ្សេងកំពុងរក្សាទុកការកំណត់។ សូមព្យាយាមម្តងទៀត។",
    "Someone else is saving the accounts right now. Try again.": "មានអ្នកផ្សេងកំពុងរក្សាទុកគណនី។ សូមព្យាយាមម្តងទៀត។",
    "The accounts file cannot be read safely — nothing was changed.": "មិនអាចអានឯកសារគណនីដោយសុវត្ថិភាព — គ្មានអ្វីត្រូវបានផ្លាស់ប្តូរ។",

    # --- morning / evening counts ------------------------------------------------------------------
    "Count date": "ថ្ងៃរាប់",
    "When did you count?": "តើអ្នករាប់នៅពេលណា?",
    "🌅 Morning — before the day's sales": "🌅 ពេលព្រឹក — មុនការលក់ប្រចាំថ្ងៃ",
    "🌙 Evening — after the day's sales": "🌙 ពេលល្ងាច — ក្រោយការលក់ប្រចាំថ្ងៃ",
    "Count each stock and press its 💾 Save.": "រាប់ស្តុកនីមួយៗ ហើយចុច 💾 រក្សាទុក របស់វា។",
    "— the others keep their last count. The sheets start with what the app expects: only change what is different. Evening: first":
        "— ស្តុកផ្សេងរក្សាការរាប់ចុងក្រោយ។ តារាងចាប់ផ្តើមពីអ្វីដែលកម្មវិធីរំពឹង: កែតែអ្វីដែលខុស។ ពេលល្ងាច: ដំបូង",
    "🚚 move": "🚚 ផ្ទេរ",
    "what the cooling room needs for tomorrow.": "អ្វីដែលទូរត្រជាក់ត្រូវការសម្រាប់ថ្ងៃស្អែក។",
    "🌅 Morning count of": "🌅 ការរាប់ពេលព្រឹកថ្ងៃ",
    ": saved as the stock at the end of": ": រក្សាទុកជាស្តុកនៅចុងថ្ងៃ",
    ". The sales of": "។ ការលក់ថ្ងៃ",
    "are taken off it.": "ត្រូវដកចេញពីវា។",
    "are taken off.": "ត្រូវដកចេញ។",
    "Count before anything is sold or delivered.": "សូមរាប់មុនពេលលក់ ឬដឹកនំចេញ។",
    "· counted": "· បានរាប់",
    "(morning). Counted before the day's sales? Then press 🌅 below: the count becomes the stock at the end of":
        "(ពេលព្រឹក)។ រាប់មុនការលក់ប្រចាំថ្ងៃឬ? បើដូច្នេះ ចុច 🌅 ខាងក្រោម: ការរាប់នឹងក្លាយជាស្តុកនៅចុងថ្ងៃ",
    ", and the sales of": " ហើយការលក់ថ្ងៃ",
    "🌅 Yes — counted before the day's sales (fix)": "🌅 បាទ/ចាស — រាប់មុនការលក់ (កែ)",
    "🌙 No — it is the stock at the end of the day": "🌙 ទេ — វាជាស្តុកនៅចុងថ្ងៃ",
    ": fixed — now the stock at the end of": ": បានកែ — ឥឡូវជាស្តុកនៅចុងថ្ងៃ",
    "count moved to morning": "ការរាប់ត្រូវប្តូរទៅពេលព្រឹក",

    # --- count from an Excel file -----------------------------------------------------------------
    "📥 Fill from your Excel count sheet": "📥 បំពេញពីតារាងរាប់ Excel របស់អ្នក",
    "Send the Excel file of your count (your usual layout: one row per production date, one column per bun). The numbers go into the sheet below — check them, then press 💾 Save.":
        "ផ្ញើឯកសារ Excel នៃការរាប់របស់អ្នក (ទម្រង់ធម្មតា: មួយជួរសម្រាប់មួយថ្ងៃផលិត មួយជួរឈរសម្រាប់មួយនំ)។ លេខនឹងចូលក្នុងតារាងខាងក្រោម — ពិនិត្យ រួចចុច 💾 រក្សាទុក។",
    "Excel file (.xlsx)": "ឯកសារ Excel (.xlsx)",
    "⚠️ This file cannot be read:": "⚠️ មិនអាចអានឯកសារនេះបាន:",
    "⚠️ No count found in this file: it needs a row with the bun names (N1, N2 … ស, ល, ក, តយ) and one row per production date under it.":
        "⚠️ រកមិនឃើញការរាប់ក្នុងឯកសារនេះ: វាត្រូវការជួរដែលមានឈ្មោះនំ (N1, N2 … ស, ល, ក, តយ) និងមួយជួរសម្រាប់មួយថ្ងៃផលិតនៅខាងក្រោម។",
    "Sheet in the file": "សន្លឹកក្នុងឯកសារ",
    "dates": "ថ្ងៃ",
    "⚠️ This sheet looks like": "⚠️ សន្លឹកនេះមើលទៅដូចជា",
    ", not": " មិនមែន",
    ". Check before you use it.": "។ សូមពិនិត្យមុនប្រើ។",
    "⚠️ The sheet says": "⚠️ សន្លឹកសរសេរថ្ងៃ",
    "; this count is saved for": "; ការរាប់នេះរក្សាទុកសម្រាប់ថ្ងៃ",
    ". Check the date and morning / evening above.": "។ សូមពិនិត្យថ្ងៃ និងព្រឹក / ល្ងាច ខាងលើ។",
    "Also in the file:": "មានក្នុងឯកសារផងដែរ:",
    "⬇️ Put these numbers in the count sheet": "⬇️ ដាក់លេខទាំងនេះចូលតារាងរាប់",
    "pcs from": "គ្រាប់ ពី",
    "are in the count sheet of": "បានចូលតារាងរាប់នៃ",
    "— open its tab, check them, then press 💾 Save.": "— បើកផ្ទាំងរបស់វា ពិនិត្យ រួចចុច 💾 រក្សាទុក។",

    # --- plan: own sales / day and max per day ---------------------------------------------------------
    "✏️ Adjust the plan — max production per day, sales / day": "✏️ កែផែនការ — ការផលិតអតិបរមាក្នុងមួយថ្ងៃ, ការលក់ / ថ្ងៃ",
    "bun(s) set by you": "នំកំណត់ដោយអ្នក",
    "🏭 Max production per day (pcs, 0 = no limit)": "🏭 ការផលិតអតិបរមាក្នុងមួយថ្ងៃ (គ្រាប់, 0 = គ្មានកម្រិត)",
    "Sales / day: the app's number comes from the sale journal (average of the selling days). Type your own number to use it instead — in 📊 Live stock, 📅 Next week plan and 🧊 rooms; empty = use the app's. The days of the week keep their shape.":
        "ការលក់ / ថ្ងៃ: លេខរបស់កម្មវិធីមកពីបញ្ជីលក់ (មធ្យមនៃថ្ងៃលក់)។ វាយលេខរបស់អ្នក ដើម្បីប្រើលេខនោះជំនួស — ក្នុង 📊 ស្តុកផ្ទាល់, 📅 ផែនការសប្តាហ៍ក្រោយ និង 🧊 បន្ទប់; ទទេ = ប្រើលេខកម្មវិធី។ ថ្ងៃនីមួយៗក្នុងសប្តាហ៍រក្សារូបរាងដដែល។",
    "✏️ Adjust sales / day": "✏️ កែការលក់ / ថ្ងៃ",
    "✏️ Sold / day typed by you:": "✏️ លក់ / ថ្ងៃ ដែលអ្នកវាយ:",
    "App (pcs/day)": "កម្មវិធី (គ្រាប់/ថ្ងៃ)",
    "✏️ Your sales / day": "✏️ ការលក់ / ថ្ងៃ របស់អ្នក",
    "Your sales / day": "ការលក់ / ថ្ងៃ របស់អ្នក",
    "Empty = use the app's number": "ទទេ = ប្រើលេខកម្មវិធី",
    "↺ Use the app's sales / day for all": "↺ ប្រើការលក់ / ថ្ងៃ របស់កម្មវិធីសម្រាប់ទាំងអស់",
    "✅ Saved — the app uses your sales / day now.": "✅ បានរក្សាទុក — កម្មវិធីប្រើការលក់ / ថ្ងៃ របស់អ្នកឥឡូវនេះ។",
    "✏️ Planned with": "✏️ ធ្វើផែនការដោយ",
    "your sales / day": "ការលក់ / ថ្ងៃ របស់អ្នក",
    "🏭 At most": "🏭 យ៉ាងច្រើន",
    "pcs a day. When it is not enough, every bun first gets enough not to run out before it is made again; the rest is shared so all buns come closer to their target at the same pace.":
        "គ្រាប់ក្នុងមួយថ្ងៃ។ ពេលមិនគ្រប់ នំនីមួយៗទទួលបានគ្រប់មុនសិន ដើម្បីកុំឲ្យអស់មុនពេលផលិតម្តងទៀត; ដែលនៅសល់ចែកឲ្យនំទាំងអស់ខិតជិតគោលដៅក្នុងល្បឿនដូចគ្នា។",
    "plan settings saved": "បានរក្សាទុកការកំណត់ផែនការ",
}

# the 3D view (JavaScript text): exact phrases only
KM_JS = {
    "🟢 Door IN (new stock)": "🟢 ទ្វារចូល (ស្តុកថ្មី)",
    "🟠 Door OUT (take first)": "🟠 ទ្វារចេញ (យកមុន)",
    "🚪 Door IN / OUT": "🚪 ទ្វារចូល / ចេញ",
    "🚶 Walkway (keep free)": "🚶 ផ្លូវដើរ (ទុកទំនេរ)",
    " (keep empty)": " (ទុកទំនេរ)",
    "👆 Tap a stack: bun, lot date, age, crates, pcs.": "👆 ចុចលើជង់: នំ ថ្ងៃឡូតិ៍ អាយុ កេស គ្រាប់។",
    "Drag to turn · pinch / wheel to zoom.": "អូសដើម្បីបង្វិល · ច្បិច / កង់ដើម្បីពង្រីក។",
    "All buns": "នំទាំងអស់",
    "Color: age": "ពណ៌: អាយុ",
    "Color: bun type": "ពណ៌: ប្រភេទនំ",
    "Label: bun": "ស្លាក: នំ",
    "Label: lot date": "ស្លាក: ថ្ងៃឡូតិ៍",
    "⏸ Pause": "⏸ ផ្អាក",
    "▶ Play": "▶ លេង",
    "🏭 Both rooms": "🏭 បន្ទប់ទាំងពីរ",
    "📥 new ": "📥 ថ្មី ",
    " · ⭐ TAKE FIRST": " · ⭐ យកមុន",
    " deep · ": " ជម្រៅ · ",
    " stacks · ": " ជង់ · ",
    " crates · ": " កេស · ",
    " pcs": " គ្រាប់",
    " 0–2 days · ": " 0–2 ថ្ងៃ · ",
    " fresh · ": " ស្រស់ · ",
    " near shelf life · ": " ជិតផុតអាយុកាល · ",
    " past shelf life": " ហួសអាយុកាល",
    "1 lane = 1 bun (yellow name at the front of each lane) · take from the FRONT · push new crates in at the BACK of the same lane · ⭐ = oldest (take first) · 📥 = space for tomorrow":
        "1 ជួរ = 1 នំ (ឈ្មោះលឿងនៅខាងមុខជួរ) · យកពីខាងមុខ · រុញកេសថ្មីចូលនៅខាងក្រោយជួរដដែល · ⭐ = ចាស់ជាងគេ (យកមុន) · 📥 = កន្លែងសម្រាប់ការផលិតថ្ងៃស្អែក",
    "\\'s production": "",
    "Raw material": "វត្ថុធាតុដើម",
    "Cooling fan": "កង្ហារត្រជាក់",
    "Cooling room": "ទូរត្រជាក់",
    "Freezer room": "ទូរកក",
}

LANGS = {"en": "🇬🇧 English", "km": "🇰🇭 ខ្មែរ"}
_TR = {}


def lang():
    try:
        return st.session_state.get("lang", "en")
    except Exception:
        return "en"


def _tr_rx():
    if "rx" not in _TR:
        keys = sorted((k for k in KM if k.strip()), key=len, reverse=True)
        parts = []
        for k in keys:
            p = re.escape(k)
            if re.match(r"[A-Za-z0-9]", k):
                p = r"(?<![A-Za-z0-9_])" + p
            if re.search(r"[A-Za-z0-9]$", k):
                p = p + r"(?![A-Za-z0-9_])"
            parts.append(p)
        _TR["rx"] = re.compile("|".join(parts))
    return _TR["rx"]


def _tr_plain(s):
    hit = _TR.setdefault("cache", {})
    if s not in hit:
        if len(hit) > 20000:
            hit.clear()
        hit[s] = _tr_rx().sub(lambda m: KM.get(m.group(0), m.group(0)), s)
    return hit[s]


def tr(s):
    """English -> Khmer when ខ្មែរ is chosen (phrases from KM; numbers, codes and bun names stay)."""
    if lang() != "km" or not isinstance(s, str) or not s or not re.search(r"[A-Za-z]", s):
        return s
    if "<style" in s or "<script" in s:
        return s
    if "<" in s and ">" in s:                                   # HTML: only the text between the tags
        return "".join(x if x.startswith("<") else _tr_plain(x) for x in re.split(r"(<[^>]*>)", s))
    return _tr_plain(s)


def tr_js(html):
    if lang() != "km":
        return html
    for k in sorted(KM_JS, key=len, reverse=True):
        html = html.replace(k, KM_JS[k])
    return html


def _tr_cfg(df, cfg):
    """Column labels for st.dataframe / st.data_editor (the real column names stay, so the code still works)."""
    cols = [str(c) for c in getattr(df, "columns", [])]
    out = dict(cfg or {})
    for c in cols:
        v = out.get(c, None)
        if v is None and c in out:
            continue                                            # hidden column
        if isinstance(v, str):
            out[c] = tr(v)
        elif isinstance(v, dict):
            v = dict(v)
            v["label"] = tr(v.get("label") or c)
            if v.get("help"):
                v["help"] = tr(v["help"])
            out[c] = v
        elif v is None:
            t = tr(c)
            if t != c:
                out[c] = {"label": t}
    return out


def _install_tr():
    """Wrap Streamlit's screen functions once, so every label / message goes through tr()."""
    from streamlit.delta_generator import DeltaGenerator as DG
    if getattr(DG, "_hk_tr", False):
        return
    first = ["markdown", "caption", "subheader", "header", "title", "info", "warning", "success", "error", "button",
             "download_button", "expander", "checkbox", "toggle", "text_input", "number_input", "date_input",
             "time_input", "text_area", "toast", "form_submit_button", "popover", "slider", "file_uploader",
             "link_button", "radio", "selectbox", "multiselect", "select_slider", "pills", "segmented_control",
             "metric", "write", "page_link", "status", "color_picker", "camera_input", "feedback"]
    kw_text = ("label", "body", "help", "placeholder", "caption")
    choice = {"radio", "selectbox", "multiselect", "select_slider", "pills", "segmented_control"}

    def wrap(name, fn):
        def w(self, *a, **k):
            if lang() == "km":
                a = list(a)
                if a and isinstance(a[0], str) and name != "write":
                    a[0] = tr(a[0])
                elif name == "write":
                    a = [tr(x) if isinstance(x, str) else x for x in a]
                if name == "metric" and len(a) > 1 and isinstance(a[1], str):
                    a[1] = tr(a[1])
                for kk in kw_text:
                    if isinstance(k.get(kk), str):
                        k[kk] = tr(k[kk])
                if name in choice:
                    ff = k.get("format_func") or str
                    k["format_func"] = lambda x, _f=ff: tr(_f(x))
                if name == "radio" and isinstance(k.get("captions"), (list, tuple)):
                    k["captions"] = [tr(x) for x in k["captions"]]
            return fn(self, *a, **k)
        w.__name__ = name
        return w

    for n in first:
        if hasattr(DG, n):
            setattr(DG, n, wrap(n, getattr(DG, n)))
    tabs0 = DG.tabs

    def tabs(self, labels, *a, **k):
        return tabs0(self, [tr(x) for x in labels] if lang() == "km" else labels, *a, **k)
    DG.tabs = tabs
    for n in ("dataframe", "data_editor"):
        f0 = getattr(DG, n)

        def tbl(self, data=None, *a, _f=f0, _n=n, **k):
            if lang() == "km" and data is not None and hasattr(data, "columns"):
                k["column_config"] = _tr_cfg(data, k.get("column_config"))
                if _n == "dataframe":                      # read-only: the words in the cells too
                    try:
                        data = data.copy()
                        for c in data.columns:
                            if data[c].dtype == object or str(data[c].dtype).startswith("str"):
                                data[c] = data[c].map(lambda x: tr(x) if isinstance(x, str) else x)
                    except Exception:
                        pass
            return _f(self, data, *a, **k)
        setattr(DG, n, tbl)
    DG._hk_tr = True
    import streamlit as _st
    main = getattr(_st, "_main", None)
    for n in first + ["tabs", "dataframe", "data_editor"]:
        if main is not None and hasattr(_st, n) and hasattr(main, n):
            try:
                setattr(_st, n, getattr(main, n))
            except Exception:
                pass


_install_tr()


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
COUNT_COLS = ["Saved_At", "Count_Date", "Bun", "Prod_Date", "Pcs", "By", "Count_Id", "Place", "Kind"]
ADJ_COLS = ["Saved_At", "Date", "Bun", "Prod_Date", "Pcs", "Reason", "By", "Adj_Id", "Place"]
MOVE_FILE = "stock_moves.csv"                     # evening moves: frozen room -> cooling room
MOVE_COLS = ["Saved_At", "Date", "Bun", "Prod_Date", "Pcs", "From", "To", "By", "Move_Id"]
# ---- the 3 stocks, each counted and saved by itself ----
ROLES = ["cool", "frozen", "aeon"]
ROLE_ICON = {"cool": "❄️", "frozen": "🧊", "aeon": "🛒"}
ROLE_EN = {"cool": "Cooling room", "frozen": "Frozen room", "aeon": "Frozen AEON"}
DEFAULT_PLACE_NAMES = {"cool": "ស្តុកនំក្នុងទូរ", "frozen": "ស្តុកទូរកក", "aeon": "ស្តុកទូរកក AEON"}
OLD_PLACE_ROLE = {"ស្តុកនំក្នុងទូរ": "cool", "ស្តុកទូរកក": "aeon"}    # counts saved before the rooms were split
AEON_WORDS = ("AEON", "អ៊ីអន", "អ៊ីយ៉ន")             # customer names whose buns come from the AEON stock
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
    "max_prod_per_day": 20000,      # 0 = no limit (the factory makes at most ~20,000 pcs a day)
    "access_by_role": {"staff": "edit", "sales": "view", "viewer": "view"},   # automatic, by Supply Hub role
    "access_override": {},          # username -> hidden / view / edit, only for people who differ from their role
    "access_default": "view",
    "places": ["ស្តុកនំក្នុងទូរ", "ស្តុកទូរកក"],   # (old setting, replaced by place_names)
    "place_names": dict(DEFAULT_PLACE_NAMES),       # cooling room / frozen room / frozen AEON
    "cool_days": 1,                                 # evening move: cooling room keeps this many days of sales
    "daily_in_pcs": 16000,                          # the frozen room always keeps space for this much new production
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


def _parse_csv(data, cols):
    """(frame of good lines, header, bad lines). A line with too many / too few columns (e.g. 1,200 typed
    without quotes in Excel) is NOT read shifted: it is kept aside untouched for the 🤖 bot / Admin."""
    text = data.decode("utf-8-sig", errors="replace")
    rows = list(csv.reader(io.StringIO(text)))
    if not rows:
        return pd.DataFrame(columns=cols, dtype=object), list(cols), []
    header = [h.strip() for h in rows[0]]
    good, bad = [], []
    for r in rows[1:]:
        if not any(str(x).strip() for x in r):
            continue
        (good if len(r) == len(header) else bad).append(r)
    df = pd.DataFrame(good, columns=header, dtype=object)
    for c in cols:
        if c not in df.columns:
            df[c] = ""
    return df[cols].astype(object), header, bad


def _load_csv(name, cols, max_age=8):
    data, rev = read_bytes(name, max_age)
    if not data:
        return pd.DataFrame(columns=cols, dtype=object), rev, list(cols), []
    df, header, bad = _parse_csv(data, cols)
    return df, rev, header, bad


def read_csv(name, cols, max_age=8):
    df, rev, _h, _bad = _load_csv(name, cols, max_age)
    return df, rev


def _csv_bytes(df, cols, bad=()):
    buf = io.StringIO()
    df[cols].to_csv(buf, index=False, lineterminator="\n")
    if bad:                                              # lines the app could not read stay in the file as they were
        w = csv.writer(buf, lineterminator="\n")
        for r in bad:
            w.writerow(r)
    return buf.getvalue().encode("utf-8-sig")


def modify_csv(name, cols, change):
    """read -> change(frame) -> save; retried if someone else saved at the same moment."""
    for attempt in range(5):
        df, rev, _h, bad = _load_csv(name, cols, max_age=0)
        new = change(df.copy())                          # (the bot's change may raise Conflict: then nothing is saved)
        try:
            write_bytes(name, _csv_bytes(new, cols, bad), rev)
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
        return pd.DataFrame(columns=["Date", "Bun", "Pcs", "Aeon"]), {}
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
        cust = str(r[1]).upper()
        is_aeon = any(w in cust for w in AEON_WORDS)       # AEON orders are taken from the AEON frozen stock
        for k, c in cols.items():
            v = r[c] if c < len(r) else None
            if isinstance(v, (int, float)) and v:
                out.append((d, k, float(v), is_aeon))
            elif isinstance(v, str) and v.strip().replace(".", "", 1).isdigit():
                out.append((d, k, float(v), is_aeon))
    df = pd.DataFrame(out, columns=["Date", "Bun", "Pcs", "Aeon"])
    if ym and not df.empty:                       # a journal only speaks for its own month
        df = df[[(x.year, x.month) == ym for x in df["Date"]]]
    return df.groupby(["Date", "Bun", "Aeon"], as_index=False)["Pcs"].sum(), names


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
    sales = pd.concat(frames, ignore_index=True) if frames else pd.DataFrame(columns=["Date", "Bun", "Pcs", "Aeon"])
    if not sales.empty:
        sales = sales.groupby(["Date", "Bun", "Aeon"], as_index=False)["Pcs"].sum()
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


def place_names(cfg):
    pn = cfg.get("place_names") or {}
    return {r: str(pn.get(r) or DEFAULT_PLACE_NAMES[r]).strip() for r in ROLES}


def place_label(cfg, role):
    return f"{ROLE_ICON[role]} {place_names(cfg)[role]}"


def _row_role(place, kind):
    k = str(kind or "").strip()
    if k in ROLES:
        return k
    return OLD_PLACE_ROLE.get(str(place or "").strip(), "cool")


def latest_place_counts(counts):
    """{role: (count_date, {bun: {prod_date: pcs}}, count_id, saved_at, by, {buns in that count})} — the newest
    count of each stock (cooling room / frozen room / AEON), each saved by itself."""
    out = {}
    if counts.empty:
        return out
    c = counts.copy()
    c["_cd"] = c["Count_Date"].map(_day)
    c = c[c["_cd"].notna()]
    c["_role"] = [_row_role(p, k) for p, k in zip(c["Place"], c["Kind"])]
    for role, g in c.groupby("_role"):
        g = g.sort_values(["_cd", "Saved_At"])
        cid = g["Count_Id"].iloc[-1]
        last = g[g["Count_Id"] == cid]
        cd = last["_cd"].iloc[0]
        bt = {}
        for r in last.to_dict("records"):
            n = _num(r["Pcs"])
            if n:
                k = _day(r["Prod_Date"]) or cd
                bt.setdefault(r["Bun"], {})
                bt[r["Bun"]][k] = bt[r["Bun"]].get(k, 0) + n
        out[role] = (cd, bt, cid, str(last["Saved_At"].iloc[0]), ", ".join(sorted(set(last["By"]))), set(last["Bun"]))
    return out


def _take(batch, n, first=None):
    """Takes n pcs, oldest production date first (or a given date first). Returns ([(date, pcs)], not found)."""
    got = []
    keys = ([first] if first in batch else []) + [k for k in sorted(batch) if k != first]
    for k in keys:
        if n <= 0:
            break
        q = min(batch.get(k, 0), n)
        if q > 0:
            batch[k] -= q
            got.append((k, q))
            n -= q
    return got, n


def compute_places(buns, prod, counts, adjs, sales, until, moves=None):
    """The stock of each place day by day, from each place's own last count:
    new production -> frozen room · evening moves frozen -> cooling · AEON orders from the AEON stock (if it runs
    out: from the normal stock) · other orders from the cooling room first, then the frozen room.
    A place counted later than another is 'not known yet' until its count day (its count already includes those days).
    Returns ({role: {bun: {prod_date: pcs}}}, short {bun: pcs}, history, no_count [buns], last count {role: info})."""
    if moves is None:
        moves, _r = read_csv(MOVE_FILE, MOVE_COLS)
    base = latest_place_counts(counts)
    p = prod.copy()
    p["_d"] = p["Prod_Date"].map(_day)
    p["_n"] = p["Pcs"].map(_num).astype(float)
    a = adjs.copy()
    a["_d"] = a["Date"].map(_day)
    a["_pd"] = a["Prod_Date"].map(_day)
    a["_n"] = a["Pcs"].map(_num).astype(float)
    a["_role"] = [x if x in ROLES else "" for x in a["Place"].astype(str).str.strip()]
    mv = moves.copy()
    mv["_d"] = mv["Date"].map(_day)
    mv["_pd"] = mv["Prod_Date"].map(_day)
    mv["_n"] = mv["Pcs"].map(_num).astype(float)
    gen, aeon = {}, {}
    has_flag = "Aeon" in sales.columns
    for r in sales.itertuples(index=False):
        tgt = aeon if has_flag and bool(getattr(r, "Aeon")) else gen
        tgt[(r.Date, r.Bun)] = tgt.get((r.Date, r.Bun), 0) + r.Pcs
    first_day = min([d for d in p["_d"].dropna()] + [until])
    start = min([v[0] for v in base.values()] + [first_day - timedelta(days=1)]) if base else first_day - timedelta(days=1)
    seen = set().union(*[v[5] for v in base.values()]) if base else set()
    out = {r: {} for r in ROLES}
    short, hist, no_count = {}, [], []
    prod_by = p[p["_d"].notna()].groupby(["Bun", "_d"])["_n"].sum().to_dict()
    # production of the frozen room's count day that was logged AFTER that count (e.g. the evening count was done at
    # 16:00, the day's production came in later / was logged next morning): the count could not include it
    late_by = {}
    if "frozen" in base:
        fcd, fbt, _cid, f_saved = base["frozen"][0], base["frozen"][1], base["frozen"][2], base["frozen"][3]
        sv = p["Saved_At"].astype(str).str.strip() if "Saved_At" in p.columns else pd.Series([""] * len(p))
        late = p[(p["_d"] == fcd) & (sv > str(f_saved).strip())]
        for b2, g2 in late.groupby("Bun"):
            if not fbt.get(b2, {}).get(fcd):                  # the count has no lot of that day: add it
                late_by[b2] = float(g2["_n"].sum())
    for bun in buns:
        if bun not in seen:
            no_count.append(bun)
        stock, known = {}, {}
        for r in ROLES:
            if r in base and base[r][0] > start:
                stock[r], known[r] = {}, False               # counted later: its count covers the days before
            else:
                stock[r], known[r] = dict(base[r][1].get(bun, {})) if r in base else {}, True
                if r == "frozen" and r in base and base[r][0] == start and late_by.get(bun):
                    stock[r][start] = stock[r].get(start, 0) + late_by[bun]   # logged after the count
        ab = a[(a["Bun"] == bun) & a["_d"].notna()]
        mb = mv[(mv["Bun"] == bun) & mv["_d"].notna()]
        miss = 0.0
        d = start + timedelta(days=1)
        while d <= until:
            n = prod_by.get((bun, d), 0)
            if n and known["frozen"]:
                stock["frozen"][d] = stock["frozen"].get(d, 0) + n          # new production goes to the frozen room
            for r in mb[mb["_d"] == d].to_dict("records"):
                fr, to = str(r["From"]).strip(), str(r["To"]).strip()
                if fr not in ROLES or to not in ROLES:
                    continue
                got = _take(stock[fr], r["_n"], r["_pd"])[0] if known[fr] else [(r["_pd"] or d, r["_n"])]
                if known[to]:
                    for k, q in got:
                        stock[to][k] = stock[to].get(k, 0) + q
            for r in ab[ab["_d"] == d].to_dict("records"):
                n, role = r["_n"], r["_role"]
                if n >= 0:
                    role = role or "cool"
                    if known[role]:
                        k = r["_pd"] or d
                        stock[role][k] = stock[role].get(k, 0) + n
                else:
                    rest = -n
                    for role2 in ([role] if role else ["cool", "frozen"]):
                        if rest > 0 and known[role2]:
                            rest = _take(stock[role2], rest, r["_pd"])[1]
            need_a, need_g = aeon.get((d, bun), 0), gen.get((d, bun), 0)
            if need_a and known["aeon"]:
                need_g += _take(stock["aeon"], need_a)[1]        # AEON stock empty: from the normal stock
            if need_g:
                if not known["cool"]:
                    need_g = 0                                   # the cooling room's count will show it
                else:
                    need_g = _take(stock["cool"], need_g)[1]
                if need_g:
                    need_g = _take(stock["frozen"], need_g)[1] if known["frozen"] else 0
                miss += need_g
            for r in ROLES:
                if r in base and base[r][0] == d:                # the evening count of that place
                    stock[r], known[r] = dict(base[r][1].get(bun, {})), True
                    if r == "frozen" and late_by.get(bun):       # that day's production logged after the count
                        stock[r][d] = stock[r].get(d, 0) + late_by[bun]
                stock[r] = {k: v for k, v in stock[r].items() if v > 0.0001}
            hist.append((d, bun, sum(sum(v.values()) for v in stock.values())))
            d += timedelta(days=1)
        for r in ROLES:
            out[r][bun] = {k: v for k, v in stock[r].items() if v > 0.0001}
        short[bun] = miss
    return out, short, pd.DataFrame(hist, columns=["Date", "Bun", "Stock"]), no_count, base


def merge_places(places_stock, buns):
    out = {}
    for b in buns:
        m = {}
        for r in ROLES:
            for k, v in places_stock[r].get(b, {}).items():
                m[k] = m.get(k, 0) + v
        out[b] = m
    return out


def compute_stock(buns, prod, counts, adjs, sales, until):
    """All places together: (batches {bun: {prod_date: pcs}}, short, history, no_count) — used by the plan."""
    pl, short, hist, no_count, _base = compute_places(buns, prod, counts, adjs, sales, until)
    return merge_places(pl, buns), short, hist, no_count


OWN_SPEED = {}          # {bun: pcs/day} typed by Admin ("✏️ Your sales / day"); used instead of the journal's number


def sales_speed(sales, buns, until, lookback, raw=False):
    """Average pcs per SELLING day (days the journal has sales) over the last `lookback` days before `until`.
    Buns with "your sales / day" set use that number (raw=True = always the journal's number)."""
    lo = until - timedelta(days=lookback)
    win = sales[(sales["Date"] > lo) & (sales["Date"] < until)] if not sales.empty else sales
    sell_days = sorted(set(win["Date"])) if not win.empty else []
    n = max(len(sell_days), 1)
    tot = win.groupby("Bun")["Pcs"].sum().to_dict() if not win.empty else {}
    out = {b: tot.get(b, 0) / n for b in buns}
    if not raw:
        out.update({b: v for b, v in OWN_SPEED.items() if b in out})
    return out, len(sell_days)


def forecast(sales, buns, start, days, lookback, raw=False):
    """{(date, bun): pcs} — same weekday average over the last weeks (falls back to the overall average).
    Buns with "your sales / day" are scaled to that number (the weekday shape stays)."""
    lo = start - timedelta(days=lookback)
    win = sales[(sales["Date"] >= lo) & (sales["Date"] < start)] if not sales.empty else sales
    speed, _n = sales_speed(sales, buns, start, lookback, raw=True)
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
    if not raw:
        for b, v in OWN_SPEED.items():
            if b not in buns:
                continue
            wk = [by_wd.get((wd, b), speed.get(b, 0)) for wd in range(7)]
            open_wd = [wd for wd in range(7) if not (by_wd and all(by_wd.get((wd, x), 1) == 0 for x in buns))]
            avg = sum(wk[wd] for wd in open_wd) / max(len(open_wd), 1)
            for i in range(days):
                d = start + timedelta(days=i)
                if d.weekday() not in open_wd:
                    continue
                out[(d, b)] = out[(d, b)] * v / avg if avg > 0 else float(v)
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
        # daily capacity (e.g. 20,000 pcs): first every bun gets enough not to run out before its next production
        # day, then the rest is shared so every bun comes closer to its target at the same pace
        if cap_prod and sum(prod.values()) > cap_prod:
            must = {}
            for b in buns:
                if prod[b] <= 0:
                    must[b] = 0
                    continue
                cover, j = fc.get((d, b), 0), 1
                while j <= 14:                                   # sales until this bun is made again
                    dd = d + timedelta(days=j)
                    if dd.weekday() in pdays[b] and j >= 1 and sum(fc.get((dd, x), 0) for x in buns) > 0:
                        cover += fc.get((dd, b), 0)              # (bread made that day sells from the next day)
                        break
                    cover += fc.get((dd, b), 0)
                    j += 1
                must[b] = min(prod[b], int(-(-max(cover - stock.get(b, 0), 0) // rnd) * rnd))
            if sum(must.values()) >= cap_prod:                   # not even that fits: share the shortage
                f = cap_prod / max(sum(must.values()), 1)
                prod = {b: int(must[b] * f // rnd * rnd) for b in buns}
            else:
                room = cap_prod - sum(must.values())
                extra = {b: prod[b] - must[b] for b in buns}
                f = min(1.0, room / max(sum(extra.values()), 1))
                prod = {b: must[b] + int(extra[b] * f // rnd * rnd) for b in buns}
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
    OWN_SPEED.clear()
    OWN_SPEED.update({b: float(_num(v)) for b, v in (cfg.get("sales_per_day") or {}).items() if _num(v) > 0})
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
    pl_stock, short, hist, no_count, base = compute_places(buns, prod, counts, adjs, sales, t)
    show_flash("c_flash")
    morning_count_banner(cfg, can_edit, st.session_state.get("p_user", ""), base, "live")
    batches = merge_places(pl_stock, buns)
    speed, n_sell = sales_speed(sales, buns, t, int(cfg["lookback_days"]))
    total = sum(sum(v.values()) for v in batches.values())
    tiles([(place_label(cfg, r), f"{int(round(sum(sum(v.values()) for v in pl_stock[r].values()))):,}",
            (f"counted {base[r][0]:%d %b}" if r in base else "never counted")
            + (" · new production comes here" if r == "frozen" else " · AEON orders only" if r == "aeon" else ""))
           for r in ROLES])
    if float(cfg.get("daily_in_pcs", 16000) or 0) > 0:
        sp = frozen_space(cfg, {b: bun_crates(cfg, b, {b: pl_stock["frozen"].get(b, {})}) for b in buns}, speed, buns)
        msg = (f"📥 **Room for new production** in {sp['room']}: **{sp['free']} free stacks ≈ {sp['free_pcs']:,} pcs** · "
               f"needed every day: {sp['need']} stacks for {int(sp['daily']):,} pcs")
        if sp["ok"]:
            st.success(msg)
        else:
            st.error(msg + " — ⚠️ not enough. This evening's 🚚 move list (📦 Stock count) frees space by moving old "
                           "crates to the cooling room.")
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
    if OWN_SPEED:
        st.caption("✏️ Sold / day typed by you: " + ", ".join(f"{b} {int(v):,}" for b, v in OWN_SPEED.items() if b in buns))
    own_sales_editor(cfg, can_edit, names, buns, sales, t, {b: sum(batches[b].values()) for b in buns}, "live")
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



def own_sales_editor(cfg, can_edit, names, buns, sales, t, stock, kp, with_cap=False):
    """✏️ Your sales / day per bun (+ the max production per day on the plan page). Saved in the settings and used
    everywhere: 📊 Live stock (days of stock, status), 📅 plan, 🧊 rooms. Returns {bun: your pcs/day}."""
    app, _n = sales_speed(sales, buns, t, int(cfg["lookback_days"]), raw=True)
    own = {b: float(_num(v)) for b, v in (cfg.get("sales_per_day") or {}).items() if b in buns and _num(v) > 0}
    title = ("✏️ Adjust the plan — max production per day, sales / day" if with_cap else "✏️ Adjust sales / day")
    with st.expander(title + (f" · {len(own)} bun(s) set by you" if own else ""), expanded=False):
        cap_v = None
        if with_cap:
            cA, cB = st.columns([1, 2])
            cap_v = cA.number_input("🏭 Max production per day (pcs, 0 = no limit)", min_value=0, max_value=500000,
                                    step=1000, value=int(cfg.get("max_prod_per_day") or 0), key=f"{kp}_cap",
                                    disabled=not can_edit)
            box = cB
        else:
            box = st
        box.caption("Sales / day: the app's number comes from the sale journal (average of the selling days). Type "
                    "your own number to use it instead — in 📊 Live stock, 📅 Next week plan and 🧊 rooms; empty = use "
                    "the app's. The days of the week keep their shape.")
        n = st.session_state.get("own_n", 0)
        edf = pd.DataFrame([{"Bun": b, "Name": names.get(b, ""), "App (pcs/day)": int(round(app.get(b, 0))),
                             "Your sales / day": (int(own[b]) if b in own else None)}
                            for b in buns if app.get(b, 0) > 0 or b in own or stock.get(b)])
        ed = st.data_editor(edf, hide_index=True, width="stretch", key=f"{kp}_own_{n}",
                            disabled=["Bun", "Name", "App (pcs/day)"] if can_edit else True,
                            column_config={"Your sales / day": st.column_config.NumberColumn(
                                "✏️ Your sales / day", min_value=0, max_value=100000, step=10, format="%d",
                                help="Empty = use the app's number")})
        if can_edit:
            b1, b2 = st.columns(2)
            if b1.button("💾 Save", key=f"{kp}_own_save", type="primary"):
                new_own = {r["Bun"]: int(_num(r["Your sales / day"])) for r in ed.to_dict("records")
                           if _num(r["Your sales / day"]) > 0}
                try:
                    def _ch(c):
                        c["sales_per_day"] = new_own
                        if cap_v is not None:
                            c["max_prod_per_day"] = int(cap_v)
                            c["max_prod_set"] = True
                    update_settings(_ch)
                    audit("plan settings saved", (f"max/day {int(cap_v):,} · " if cap_v is not None else "")
                          + "sales/day " + ", ".join(f"{b} {v:,}" for b, v in new_own.items()))
                    st.session_state["own_flash"] = "✅ Saved — the app uses your sales / day now."
                except Exception as e:
                    st.error(f"⚠️ Not saved: {e}")
                    st.stop()
                _rerun_here()
            if b2.button("↺ Use the app's sales / day for all", key=f"{kp}_own_clear", disabled=not own):
                try:
                    update_settings(lambda c: c.update(sales_per_day={}))
                    st.session_state["own_n"] = n + 1
                except Exception as e:
                    st.error(f"⚠️ Not saved: {e}")
                    st.stop()
                _rerun_here()
    show_flash("own_flash")
    return own

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
    preset = st.session_state.setdefault("_grid_preset", {}).pop(key, None)
    if preset is not None:                               # numbers taken from an uploaded Excel sheet
        bases[key] = preset
    elif key not in st.session_state:                    # shown for the first time, or back from another page
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
    merged = {}                                          # the same date typed on 2 rows: added together
    for d, vals in out:
        m = merged.setdefault(d, {})
        for b, q in vals.items():
            m[b] = m.get(b, 0) + q
    return sorted(merged.items(), key=lambda x: x[0])


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


_MON = {m: i for i, m in enumerate(["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov",
                                      "dec"], 1)}


def _sheet_date(v, year_hint):
    """A date cell of a count sheet: a real date, or text like 'Wed, Nov-18, 26', '18/11/2026', '2026-11-18'."""
    if isinstance(v, datetime):
        return v.date()
    if isinstance(v, date):
        return v
    if isinstance(v, (int, float)) and 40000 < v < 60000:          # an Excel date number
        return (datetime(1899, 12, 30) + timedelta(days=int(v))).date()
    t = str(v or "").strip().lower()
    if not t:
        return None
    m = re.search(r"([a-z]{3})[a-z]*[\s\-/.]*(\d{1,2})\b(?:[,\s\-/.]+(\d{2,4}))?", t)
    if m and m.group(1) in _MON:
        y = int(m.group(3)) if m.group(3) else year_hint
        y = y + 2000 if y < 100 else y
        try:
            return date(y, _MON[m.group(1)], int(m.group(2)))
        except ValueError:
            return None
    m = re.search(r"(\d{4})[\-/.](\d{1,2})[\-/.](\d{1,2})", t)
    if m:
        try:
            return date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        except ValueError:
            return None
    m = re.search(r"(\d{1,2})[\-/.](\d{1,2})[\-/.](\d{2,4})", t)
    if m:
        y = int(m.group(3))
        y = y + 2000 if y < 100 else y
        try:
            return date(y, int(m.group(2)), int(m.group(1)))       # day first, like in Cambodia
        except ValueError:
            return None
    return None


def parse_count_excel(data, cfg, buns, names):
    """Your Excel count sheet -> [{"sheet", "role", "date" (from the title), "rows": [(prod_date, {bun: pcs})]}].
    Finds the header row with the bun names (N1, N2 … ស, ល, ក, តយ), then one row per production date; the
    total row and the សរុប column are left out."""
    from openpyxl import load_workbook
    wb = load_workbook(io.BytesIO(data), data_only=True, read_only=True)
    keys = {}
    for b in buns:                                       # codes and short names first (N1 … ស, ល, ក, តយ)
        for k in (b, short(b)):
            keys.setdefault(str(k).strip().upper(), b)
    by_name = {}
    for b in buns:                                       # then the full names; one name for 2 buns -> the one
        nm = str(names.get(b, "") or "").strip()         # with a short name (ល្ពៅ = N41, not N34)
        if nm:
            by_name.setdefault(nm.upper(), []).append(b)
    for nm, lst in by_name.items():
        keys.setdefault(nm, ([b for b in lst if b in SHORT] or lst)[0])
    pn = place_names(cfg)
    out = []
    for ws in wb.worksheets:
        grid = [list(r) for r in ws.iter_rows(min_row=1, max_row=min(ws.max_row or 200, 300), values_only=True)]
        head_i, cols = None, {}
        for i, row in enumerate(grid[:15]):
            found = {}
            for j, v in enumerate(row):
                b = keys.get(str(v or "").strip().upper())
                if b and b not in found.values():
                    found[j] = b
            if len(found) >= 3:
                head_i, cols = i, found
                break
        if head_i is None:
            continue
        title = " ".join(str(v) for r in grid[:head_i] for v in r if v not in (None, "")) + " " + ws.title
        role = None
        if any(w.upper() in title.upper() for w in AEON_WORDS):
            role = "aeon"
        else:
            for r_ in ("cool", "frozen"):
                if pn.get(r_) and pn[r_] in title:
                    role = r_
            if role is None:
                for nm, r_ in OLD_PLACE_ROLE.items():
                    if nm in title:
                        role = "frozen" if r_ == "aeon" else r_
        m = re.search(r"(\d{1,2})[./-](\d{1,2})[./-](\d{4})", title)
        t_date = None
        if m:
            try:
                t_date = date(int(m.group(3)), int(m.group(2)), int(m.group(1)))
            except ValueError:
                t_date = None
        year = (t_date or today_kh()).year
        rows = {}
        first_col = min(cols)
        for row in grid[head_i + 1:]:
            d = None
            for v in row[:first_col]:                       # the date is left of the bun columns
                d = _sheet_date(v, year)
                if d:
                    break
            if not d:
                continue
            vals = {}
            for j, b in cols.items():
                n = _num(row[j] if j < len(row) else None)
                if n > 0:
                    vals[b] = vals.get(b, 0) + int(round(n))
            if vals:
                r0 = rows.setdefault(d, {})
                for b, q in vals.items():
                    r0[b] = r0.get(b, 0) + q
        out.append({"sheet": ws.title, "role": role, "date": t_date, "rows": sorted(rows.items(), key=lambda x: x[0])})
    return out


def _upload_count(cfg, role, cd, mode, n, show, names, buns):
    """📥 Fill this count sheet from your Excel file (then check and press 💾 Save)."""
    pn = place_names(cfg)[role]
    with st.expander("📥 Fill from your Excel count sheet", expanded=False):
        st.caption("Send the Excel file of your count (your usual layout: one row per production date, one column per "
                   "bun). The numbers go into the sheet below — check them, then press 💾 Save.")
        up = st.file_uploader("Excel file (.xlsx)", type=["xlsx", "xlsm"], key=f"cnt_up_{role}_{n}")
        if not up:
            return
        try:
            found = [x for x in parse_count_excel(up.getvalue(), cfg, buns, names) if x["rows"]]
        except Exception as e:
            st.error(f"⚠️ This file cannot be read: {e}")
            return
        if not found:
            st.error("⚠️ No count found in this file: it needs a row with the bun names (N1, N2 … ស, ល, ក, តយ) and "
                     "one row per production date under it.")
            return
        mine = [x for x in found if x["role"] == role]
        opts = mine + [x for x in found if x not in mine]
        pick = st.selectbox("Sheet in the file", list(range(len(opts))), key=f"cnt_up_pick_{role}_{n}",
                            format_func=lambda i: f"{opts[i]['sheet']} · {len(opts[i]['rows'])} dates · "
                                                  f"{sum(sum(v.values()) for _d, v in opts[i]['rows']):,} pcs")
        x = opts[pick]
        if x["role"] and x["role"] != role:
            st.warning(f"⚠️ This sheet looks like {place_label(cfg, x['role'])}, not {pn}. Check before you use it.")
        if x["date"] and x["date"] != cd:
            st.warning(f"⚠️ The sheet says {x['date']:%d.%m.%Y}; this count is saved for {cd:%d.%m.%Y}. "
                       "Check the date and morning / evening above.")
        unknown = [b for _d, v in x["rows"] for b in v if b not in show]
        rows = [(d, {b: q for b, q in v.items() if b in buns}) for d, v in x["rows"]]
        st.markdown(excel_html(f"{x['sheet']}", [(day_label(d), v) for d, v in rows], show), unsafe_allow_html=True)
        if unknown:
            st.caption("Also in the file: " + ", ".join(sorted(set(short(b) for b in unknown))))
        if st.button("⬇️ Put these numbers in the count sheet", key=f"cnt_up_go_{role}_{n}", type="primary"):
            n2 = n + 1
            st.session_state[f"cnt_n_{role}"] = n2
            st.session_state.setdefault("_grid_preset", {})[f"cnt_{role}_{cd}_{mode[:2]}_{n2}"] = rows
            st.session_state["cntp_" + f"{role}_{cd}_{mode[:2]}_{n2}"] = {
                "data": {pn: {d: dict(v) for d, v in rows}}, "done": {pn: []}, "idx": {pn: 0}}
            st.session_state["c_flash"] = (f"📥 {sum(sum(v.values()) for _d, v in rows):,} pcs from "
                                           f"{x['sheet']} are in the count sheet of {place_label(cfg, role)} — open "
                                           f"its tab, check them, then press 💾 Save.")
            _rerun_here()


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


def _count_phone(places, start_rows, show, names, cd, sig, single=False):
    """Phone: one freezer, one production date at a time, big number boxes, ✅ Counted · next."""
    dk = "cntp_" + sig
    if dk not in st.session_state:
        st.session_state[dk] = {"data": {pl: {d: dict(v) for d, v in start_rows[pl]} for pl in places},
                                "done": {pl: [] for pl in places}, "idx": {pl: 0 for pl in places}}
    S = st.session_state[dk]
    if S.get("goto_pl"):
        st.session_state[dk + "_pl"] = S.pop("goto_pl")       # set before the picker is drawn
    if single:
        pl = places[0]
    else:
        pl = st.radio("🧊 Freezer", places, horizontal=True, key=dk + "_pl")   # fixed labels: the choice never jumps
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
        st.success("🎉 All dates counted — check the total and press 💾 Save below.")
    return {x: sorted((dd, {b: v for b, v in vals.items() if v}) for dd, vals in S["data"][x].items()) for x in places}


def page_count(cfg, can_edit, me):
    st.subheader("📦 Stock count")
    prod, counts, adjs, sales, names, buns = get_data(cfg)
    show_flash("c_flash")
    pn = place_names(cfg)
    c1, c2 = st.columns([1, 2])
    cd = c1.date_input("Count date", value=today_kh(), max_value=today_kh(), key="cnt_date")
    when_opts = ["🌅 Morning — before the day's sales", "🌙 Evening — after the day's sales"]
    if "cnt_when" not in st.session_state:
        st.session_state["cnt_when"] = when_opts[0] if now_kh().hour < 12 else when_opts[1]
    when = c1.radio("When did you count?", when_opts, key="cnt_when")
    morning = when.startswith("🌅")
    cd_save = cd - timedelta(days=1) if morning else cd           # a morning count = the stock at the end of the day before
    pl_now, _s0, _h0, _n0, base = compute_places(buns, prod, counts, adjs, sales, cd)
    pl_stock = pl_now if not morning else compute_places(buns, prod, counts, adjs, sales, cd_save)[0]
    show = active_buns(buns, sales, merge_places(pl_now, buns))
    c2.caption("Count each stock and press its 💾 Save. **Each stock is saved by itself** — the others keep their "
               "last count. The sheets start with what the app expects: only change what is different. "
               "Evening: first **🚚 move** what the cooling room needs for tomorrow.")
    if morning:
        c2.info(f"🌅 Morning count of {cd:%d %b}: saved as the stock at the end of **{cd_save:%d %b}**. The sales of "
                f"{cd:%d %b} are taken off it. Count before anything is sold or delivered.")
    morning_count_banner(cfg, can_edit, me, base, "cnt")
    mode = st.radio("Start the sheets from", ["🧮 What the app expects (recommended)", "⬜ Empty sheets"],
                    horizontal=True, key="cnt_mode")
    sections = ["🚚 Move frozen → cooling"] + [place_label(cfg, r) for r in ROLES] + ["📊 All stock"]
    if st.session_state.get("phone_mode"):
        pick = st.radio("Part", sections, key="cnt_part", horizontal=False)
        boxes = {s_: (st.container() if s_ == pick else None) for s_ in sections}
    else:
        tabs = st.tabs(sections)
        boxes = dict(zip(sections, tabs))
    if boxes[sections[0]] is not None:
        with boxes[sections[0]]:
            _move_panel(cfg, can_edit, me, cd, pl_now, sales, buns, names, show)
    counted_all = {}
    for r in ROLES:
        box = boxes[place_label(cfg, r)]
        if box is None:
            continue
        with box:
            counted_all[r] = _count_place(cfg, can_edit, me, r, cd_save, mode, pl_stock, base, show, names, buns)
    if boxes[sections[-1]] is not None:
        with boxes[sections[-1]]:
            rows = []
            for r in ROLES:
                info = base.get(r)
                rows.append({"Stock": place_label(cfg, r), "Now (app)": int(round(sum(sum(v.values()) for v in pl_now[r].values()))),
                             "Last count": f"{info[0]:%d %b} · {info[3][11:16]} · {info[4]}" if info else "never counted"})
            st.dataframe(pd.DataFrame(rows), hide_index=True, width="stretch")
            tot = merge_places(pl_now, show)
            allr = {}
            for b in show:
                for d, v in tot.get(b, {}).items():
                    allr.setdefault(d, {})[b] = round(v)
            st.markdown(excel_html(f"ស្តុកនំសរុប ({cd:%d.%m.%Y}) — all 3 stocks", [(day_label(d), v) for d, v in sorted(allr.items())],
                                   show), unsafe_allow_html=True)
            sheets = {pn[r]: sorted(counted_all.get(r) or [(d, {b: round(v) for b, v in vals.items()}) for d, vals in
                                                             _rows_of(pl_now[r], show)], key=lambda x: x[0]) for r in ROLES}
            st.download_button("📥 Count sheets for printing (Excel, your layout)",
                               data=count_sheet_excel([pn[r] for r in ROLES], sheets, show, cd),
                               file_name=f"Stock_count_{cd:%Y-%m-%d}.xlsx", key="cnt_xlsx",
                               mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    st.divider()
    _adjust_panel(cfg, can_edit, me, adjs, buns, names)


def _fix_count_date(cid, new_cd):
    """Moves one saved count to another count date (e.g. a morning count -> the end of the day before)."""
    def change(df):
        m = df["Count_Id"].astype(str) == str(cid)
        old = df.loc[m, "Count_Date"].astype(str)
        df.loc[m, "Count_Date"] = new_cd.isoformat()
        z = m & (df["Pcs"].map(_num).astype(float) == 0) & (df["Prod_Date"].astype(str).isin(set(old)))
        df.loc[z, "Prod_Date"] = new_cd.isoformat()           # the 0 rows of absent buns follow the count
        return df
    modify_csv(COUNT_FILE, COUNT_COLS, change)


def morning_count_banner(cfg, can_edit, me, base, key):
    """A count saved before noon with today's date was most likely counted BEFORE the day's sales. As the stock at
    the end of that day, that day's sales would never be taken off — ask once, and fix it with one tap."""
    ok_ids = set(cfg.get("count_checked") or [])
    for role in ROLES:
        info = base.get(role)
        if not info:
            continue
        cd, cid, saved = info[0], str(info[2]), str(info[3])
        try:
            sd, hour = date.fromisoformat(saved[:10]), int(saved[11:13])
        except Exception:
            continue
        if sd != cd or hour >= 12 or cid in ok_ids:
            continue
        pn = place_label(cfg, role)
        st.warning(f"🌅 **{pn}** · counted {cd:%d %b} {saved[11:16]} (morning). Counted before the day's sales? Then "
                   f"press 🌅 below: the count becomes the stock at the end of {cd - timedelta(days=1):%d %b}, and "
                   f"the sales of {cd:%d %b} are taken off.")
        if not can_edit:
            continue
        b1, b2 = st.columns(2)
        if b1.button("🌅 Yes — counted before the day's sales (fix)", key=f"{key}_mfix_{role}", type="primary"):
            try:
                _fix_count_date(cid, cd - timedelta(days=1))
                audit("count moved to morning", f"{pn}: {cd:%d %b} {saved[11:16]} -> end of {cd - timedelta(days=1):%d %b}")
                st.session_state["c_flash"] = (f"✅ {pn}: fixed — now the stock at the end of "
                                               f"{cd - timedelta(days=1):%d %b}. The sales of {cd:%d %b} are taken off.")
            except Exception as e:
                st.error(f"⚠️ Not changed: {e}")
                return
            st.rerun()
        if b2.button("🌙 No — it is the stock at the end of the day", key=f"{key}_mok_{role}"):
            try:
                update_settings(lambda c: c.setdefault("count_checked", []).append(cid))
            except Exception:
                pass
            st.rerun()


def _rows_of(stock_role, show):
    """{bun: {date: pcs}} -> [(date, {bun: pcs})]"""
    by = {}
    for b in show:
        for d, v in stock_role.get(b, {}).items():
            if v >= 0.5:
                by.setdefault(d, {})[b] = round(v)
    return sorted(by.items())


def _count_place(cfg, can_edit, me, role, cd, mode, pl_stock, base, show, names, buns):
    """One stock (cooling room / frozen room / AEON): count sheet + check + its own 💾 Save."""
    pn = place_names(cfg)[role]
    n_key = f"cnt_n_{role}"
    n = st.session_state.get(n_key, 0)
    info = base.get(role)
    st.caption(f"{ROLE_ICON[role]} **{ROLE_EN[role]}** · "
               + ("new production comes here · " if role == "frozen" else "")
               + ("only for AEON orders · " if role == "aeon" else "")
               + (f"last count {info[0]:%d %b %Y} {info[3][11:16]} by {info[4]}" if info else "never counted yet"))
    exp = pl_stock[role]
    start = _rows_of(exp, show) if mode.startswith("🧮") else []
    if not any(d == cd for d, _v in start):
        start = start + [(cd, {})]
    if can_edit:
        _upload_count(cfg, role, cd, mode, n, show, names, buns)
    if st.session_state.get("phone_mode"):
        counted = _count_phone([pn], {pn: start}, show, names, cd, f"{role}_{cd}_{mode[:2]}_{n}", single=True)[pn]
    else:
        gk = f"cnt_{role}_{cd}_{mode[:2]}_{n}"
        counted, restored = draft_grid(start, show, gk, max_date=cd)
        if restored:
            st.info("📝 Your count from before is still here — it is NOT saved yet.")
        st.markdown(excel_html(f"{pn} ({cd:%d.%m.%Y})", [(day_label(d), v) for d, v in sorted(counted, key=lambda x: x[0])], show),
                    unsafe_allow_html=True)
    tot_c = {b: sum(v.get(b, 0) for _d, v in counted) for b in show}
    tot_e = {b: sum(exp.get(b, {}).values()) for b in show}
    with st.expander(f"🔍 Check: counted vs what the app expected in {pn}", expanded=False):
        chk = pd.DataFrame([{"Bun": short(b), "App expected": int(round(tot_e[b])), "Counted": int(tot_c[b]),
                             "Difference": int(tot_c[b] - round(tot_e[b]))} for b in show])
        chk.loc[len(chk)] = ["សរុប", int(chk["App expected"].sum()), int(chk["Counted"].sum()), int(chk["Difference"].sum())]
        st.dataframe(chk.style.map(lambda v: "color:#c62828;font-weight:700" if isinstance(v, (int, float)) and v < 0
                                   else ("color:#2e7d32;font-weight:700" if isinstance(v, (int, float)) and v > 0 else ""),
                                   subset=["Difference"]), hide_index=True, width="stretch")
    if not can_edit:
        st.info("👁️ View only — ask Admin for edit access to save a count.")
        return counted
    if info and info[0] == cd:
        st.warning(f"ℹ️ {pn} was already counted for {cd:%d %b} at {info[3][11:16]} by {info[4]}. "
                   "Saving again **replaces** that count.")
    exp_all = sum(tot_e.values())
    big = [b for b in show if abs(tot_c[b] - tot_e[b]) > max(300, 0.15 * tot_e[b])]
    big_total = abs(sum(tot_c.values()) - exp_all) > max(500, 0.03 * exp_all)
    ok_big = True
    if big or big_total:
        st.warning("⚠️ Big difference from what the app expected: " + ", ".join(
            f"{short(b)} {int(tot_c[b] - round(tot_e[b])):+,}" for b in big[:8])
            + (f" · total {int(sum(tot_c.values()) - round(exp_all)):+,} pcs" if big_total else "")
            + ". Check once more (a missing date? a typo? buns moved without 🚚?).")
        ok_big = st.checkbox("✔️ I checked these numbers — they are right", key=f"cnt_ok_{role}_{n}")
    clicked = st.button(f"💾 Save {ROLE_ICON[role]} {pn} ({int(sum(tot_c.values())):,} pcs)", type="primary",
                        key=f"cnt_save_{role}", disabled=not ok_big, width="stretch")
    undo_bar(f"count_{role}", "c_flash")
    if clicked:
        sig = json.dumps([role, cd.isoformat(), [(d.isoformat(), sorted(v.items())) for d, v in sorted(counted, key=lambda x: x[0])]])
        if not save_guard(f"count_{role}", sig):
            st.info("✅ Already saved a moment ago — it is not saved twice.")
            st.toast("✅ Already saved a moment ago — not saved twice.")
            return counted
        cid, stamp = uuid.uuid4().hex[:10], now_kh().strftime("%Y-%m-%d %H:%M:%S")
        new = [{"Saved_At": stamp, "Count_Date": cd.isoformat(), "Bun": b, "Prod_Date": d.isoformat(), "Pcs": str(int(q)),
                "By": me, "Count_Id": cid, "Place": pn, "Kind": role}
               for d, v in counted for b, q in v.items() if q]
        have = {r_["Bun"] for r_ in new}
        new += [{"Saved_At": stamp, "Count_Date": cd.isoformat(), "Bun": b, "Prod_Date": cd.isoformat(), "Pcs": "0",
                 "By": me, "Count_Id": cid, "Place": pn, "Kind": role} for b in buns if b not in have]   # counted: none
        try:
            modify_csv(COUNT_FILE, COUNT_COLS, lambda df: pd.concat([df, pd.DataFrame(new)], ignore_index=True))
            audit("count saved", f"{pn} {cd:%d %b %Y}: {int(sum(tot_c.values())):,} pcs · " + ", ".join(
                f"{short(b)} {int(tot_c[b])} ({int(tot_c[b] - round(tot_e[b])):+d})" for b in show if tot_c[b] or tot_e[b]))
            label = f"{pn} {cd:%d %b} · {int(sum(tot_c.values())):,} pcs"
            remember_undo(f"count_{role}", COUNT_FILE, COUNT_COLS, "Count_Id", cid, label)
            st.session_state["c_flash"] = f"✅ Saved: {label}"
            drop_draft(f"cnt_{role}_{cd}_{mode[:2]}_{n}")
            st.session_state[n_key] = n + 1
            _rerun_here()
        except Exception as e:
            st.session_state.pop(f"_sig_count_{role}", None)
            st.error(f"Not saved: {e}")
            st.toast(f"⚠️ Not saved: {e}"[:140])
    return counted


def frozen_space(cfg, frozen_crates, speed, buns, plan=None):
    """Free places in the frozen room for one day of new production (`daily_in_pcs`, split over the buns like the
    sales). Each bun has its own lanes, so it is checked bun by bun: the free places at the back of the bun's lanes
    must take its share. frozen_crates = {bun: [crates] (1 stack = 1 date) or a number of crates} (not the AEON line)."""
    rooms, cr = rooms_of(cfg), crate_size(cfg)
    room = rooms[1] if len(rooms) > 1 else rooms[0]
    g = room_geom(room, cr)
    plan = plan or room_plan(cfg, g, buns, speed)
    high = g["high"]
    per, daily = daily_need(cfg, buns, speed, high)
    used_by, need_by = {}, {}
    for b in buns:
        k = plan["key_of"].get(b)
        if k is None:
            continue
        used_by[k] = used_by.get(k, 0) + n_places(frozen_crates.get(b, 0), high)
        if per.get(b, 0) > 0:                               # tomorrow's production: its own stacks per bun
            need_by[k] = need_by.get(k, 0) + math.ceil(per[b] / high)
    slots = {k: len(lane_slots(plan, k)) for k in dict.fromkeys(ln["key"] for ln in plan["lanes"] if ln.get("key"))}
    for k in slots:
        used_by.setdefault(k, 0)
    used_by = {k: v for k, v in used_by.items() if k in slots}
    need_by = {k: v for k, v in need_by.items() if k in slots}
    free_by = {k: max(0, slots[k] - used_by[k]) for k in slots}
    short_by = {k: need_by[k] - free_by[k] for k in need_by if need_by[k] > free_by[k]}
    free, need = sum(free_by.values()), sum(need_by.values())
    crates_day = sum(per.values()) or 1e-9
    avg_cp = daily / crates_day if daily > 0 else 60
    return {"room": room["name"], "places": sum(slots.values()), "used": sum(used_by.values()), "free": free,
            "need": need, "high": high, "daily": daily, "free_pcs": int(free * high * avg_cp), "ok": not short_by,
            "need_by": need_by, "free_by": free_by, "short_by": short_by}


def move_suggestion(cfg, pl_stock, sales, buns, day):
    """What to move this evening from the frozen room to the cooling room, in WHOLE CRATES (oldest production date
    first), so the cooling room holds the next `cool_days` days of sales — never more than each bun's own lanes in
    the cooling room can take — and so the frozen room has space at the back of every bun's lanes for tomorrow."""
    days = max(1, int(float(cfg.get("cool_days") or 1)))
    fc = forecast(sales, buns, day + timedelta(days=1), days, int(cfg["lookback_days"]))
    speed, _n = sales_speed(sales, buns, day + timedelta(days=1), int(cfg["lookback_days"]))
    rooms, cr = rooms_of(cfg), crate_size(cfg)
    g = room_geom(rooms[0], cr)
    plan = room_plan(cfg, g, buns, speed)
    frz_room = rooms[1] if len(rooms) > 1 else rooms[0]
    fplan = room_plan(cfg, room_geom(frz_room, cr), buns, speed)
    info = {}
    for b in buns:
        cp = crate_pcs(cfg, b)
        need = sum(fc.get((day + timedelta(days=i + 1), b), 0) for i in range(days))
        cool = sum(pl_stock["cool"].get(b, {}).values())
        fr_crates = bun_crates(cfg, b, {b: pl_stock["frozen"].get(b, {})})        # oldest first
        cool_list = bun_crates(cfg, b, {b: pl_stock["cool"].get(b, {})})
        cool_crates = len(cool_list)
        want = math.ceil(max(0.0, need - cool) / cp)
        info[b] = {"need": need, "cool": cool, "frozen": sum(x[1] for x in fr_crates), "cp": cp,
                   "fr_crates": fr_crates, "cool_crates": cool_crates, "cool_list": cool_list,
                   "crates": min(want, len(fr_crates)),
                   "want": want, "lane": lane_label(plan["key_of"].get(b))}
    cap = {k: len(lane_slots(plan, k)) for k in                  # places (stacks) of each lane group
           dict.fromkeys(ln["key"] for ln in plan["lanes"] if ln.get("key"))}

    def bun_places(mv, b):                                   # 1 stack = 1 date
        return n_places(info[b]["cool_list"] + info[b]["fr_crates"][:mv[b]], g["high"])

    def lane_places(mv, k):
        return sum(bun_places(mv, b) for b in info if plan["key_of"].get(b) == k)

    def fits(mv, b):
        k = plan["key_of"].get(b)
        if k is None:
            return False
        return lane_places(mv, k) <= max(cap.get(k, 0), lane_places({x: 0 for x in mv}, k))

    def stacks_after(mv):
        return sum(lane_places(mv, k) for k in cap)
    mv = {b: v["crates"] for b, v in info.items()}
    capped = []
    for b in info:                                          # each bun: only what its cooling lanes can take
        while mv[b] > 0 and not fits(mv, b):
            mv[b] -= 1
            if b not in capped:
                capped.append(b)
    # 📥 the frozen room must keep space at the back of every bun's lanes: move more old crates if needed
    extra = {b: 0 for b in info}

    def frz_after():
        return {b: info[b]["fr_crates"][mv[b]:] for b in info}
    sp = frozen_space(cfg, frz_after(), speed, buns, plan=fplan)
    for _ in range(500):
        if sp["ok"]:
            break
        best = None
        for k in sp["short_by"]:
            for b in info:
                if fplan["key_of"].get(b) != k:
                    continue
                left = len(info[b]["fr_crates"]) - mv[b]
                if left <= 0:
                    continue
                n = len(date_stacks(info[b]["fr_crates"][mv[b]:], sp["high"])[0])   # its oldest stack
                mv[b] += n
                ok = fits(mv, b)
                mv[b] -= n
                if ok and (best is None or n < best[1]):
                    best = (b, n)
        if best is None:
            break                                          # the cooling lanes are full too
        mv[best[0]] += best[1]
        extra[best[0]] += best[1]
        sp = frozen_space(cfg, frz_after(), speed, buns, plan=fplan)
    for b, v in info.items():
        v["crates"] = mv[b]
        v["extra"] = extra[b]
    room = {"places": sum(cap.values()), "high": g["high"], "before": stacks_after({b: 0 for b in info}),
            "after": stacks_after(mv), "capped": capped, "name": rooms[0]["name"], "frozen": sp, "plan": plan,
            "speed": speed, "fplan": fplan, "fname": frz_room["name"], "fgeom": room_geom(frz_room, cr)}
    return info, days, room


def _take_crates(fr_crates, k):
    """The first k crates (oldest first) -> {prod_date: pcs}."""
    out = {}
    for d, n in fr_crates[:max(0, int(k))]:
        out[d] = out.get(d, 0) + n
    return out


def _move_panel(cfg, can_edit, me, cd, pl_stock, sales, buns, names, show):
    pn = place_names(cfg)
    t = today_kh()
    if cd != t:
        st.info("🚚 Moves are made for today's evening — choose today's date above.")
        return
    info, days, room = move_suggestion(cfg, pl_stock, sales, buns, t)
    moves, _r = read_csv(MOVE_FILE, MOVE_COLS)
    done_today = moves[moves["Date"] == t.isoformat()] if not moves.empty else moves
    st.markdown(f"**🚚 Move from {ROLE_ICON['frozen']} {pn['frozen']} to {ROLE_ICON['cool']} {pn['cool']}** — the app "
                f"suggests it by itself: enough for **{days} day{'s' if days > 1 else ''}** of sales (tomorrow"
                + (f" + {days - 1} more" if days > 1 else "") + "), **whole crates, oldest production date first**.")
    if len(done_today):
        st.success("✅ Already moved today: " + ", ".join(
            f"{short(b)} {int(g_['Pcs'].map(_num).astype(float).sum()):,}" for b, g_ in done_today.groupby("Bun"))
            + " pcs — the list below already counts them.")
    sp = room["frozen"]
    if sp["daily"]:
        msg = (f"📥 After this move the frozen room has **{sp['free']} free stacks (≈ {sp['free_pcs']:,} pcs)** for "
               f"tomorrow's production — needed: **{sp['need']} stacks for {int(sp['daily']):,} pcs**.")
        (st.success if sp["ok"] else st.error)(msg + ("" if sp["ok"] else " ⚠️ Not enough even after moving for: "
                                                     + ", ".join(f"{lane_label(k)} −{n}" for k, n in sp["short_by"].items())
                                                     + " stacks — their cooling lanes are full too: produce less of "
                                                       "these tomorrow, or sell / move stock elsewhere."))
        if any(v.get("extra") for v in info.values()):
            st.caption("🚚 includes extra old crates moved only to make room for tomorrow's production: " + ", ".join(
                f"{short(b)} +{v['extra']}" for b, v in info.items() if v.get("extra")))
    if room["capped"]:
        st.warning("⚠️ Their cooling lanes are full — the list was made smaller so the crates fit: "
                   + ", ".join(short(b) for b in room["capped"]) + ".")
    rows = []
    for b, v in info.items():
        if not (b in show or v["crates"]):
            continue
        took = _take_crates(v["fr_crates"], v["crates"])
        rows.append({"Bun": b, "Name": names.get(b, ""), "Lane": v["lane"], "❄️ Cooling now (pcs)": int(round(v["cool"])),
                     "Needed (pcs)": int(round(v["need"])), "🧊 Frozen now (pcs)": int(round(v["frozen"])),
                     "🚚 Move (crates)": int(v["crates"]), "= pcs": int(round(sum(took.values()))),
                     "Pcs / crate": v["cp"],
                     "Take these dates": ", ".join(f"{d:%d/%m}×{sum(1 for x in v['fr_crates'][:v['crates']] if x[0] == d)}"
                                                   for d in sorted(took))})
    df = pd.DataFrame(rows)
    n = st.session_state.get("mv_n", 0)
    ed = st.data_editor(df, hide_index=True, width="stretch", key=f"mv_{n}",
                        disabled=[c for c in df.columns if c != "🚚 Move (crates)"],
                        column_config={"🚚 Move (crates)": st.column_config.NumberColumn(
                            "🚚 Move (crates)", min_value=0, step=1, help="Change it if you moved a different number of crates"),
                            "= pcs": st.column_config.NumberColumn("= pcs (suggested)")})
    mv = {r["Bun"]: max(0, min(int(r["🚚 Move (crates)"] or 0), len(info[r["Bun"]]["fr_crates"])))
          for r in ed.to_dict("records")}
    took = {b: _take_crates(info[b]["fr_crates"], k) for b, k in mv.items() if k}
    tot_pcs = int(round(sum(sum(x.values()) for x in took.values())))
    tot_cr = sum(mv.values())
    if tot_cr:
        st.markdown(f"### 🚚 Move **{tot_cr:,} crates = {tot_pcs:,} pcs**")
        st.caption(" · ".join(f"{short(b)} {k} crates ({int(round(sum(took[b].values()))):,} pcs)" for b, k in mv.items() if k))
    else:
        st.markdown("✅ Nothing to move — the cooling room already has enough for tomorrow.")
    over = [b for b, k in ed.set_index("Bun")["🚚 Move (crates)"].items() if int(k or 0) > len(info[b]["fr_crates"])]
    if over:
        st.warning("⚠️ More crates than the frozen room has: " + ", ".join(short(b) for b in over)
                   + " — only what the frozen room has is counted. Count the frozen room?")

    # 🗺️ where to put them: the cooling room after the move (your sheet layout)
    rooms, cr = rooms_of(cfg), crate_size(cfg)
    g = room_geom(rooms[0], cr)
    cool_after = {b: dict(pl_stock["cool"].get(b, {})) for b in buns}
    for b, add in took.items():
        for d, q in add.items():
            cool_after[b][d] = cool_after[b].get(d, 0) + q
    lists = {b: bun_crates(cfg, b, cool_after) for b in buns}
    stacks, overflow, _l, _f = room_fill(cfg, g, {b: v for b, v in lists.items() if v}, room["plan"])
    new_marks, put_by, rotate = {}, {}, {}
    for b, k in mv.items():                 # where the moved crates sit in the bun's own lanes (by their date)
        if not k:
            continue
        moved = info[b]["fr_crates"][:k]
        m_by = {}
        for d, _q in moved:
            m_by[d] = m_by.get(d, 0) + 1
        old_dates = [d for d, _q in info[b]["cool_list"]]
        if old_dates and min(m_by) < max(old_dates):      # older than what is in the cooling room already
            rotate[b] = (min(m_by), max(old_dates))
        for s_ in sorted([x for x in stacks if x["b"] == b], key=lambda x: -x.get("i", 0)):
            d = min(y[0] for y in s_["segs"])
            q = min(m_by.get(d, 0), sum(y[1] for y in s_["segs"]))
            if q > 0:
                m_by[d] -= q
                new_marks[(s_["r"], s_["c"])] = new_marks.get((s_["r"], s_["c"]), 0) + q
                ln, _pos = stack_where(room["plan"], s_["c"], s_["r"])
                put_by.setdefault(b, {})[ln] = put_by.setdefault(b, {}).get(ln, 0) + q
    # 🧊 where to take them: the frozen room before the move, oldest stacks (the fronts) first
    fg, fplan = room["fgeom"], room["fplan"]
    flists = {b: bun_crates(cfg, b, {b: pl_stock["frozen"].get(b, {})}) for b in buns}
    fstacks, _fo, _fl, _ff = room_fill(cfg, fg, {b: v for b, v in flists.items() if v}, fplan)
    take_marks, take_by = {}, {}
    for b, k in mv.items():
        left = k
        for s_ in take_order(fplan, fstacks, b):
            if left <= 0:
                break
            q = min(left, sum(y[1] for y in s_["segs"]))
            take_marks[(s_["r"], s_["c"])] = q
            ln, _pos = stack_where(fplan, s_["c"], s_["r"])
            take_by.setdefault(b, {})[ln] = take_by.setdefault(b, {}).get(ln, 0) + q
            left -= q
    if tot_cr:
        st.markdown("#### 🚚 Step by step — take from the FRONT, push in at the BACK")
        steps = []
        for b in sorted([b for b in mv if mv[b]], key=lambda x: min([k for k in take_by.get(x, {}) if k] or [99])):
            fr = ", ".join(f"L{ln} ×{q}" if ln else f"⚠️ other place ×{q}" for ln, q in sorted(
                take_by.get(b, {}).items(), key=lambda x: x[0] or 99))
            to = ", ".join(f"L{ln} ×{q}" if ln else f"⚠️ no lane ×{q}" for ln, q in sorted(
                put_by.get(b, {}).items(), key=lambda x: x[0] or 99))
            if b in rotate:
                dst = (f"⚠️ these ({rotate[b][0]:%d/%m}) are OLDER than the {rotate[b][1]:%d/%m} crates already in "
                       f"**{to or '–'}**: take that lane out, put these in where 🆕 shows (oldest at the FRONT), "
                       f"push the rest back in behind")
            else:
                dst = f"push in at the back of **{to or '–'}**"
            steps.append(f"{len(steps) + 1}. **{b}** {names.get(b, '')} · **{mv[b]} crates** — 🧊 {room['fname']}: "
                         f"take from the front of **{fr or '–'}** → ❄️ {rooms[0]['name']}: {dst}")
        st.markdown("\n".join(steps))
        if rotate:
            st.warning("🔄 Today the frozen room has **older** bread than the cooling room for: "
                       + ", ".join(rotate) + ". FIFO = oldest out first, so these lanes must be re-stacked once "
                       "(oldest at the front). When the old stock is used up, the moved crates are always the newest "
                       "and just go in at the back.")
        st.caption("L = lane, counted from the left of the room (the lane names are on the maps). Do one bun at a "
                   "time; never put a bun in another bun's lane.")
    with st.expander(f"🧊 {room['fname']} now — where to take the crates", expanded=False):
        st.caption("**🚚 = take this many crates** — the oldest, at the FRONT of the bun's lanes.")
        html_f, _t = room_sheet_html({"name": room["fname"], "door_in": "", "door_out": "front"}, fg, fstacks, names,
                                     take=take_marks, plan=fplan)
        st.markdown(html_f, unsafe_allow_html=True)
    with st.expander(f"🗺️ {rooms[0]['name']} after the move — where to put the crates", expanded=bool(tot_cr)):
        st.caption("**🆕 = put the moved crates here** (normally at the BACK of the bun's own lane; 🔄 = older crates: "
                   "at the front). The oldest crates are always at the "
                   "FRONT (⭐ = take first). Every bun always has the same lane — the name is under each column. "
                   f"Places used: {room['before']} → **{len(stacks)}** of {g['places']} stacks.")
        if overflow:
            st.warning("⚠️ No place for: " + ", ".join(f"{short(b)} {q} crates" for b, q in overflow.items())
                       + " — move fewer crates.")
        html, _tot = room_sheet_html(rooms[0], g, stacks, names, new=new_marks, plan=room["plan"])
        st.markdown(html, unsafe_allow_html=True)
        st.download_button("⬇️ This map (Excel)", room_sheet_excel(rooms[0], g, stacks, plan=room["plan"]),
                           file_name=f"cooling_room_after_move_{t}.xlsx", key="mv_map_xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    if not can_edit:
        return
    clicked = st.button(f"✅ We moved these — save ({tot_cr:,} crates · {tot_pcs:,} pcs)", type="primary",
                        key="mv_save", disabled=not tot_cr, width="stretch")
    undo_bar("move", "c_flash")
    if clicked:
        if not save_guard("move", json.dumps(sorted(mv.items()))):
            st.info("✅ Already saved a moment ago — it is not saved twice.")
            return
        mid, stamp = uuid.uuid4().hex[:10], now_kh().strftime("%Y-%m-%d %H:%M:%S")
        new = [{"Saved_At": stamp, "Date": t.isoformat(), "Bun": b, "Prod_Date": d.isoformat(), "Pcs": str(int(round(q))),
                "From": "frozen", "To": "cool", "By": me, "Move_Id": mid}
               for b, add in took.items() for d, q in sorted(add.items()) if q >= 0.5]
        try:
            modify_csv(MOVE_FILE, MOVE_COLS, lambda df_: pd.concat([df_, pd.DataFrame(new)], ignore_index=True))
            label = f"moved {tot_cr:,} crates ({tot_pcs:,} pcs) frozen → cooling"
            audit("move saved", label + " · " + ", ".join(f"{short(b)} {k} cr" for b, k in mv.items() if k))
            remember_undo("move", MOVE_FILE, MOVE_COLS, "Move_Id", mid, label)
            st.session_state["c_flash"] = f"✅ Saved: {label}"
            st.session_state["mv_n"] = n + 1
            _rerun_here()
        except Exception as e:
            st.session_state.pop("_sig_move", None)
            st.error(f"Not saved: {e}")


def _adjust_panel(cfg, can_edit, me, adjs, buns, names):
    pn = place_names(cfg)
    st.markdown("**➕➖ Adjustment** — buns that leave or enter stock without a sale invoice "
                "(damaged, samples, staff meals, returned...).")
    if can_edit:
        with st.form("adj_form", clear_on_submit=True):
            c1, c2, c3, c4 = st.columns([1.3, 1, 1, 1.4])
            b = c1.selectbox("Bun", [bun_label(x, names) for x in buns])
            kind = c2.radio("Type", ["➖ Remove", "➕ Add"], horizontal=False)
            n = c3.number_input("Pcs", min_value=1, max_value=100000, step=10)
            d = c4.date_input("Date", value=today_kh(), max_value=today_kh())
            c5, c6, c7 = st.columns([1, 1, 1.4])
            place = c5.selectbox("Stock", [""] + ROLES, format_func=lambda r: "Auto (cooling first)" if not r
                                 else f"{ROLE_ICON[r]} {pn[r]}")
            pdte = c6.date_input("Batch production date (optional)", value=None)
            reason = c7.selectbox("Reason", ["Damaged / broken", "Expired / old", "Sample / FOC not in journal",
                                             "Staff meal", "Returned by customer", "Other"])
            ok = st.form_submit_button("💾 Save adjustment")
        if ok:
            code = {bun_label(x, names): x for x in buns}[b]
            row = {"Saved_At": now_kh().strftime("%Y-%m-%d %H:%M:%S"), "Date": d.isoformat(), "Bun": code,
                   "Prod_Date": pdte.isoformat() if pdte else "", "Pcs": str(int(n if kind.startswith("➕") else -n)),
                   "Reason": reason, "By": me, "Adj_Id": uuid.uuid4().hex[:10], "Place": place}
            if not save_guard("adjustment", json.dumps([row["Date"], code, row["Pcs"], reason, place])):
                st.info("✅ This adjustment was already saved a moment ago — it is not saved twice.")
            else:
                try:
                    modify_csv(ADJ_FILE, ADJ_COLS, lambda df: pd.concat([df, pd.DataFrame([row])], ignore_index=True))
                    audit("adjustment", f"{row['Date']} {short(code)} {row['Pcs']} pcs · {reason}"
                          + (f" · {pn[place]}" if place else ""))
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
    # ✏️ your own sales / day per bun and the daily maximum (saved in the settings)
    if not cfg.get("max_prod_per_day") and not cfg.get("max_prod_set"):    # old settings files saved 0 = no limit
        cfg = {**cfg, "max_prod_per_day": DEFAULT_SETTINGS["max_prod_per_day"]}
    sp, _n = sales_speed(sales, buns, t, int(cfg["lookback_days"]))
    own = own_sales_editor(cfg, can_edit, names, buns, sales, t, stock_now, "plan", with_cap=True)
    plan = plan_production(buns, stock_now, fc, start, days, cfg)
    if own:
        st.info("✏️ Planned with **your sales / day** for: " + ", ".join(f"{b} {int(v):,}" for b, v in own.items()))
    if cfg.get("max_prod_per_day"):
        st.caption(f"🏭 At most **{int(cfg['max_prod_per_day']):,} pcs** a day. When it is not enough, every bun first "
                   "gets enough not to run out before it is made again; the rest is shared so all buns come closer to "
                   "their target at the same pace.")
    if no_count:
        st.warning("No stock count yet for " + ", ".join(no_count) + " — the plan treats their stock as 0.")
    dates = [start + timedelta(days=i) for i in range(days)]
    piv = plan.pivot_table(index="Bun", columns="Date", values="Produce", aggfunc="sum").reindex(buns)
    piv.columns = [f"{EN_DAYS[d.weekday()]} {d:%d/%m}" for d in piv.columns]
    piv.insert(0, "Bun", [names.get(b, "") for b in piv.index])
    piv["TOTAL"] = piv.drop(columns=["Bun"]).sum(axis=1)
    last = plan[plan["Date"] == dates[-1]].set_index("Bun")
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
        st.markdown("#### 🧊 The 3 stocks (each counted and saved by itself)")
        pn_now = place_names(cfg)
        pc = st.columns(4)
        new_pn = {r: pc[i].text_input(f"{ROLE_ICON[r]} {ROLE_EN[r]}", value=pn_now[r], key=f"set_pn_{r}").strip()
                  or DEFAULT_PLACE_NAMES[r] for i, r in enumerate(ROLES)}
        cool_days = pc[3].number_input("❄️ Cooling room keeps (days of sales)", min_value=1, max_value=7,
                                       value=int(float(cfg.get("cool_days") or 1)), key="set_cool_days",
                                       help="The evening 🚚 move list fills the cooling room up to this many days.")
        daily_in = st.number_input("🧊 Frozen room keeps space for new production (pcs per day)", min_value=0,
                                   max_value=200000, step=1000, value=int(cfg.get("daily_in_pcs", 16000) or 0),
                                   key="set_daily_in", help="Checked every day; the 🚚 move list frees space when needed.")
        st.caption("New production goes to 🧊 the frozen room. Orders from customers with “AEON” in the name are taken "
                   "from 🛒 the AEON stock (when it is empty: from the normal stock). Other orders: ❄️ cooling room "
                   "first, then 🧊 frozen room.")

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
                       round_to=int(rnd), max_prod_per_day=int(capp), max_prod_set=True, priority=list(prio),
                       place_names=new_pn, cool_days=int(cool_days), daily_in_pcs=int(daily_in),
                       # every bun saved with its own value: exactly what the table shows is what the app uses
                       target_days={r["Bun"]: int(r["Target days"]) for r in rows},
                       shelf_by_bun={r["Bun"]: int(r["Shelf life (days)"]) for r in rows},
                       prod_days={r["Bun"]: [i for i in range(7) if r[EN_DAYS[i]]] for r in rows},
                       access_by_role=new_by_role, **room_vals, **task_vals)
        st.session_state.pop("set_lane_auto_on", None)
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
DEFAULT_ROOMS = [{"name": "❄️ Cooling room", "cols": 9, "rows": 8, "high": 15, "blocked": "1:5-8=Cooling fan; 1:9",
                  "door_in": "right-back", "door_out": "front-middle", "h": 3.0},
                 {"name": "🧊 Freezer room", "cols": 9, "rows": 9, "high": 15, "blocked": "",
                  "door_in": "front-middle", "door_out": "front-middle", "h": 3.0, "back_m": 1.6, "aeon_rows": 11,
                  "aisle_m": 0.5}]
RAW_LABEL = "Raw material"                                 # the empty space kept at the back of a room
WALK_LABEL = "🚶 Walkway"                                  # kept free between the frozen lanes and the AEON line
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
    for i, r in enumerate(cfg.get("rooms") or DEFAULT_ROOMS):
        try:
            if "cols" not in r:                                  # an older room format: use the defaults
                continue
            back = r.get("back_m")
            back = (1.6 if i == 1 else 0.0) if back is None or back == "" else max(0.0, float(back))
            arows = r.get("aeon_rows")
            arows = (11 if i == 1 else 0) if arows is None or arows == "" else max(0, int(float(arows)))
            high = max(1, int(r.get("high") or 15))
            a_high = max(1, int(float(r.get("aeon_high") or high)))
            aisle = r.get("aisle_m")
            aisle = (0.5 if i == 1 else 0.0) if aisle is None or aisle == "" else max(0.0, float(aisle))
            out.append({"name": str(r["name"]).strip(), "cols": max(1, int(r["cols"])), "rows": max(1, int(r["rows"])),
                        "high": high, "aeon_high": a_high, "blocked": str(r.get("blocked") or ""),
                        "door_in": r.get("door_in") if r.get("door_in") in DOOR_SPOTS else "back-middle",
                        "door_out": r.get("door_out") if r.get("door_out") in DOOR_SPOTS else "front-middle",
                        "h": float(r.get("h") or 3.0), "back_m": back, "aeon_rows": arows, "aisle_m": aisle})
        except Exception:
            continue
    return [r for r in out if r["name"]] or [dict(x) for x in DEFAULT_ROOMS]


def crate_size(cfg):
    c = {**DEFAULT_CRATE, **(cfg.get("crate") or {})}
    return {k: max(5.0, float(c[k])) / 100 for k in ("w", "l", "h")}       # metres


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
    back_rows = min(room["rows"], math.ceil(round(float(room.get("back_m") or 0) / (cr["l"] + GRID_GAP), 6)))
    arows = int(room.get("aeon_rows") or 0) if room["cols"] > 1 else 0
    for r in range(back_rows):                                 # kept empty at the back (row 1 = back)
        for c in range(room["cols"] - (1 if arows else 0)):    # (the turned AEON line runs the whole wall)
            blocked.setdefault((r, c), RAW_LABEL)
    walk_cols = []
    if arows and float(room.get("aisle_m") or 0) > 0 and room["cols"] > 2:
        n_walk = max(1, int(round(float(room["aisle_m"]) / (cr["w"] + GRID_GAP))))   # whole columns
        walk_cols = list(range(max(0, room["cols"] - 1 - n_walk), room["cols"] - 1))
        for c in walk_cols:                                    # 🚶 free from the door to the back, next to AEON
            for r in range(room["rows"]):
                blocked[(r, c)] = WALK_LABEL
    fit = int((room["h"] - 0.15) // cr["h"])                  # crates that fit under the ceiling
    high = max(1, min(room["high"], fit))
    a_high = max(1, min(int(room.get("aeon_high") or room["high"]), fit)) if arows else high
    if arows:   # the right-hand line = the AEON line with turned crates: its own number of places
        places = sum(1 for r in range(room["rows"]) for c in range(room["cols"] - 1) if (r, c) not in blocked) + arows
    else:
        places = room["rows"] * room["cols"] - len(blocked)
    return {"name": room["name"], "cols": room["cols"], "rows": room["rows"], "high": high, "places": places,
            "capacity": (places - arows) * high + arows * a_high,
            "blocked": blocked, "back_rows": back_rows, "aeon_rows": arows, "aeon_high": a_high,
            "walk_cols": walk_cols, "walk_m": round(len(walk_cols) * (cr["w"] + GRID_GAP), 2),
            "w": round((room["cols"] - (1 if arows else 0)) * (cr["w"] + GRID_GAP) + ((cr["l"] + GRID_GAP) if arows else 0), 2),
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


def lane_label(k):
    """Lane key -> name: 'N1' · '🧺 N22 · N23' (small buns sharing one lane) · '— spare'."""
    k = str(k or "")
    if not k:
        return "— spare"
    return ("🧺 " + " · ".join(k.split("+"))) if "+" in k else k


def lane_members(k):
    return [x for x in str(k or "").split("+") if x]


def lane_cols(g):
    """The normal lanes of a room (one column = one lane, the AEON line not included). Staff take only from the
    FRONT (OUT side) and push new crates in at the BACK, so each lane lists its places front first."""
    last = g["cols"] - 1 if g.get("aeon_rows") else None
    out = []
    for c in range(g["cols"]):
        if c == last:
            continue
        rows = [r for r in range(g["rows"] - 1, -1, -1) if (r, c) not in g["blocked"]]
        if rows:
            out.append({"c": c, "rows": rows})
    return out


def auto_lanes(cfg, g, buns, speed):
    """1 lane = 1 bun, fixed. Lanes per bun follow its sales (crates per day). Buns too small for a lane of their
    own share a 🧺 lane (2–3 fixed buns per lane). Lanes go left → right in the Admin bun order (🧺 last)."""
    lanes = lane_cols(g)
    n = len(lanes)
    if not n:
        return []
    w = {b: max(float(speed.get(b, 0) or 0), 0.0) / crate_pcs(cfg, b) for b in buns}
    act = sorted([b for b in buns if w[b] > 0], key=lambda b: (-w[b], room_order(cfg, b)))
    if not act:                                            # no sales yet: every bun the same
        act, w = list(buns), {b: 1.0 for b in buns}
    tot = sum(w[b] for b in act) or 1.0
    own = [b for b in act if w[b] / tot * n >= 0.75]      # sells enough to fill most of a lane
    mix = [b for b in act if b not in own]
    if len(mix) == 1 and len(own) < n:                     # one small bun alone: it can have its own lane
        own, mix = own + mix, []
    while own and len(own) + (1 if mix else 0) > n:        # more buns than lanes: the smallest share 🧺
        mix.insert(0, own.pop())
    ents = {b: w[b] for b in own}
    if mix:
        ents["+"] = sum(w[b] for b in mix) or 0.01
    cnt = {e: 1 for e in ents}
    for _ in range(n - len(ents)):                         # the other lanes: biggest sellers get more (D'Hondt)
        e = max(ents, key=lambda x: ents[x] / (cnt[x] + 1) if x != "+" or cnt[x] < len(mix) else -1)
        cnt[e] += 1
    keys = [e for e in sorted(own, key=lambda e: (room_order(cfg, e), e)) for _ in range(cnt[e])]
    if mix:                                                # 🧺 lanes: share the small buns out, ~same sales each
        m = cnt["+"]
        groups = [[] for _ in range(m)]
        load = [0.0] * m
        for b in mix:                                      # biggest first, into the lightest lane
            i = min(range(m), key=lambda j: (load[j], len(groups[j])))
            groups[i].append(b)
            load[i] += w[b]
        groups = [sorted(x, key=lambda b: (room_order(cfg, b), b)) for x in groups if x]
        groups.sort(key=lambda x: room_order(cfg, x[0]))
        keys += ["+".join(x) for x in groups]
    return (keys + [""] * n)[:n]


def room_plan(cfg, g, buns, speed):
    """The fixed lane plan of a room: saved by Admin (📐) or automatic from sales.
    -> {"lanes": [{"c", "rows", "key"}], "key_of": {bun: lane key}, "saved": bool}"""
    lanes = lane_cols(g)
    saved = ((cfg.get("lanes") or {}).get(g.get("name", "")) or [])
    ok = isinstance(saved, list) and len(saved) == len(lanes) and any(saved)
    canon = {str(b).upper(): b for b in buns}
    keys = (["+".join(dict.fromkeys(canon.get(p_.strip().upper(), p_.strip()) for p_ in str(x or "").split("+")
                                    if p_.strip())) for x in saved] if ok else auto_lanes(cfg, g, buns, speed))
    for ln, k in zip(lanes, keys):
        ln["key"] = k
    key_of = {}
    for k in keys:
        for b in lane_members(k):
            key_of.setdefault(b, k)
    return {"lanes": lanes, "key_of": {b: key_of.get(b) for b in set(buns) | set(key_of)}, "saved": ok}


def lane_slots(plan, key):
    """The places of one bun (or 🧺), oldest first: the FRONT place of each of its lanes, then the next row …
    so every lane of the bun shows its oldest crates at the front, and new crates go to the back."""
    mine = [ln for ln in plan["lanes"] if ln.get("key") == key]
    out, depth = [], 0
    while any(depth < len(ln["rows"]) for ln in mine):
        out += [(ln["c"], ln["rows"][depth]) for ln in mine if depth < len(ln["rows"])]
        depth += 1
    return out


def _stack(part, bun=None):
    segs = []
    for x in reversed(part):                              # bottom = newer, top = older (taken first)
        d, q, b2 = (x[1], x[2], x[0]) if bun is None else (x[0], x[1], None)
        if segs and segs[-1][0] == d and (b2 is None or segs[-1][3] == b2):
            segs[-1][1] += 1
            segs[-1][2] += q
        else:
            segs.append([d, 1, q] + ([b2] if b2 is not None else []))
    return segs


def date_stacks(crates, high):
    """1 stack = 1 production date: [(date, pcs) crates, oldest first] -> stacks, each a list of crates of ONE date
    (a date with more crates than one stack fills 2+ stacks; the last one can be lower)."""
    by = {}
    for d, q in crates:
        by.setdefault(d, []).append((d, q))
    out = []
    for d in sorted(by):
        cr_d = by[d]
        out += [cr_d[i:i + high] for i in range(0, len(cr_d), high)]
    return out


def n_places(crates, high):
    return len(date_stacks(crates, high)) if isinstance(crates, list) else -(-max(0, int(crates or 0)) // high)


def lane_fill(cfg, g, plan, lists, high=None):
    """Put every bun in ITS OWN lanes (front = oldest). -> (stacks, left {bun: [crates that did not fit, newest]},
    free {key: [free places, back side]})"""
    high = high or g["high"]
    stacks, left, free = [], {}, {}
    groups = {}
    for b in sorted(lists, key=lambda x: (room_order(cfg, x), x)):
        if lists[b]:
            k = plan["key_of"].get(b)
            if k is None:
                left[b] = list(lists[b])
            else:
                groups.setdefault(k, []).append(b)
    keys = [ln["key"] for ln in plan["lanes"] if ln.get("key")]
    for k in dict.fromkeys(keys):
        sl = lane_slots(plan, k)
        bs = groups.get(k, [])
        if "+" not in k:
            chunks = date_stacks(list(lists.get(k, [])) if bs else [], high)      # 1 stack = 1 date
            if len(chunks) > len(sl):
                left[k] = [x for ch in chunks[len(sl):] for x in ch]
                chunks = chunks[:len(sl)]
            for i, ch in enumerate(chunks):
                c, r = sl[i]
                stacks.append({"c": c, "r": r, "b": k, "segs": _stack(ch, bun=k), "first": i == 0, "i": i})
            free[k] = sl[len(chunks):]
        else:                                             # 🧺 shared lane: 1 stack = 1 bun only. Front first:
            per = {b: date_stacks(list(lists[b]), high) for b in bs}                # 1 stack = 1 bun + 1 date
            order = [(b, j) for j in range(max([len(v) for v in per.values()] or [0]))   # the oldest stack of
                     for b in bs if j < len(per[b])]                                       # each bun, then the next
            for b, j in order[len(sl):]:
                left.setdefault(b, []).extend(per[b][j])
            order = order[:len(sl)]
            for i, (b, j) in enumerate(order):
                c, r = sl[i]
                stacks.append({"c": c, "r": r, "b": b, "segs": _stack(per[b][j], bun=b), "first": j == 0, "i": i,
                               "j": j, "shared": True})
            for b in left:                               # what did not fit is the newest: keep the order by date
                left[b].sort()
            free[k] = sl[len(order):]
    return stacks, left, free


def room_fill(cfg, g, lists, plan, aeon=None):
    """The whole room: the lanes (1 bun per lane) + the 🛒 AEON line (turned crates, 1 bun per place, front first).
    -> (stacks, overflow {bun: crates}, left {bun: [crates]}, free {key: [places]})"""
    stacks, left, free = lane_fill(cfg, g, plan, lists)
    if aeon is not None and g["cols"] > 1:
        last = g["cols"] - 1
        if g.get("aeon_rows"):
            a_spots = [(last, i) for i in range(int(g["aeon_rows"]))]
        else:
            taken = {(x["c"], x["r"]) for x in stacks}
            a_spots = [(last, r) for r in range(g["rows"]) if (r, last) not in g["blocked"] and (last, r) not in taken]
        ah = int(g.get("aeon_high") or g["high"])          # the AEON line can be stacked lower (12 / 15)
        spots = sorted(a_spots, key=lambda x: -x[1])        # front (OUT) first
        for b in sorted(aeon, key=lambda x: (room_order(cfg, x), x)):
            crates = list(aeon[b])
            if not crates:
                continue
            need = -(-len(crates) // ah)
            mine, spots = spots[:need], spots[need:]
            if len(mine) < need:
                left.setdefault(b, []).extend(crates[len(mine) * ah:])
            for i, (c_, r_) in enumerate(mine):
                stacks.append({"c": c_, "r": r_, "b": b, "segs": _stack([(b, d, q) for d, q in crates[i * ah:(i + 1) * ah]]),
                               "first": i == 0, "aeon": True, "i": i})
    return stacks, {b: len(v) for b, v in left.items() if v}, left, free


def stack_where(plan, c, r):
    """(lane number, place from the front) of a place, e.g. (1, 1) = lane 1, the front stack."""
    for i, ln in enumerate(plan["lanes"]):
        if ln["c"] == c and r in ln["rows"]:
            return i + 1, ln["rows"].index(r) + 1
    return None, None


def take_order(plan, stacks, b):
    """The stacks of one bun in the order to take them (oldest first: the fronts of its lanes, then the next row)."""
    mine = [x for x in stacks if x["b"] == b and not x.get("aeon")]
    return sorted(mine, key=lambda x: (min(y[0] for y in x["segs"]), x.get("spill", False), x.get("i", 0)))


def _nth(n):
    return {1: "front", 2: "2nd", 3: "3rd"}.get(n, f"{n}th")


def take_guide(plan, stacks, buns, names):
    """📤 One row per bun: which stacks to take first (lane · place from the front · lot · crates)."""
    rows = []
    for b in buns:
        st_ = take_order(plan, stacks, b)
        if not st_:
            continue
        row = {"Bun": b, "Name": names.get(b, ""), "Crates": sum(y[1] for x in st_ for y in x["segs"])}
        for n, x in enumerate(st_[:4]):
            ln, pos = stack_where(plan, x["c"], x["r"])
            blocked = ""
            if ln and pos and pos > 1:                     # another bun in front of it (shared lane)?
                lane = plan["lanes"][ln - 1]
                ahead = [y for y in stacks if y["c"] == lane["c"] and y["r"] in lane["rows"][:pos - 1] and y["b"] != b]
                if ahead:
                    blocked = f" (move {len(ahead)} stack of {', '.join(sorted({y['b'] for y in ahead}))} first)"
            where = f"L{ln} {_nth(pos)}" if ln else "⚠️ not its lane"
            row[["① first", "② then", "③ then", "④ then"][n]] = (
                f"{where} · {x['segs'][-1][0]:%d/%m} · {sum(y[1] for y in x['segs'])} cr{blocked}")
        rows.append(row)
    return pd.DataFrame(rows).fillna("")


def pick_list(cfg, plan, stacks, buns, names, need_pcs):
    """📤 Tomorrow's take-out: for the expected sales of each bun, which stacks to take — oldest date first."""
    rows = []
    for b in buns:
        need = float(need_pcs.get(b, 0) or 0)
        if need <= 0:
            continue
        cp = crate_pcs(cfg, b)
        want = math.ceil(need / cp)
        left, steps = want, []
        for x in take_order(plan, stacks, b):
            if left <= 0:
                break
            n = sum(y[1] for y in x["segs"])
            q = min(n, left)
            ln, pos = stack_where(plan, x["c"], x["r"])
            where = f"L{ln} {_nth(pos)}" if ln else "⚠️ other place"
            steps.append(f"{where} {min(y[0] for y in x['segs']):%d/%m} ×{q}" + ("" if q == n else f" (of {n})"))
            left -= q
        rows.append({"Bun": b, "Name": names.get(b, ""), "Tomorrow (pcs)": int(round(need)), "Crates": want,
                     "Take in this order (lane · place · date × crates)": " → ".join(steps) or "–",
                     "⚠️ Short": (f"{left} cr — take from the frozen room" if left > 0 else "")})
    return pd.DataFrame(rows)


def room_plans(cfg, rooms, geoms, buns, speed):
    return {r["name"]: room_plan(cfg, geoms[r["name"]], buns, speed) for r in rooms}


def daily_need(cfg, buns, speed, high):
    """Stacks each bun needs for one day of new production (`daily_in_pcs` split like the sales)."""
    daily = float(cfg.get("daily_in_pcs", 16000) or 0)
    tot = sum(max(float(speed.get(b, 0) or 0), 0) for b in buns)
    if daily <= 0:
        return {}, daily
    if tot <= 0:
        return {b: daily / max(len(buns), 1) / crate_pcs(cfg, b) for b in buns}, daily
    return {b: daily * max(float(speed.get(b, 0) or 0), 0) / tot / crate_pcs(cfg, b) for b in buns}, daily


def fill_rooms(cfg, rooms, geoms, buns, pl_stock, speed, plans=None):
    """❄️ cooling stock -> the first room · 🧊 frozen stock -> the second room · 🛒 AEON stock -> its own line on the
    right of the frozen room. Every bun stays in its own fixed lanes; what does not fit in a cooling lane (the newest
    crates) is shown in the frozen room."""
    plans = plans or room_plans(cfg, rooms, geoms, buns, speed)
    cool_room = rooms[0]["name"]
    frz_room = rooms[1]["name"] if len(rooms) > 1 else rooms[0]["name"]
    res = {}
    cool = {b: bun_crates(cfg, b, pl_stock["cool"]) for b in buns}
    cool = {b: v for b, v in cool.items() if v}
    carry = {}
    if cool_room != frz_room:
        stacks, _o, carry, _f = room_fill(cfg, geoms[cool_room], cool, plans[cool_room])
        res[cool_room] = {"stacks": stacks, "overflow": {}, "moved_in": {},
                          "moved_out": {b: len(v) for b, v in carry.items() if v}}
    frz = {b: bun_crates(cfg, b, pl_stock["frozen"]) for b in buns}
    for b, v in carry.items():
        frz[b] = sorted(frz.get(b, []) + v)
    if cool_room == frz_room:
        for b, v in cool.items():
            frz[b] = sorted(frz.get(b, []) + v)
    frz = {b: v for b, v in frz.items() if v}
    ae = {b: bun_crates(cfg, b, pl_stock["aeon"]) for b in buns}
    ae = {b: v for b, v in ae.items() if v}
    g, plan = geoms[frz_room], plans[frz_room]
    stacks, _o, left, free = room_fill(cfg, g, frz, plan, aeon=ae)
    # crates with no place in their own lanes: put them on any free place at the back (marked ⚠️ not its lane)
    spare = sorted({x for v in free.values() for x in v}, key=lambda x: (x[1], x[0]))
    for b in list(left):
        while left[b] and spare:
            c, r = spare.pop(0)
            part = date_stacks(left[b], g["high"])[-1]               # the newest stack (1 date)
            left[b] = left[b][:len(left[b]) - len(part)]
            stacks.append({"c": c, "r": r, "b": b, "segs": _stack(part, bun=b), "first": False, "spill": True})
            for k in free:
                if (c, r) in free[k]:
                    free[k].remove((c, r))
    overflow = {b: len(v) for b, v in left.items() if v}
    sp = frozen_space(cfg, frz, speed, buns, plan=plan)
    reserve = {}
    for k, need in sp["need_by"].items():                  # 📥 tomorrow's production: the back of each bun's lanes
        for x in (free.get(k) or [])[:need]:
            reserve[(x[1], x[0])] = k
    res[frz_room] = {"stacks": stacks, "overflow": overflow, "moved_in": {b: len(v) for b, v in carry.items() if v},
                     "moved_out": {}, "reserve": reserve, "space": sp}
    for r in rooms:
        res.setdefault(r["name"], {"stacks": [], "overflow": {}, "moved_in": {}, "moved_out": {}})
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
  const seenR={};(rd.reserve||[]).forEach(([row,c,k])=>{const [x,z]=XZ(r,c,row);quad(x,z,x+CW,z+CL,'rgba(64,192,87,.35)');
   if(!seenR[k]){seenR[k]=1;labels.push({v:[x+CW/2,0.12,z+CL/2],t:'📥 new '+(k||''),c:'#b2f2bb',fs:9,pr:1});}});
  (r.lanes||[]).forEach(([c,t])=>{const turned=r.arows>0&&c===r.cols-1;const x=o+c*PX+GAP/2+(turned?CL:CW)/2;
   labels.push({v:[x,0,-0.25],t,c:'#ffe066',fs:10,bg:'rgba(20,28,38,.85)',pr:3});});
  labels.push({v:[o+r.w/2,r.h+0.4,r.l/2],t:r.name+' · '+rd.used.toLocaleString()+' / '+r.cap.toLocaleString()+' crates · '+rd.pcs.toLocaleString()+' pcs',c:'#e9ecef',fs:12,pr:4});
  if(dims){line(k,[o,0,-0.45],[o+r.w,0,-0.45],'#adb5bd',1);labels.push({v:[o+r.w/2,0,-0.75],t:r.cols+' stacks · '+r.w+' m',c:'#ced4da',fs:10,pr:2});
   line(k,[o-0.4,0,0],[o-0.4,0,r.l],'#adb5bd',1);labels.push({v:[o-0.8,0,r.l/2],t:r.rows+' deep · '+r.l+' m',c:'#ced4da',fs:10,pr:2});}
  r.blocked.forEach(([row,c,t,raw])=>{const [x,z]=XZ(r,c,row);
   if(raw===2){quad(x,z,x+CW+GAP,z+CL+GAP,'rgba(255,212,59,.30)');if(row===r.rows-1)labels.push({v:[x+CW/2,0.15,z+CL/2],t:'🚶 Walkway (keep free)',c:'#ffe066',fs:10,pr:2});return;}
   if(raw){quad(x,z,x+CW+GAP,z+CL+GAP,'rgba(173,181,189,.35)');if(t&&t.trim())labels.push({v:[x+CW/2,0.15,z+CL/2],t:'📦 '+t+' (keep empty)',c:'#dee2e6',fs:10,pr:1});return;}
   addBox(L,k,x,0,z,CW,1.4,CL,t?'#364fc7':'#e8590c',0.55,null,0);
   if(t&&t.trim())labels.push({v:[x+CW/2,1.6,z+CL/2],t,c:'#bac8ff',fs:10,pr:1});});
  rd.stacks.forEach(s=>{const [c,row,bun,segs,first,isA]=s;const bn=BUN[bun]||{color:'#adb5bd',label:bun};
   const turned=isA&&r.arows>0;   // AEON line: crates turned, 63 cm across, 44 cm deep
   const [x,z]=turned?[off[r.name]+c*PX+GAP/2,(r.arows-1-row)*(CW+GAP)+GAP/2]:XZ(r,c,row);
   const BW=turned?CL:CW,BD=turned?CW:CL;let lev=0;
   const dim=only&&!segs.some(g=>(g[3]||bun)===only);
   segs.forEach(([lot,n,pcs,b2])=>{const sb=b2||bun,sbn=BUN[sb]||bn;const a=age(D.lots[lot]);addBox(L,k,x,lev*CH,z,BW,n*CH-0.004,BD,colBun?sbn.color:ageCol(sb,a),dim?0.12:1,
     {room:r.name,s,row,c,lot,n,pcs,a,bun:sb,rows:turned?r.arows:r.rows,aeon:isA},n);lev+=n;});
   if(!dim){const top=segs[segs.length-1];const lot=D.lots[top[0]];
    labels.push({v:[x+BW/2,lev*CH+0.12,z+BD/2],t:(isA?'🛒 ':segs.some(g=>g[3])?'🧺 ':'')+(first?'⭐ ':'')+(lotLbl?lot.slice(8,10)+'/'+lot.slice(5,7)+' ':'')+(top[3]||bun),c:'#fff',fs:9,bg:shade((BUN[top[3]||bun]||bn).color,0.5,0.92),pr:first?2:0});}});
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
function describe(r){if(!r)return '👆 Tap a stack: bun, lot date, age, crates, pcs.';const b=BUN[r.bun]||{label:r.bun},lot=D.lots[r.lot];
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
 '<br>1 lane = 1 bun (yellow name at the front of each lane) · take from the FRONT · push new crates in at the BACK of the same lane · ⭐ = oldest (take first) · 📥 = space for tomorrow\'s production';}
window.addEventListener('resize',()=>{size();redraw();});legend();size();__START__draw();
</script>"""


def _lane_names(g, plan):
    """{column: lane name} for the sheet / 3D: bun code, 🧺 small buns, 🛒 AEON."""
    out = {ln["c"]: f"L{i + 1} {lane_label(ln.get('key'))}" for i, ln in enumerate((plan or {}).get("lanes", []))}
    if g.get("aeon_rows") and g["cols"] > 1:
        out[g["cols"] - 1] = "🛒 AEON"
    for c in g.get("walk_cols") or []:
        out[c] = "🚶"
    return out


def room_sheet_html(room, g, stacks, names, new=None, reserve=None, plan=None, take=None):
    """Your Excel 'ស្តុកនំប្រចាំថ្ងៃ' layout: one cell per stack (lot date + bun / pcs), column totals, total."""
    cells = {(s["r"], s["c"]): s for s in stacks if not s.get("aeon")}
    a_line = sorted([s for s in stacks if s.get("aeon")], key=lambda s: -s["r"])      # front first
    arows = int(g.get("aeon_rows") or 0)
    bd = "border:1px solid #444;"
    h = [f"<div style='overflow-x:auto'><table style='border-collapse:collapse;font-size:13px;text-align:center;min-width:{g['cols'] * 78}px'>",
         f"<tr><td colspan='{g['cols']}' style='{bd}font-size:18px;font-weight:700;padding:6px'>ស្តុកនំប្រចាំថ្ងៃ · {room['name']}</td>"
         f"<td style='padding:4px 8px;font-size:12px'>{'Door in ⤵' if room['door_in'].startswith('right') else ''}</td></tr>"]
    col_tot = [0] * g["cols"]
    ln_names = _lane_names(g, plan)
    kmap = {ln["c"]: ln.get("key") for ln in (plan or {}).get("lanes", [])}
    sub = "<br><span style='font-weight:400;font-size:10px'>{}</span>"
    lane_row = ("<tr>" + "".join(
        f"<td style='{bd}background:#343a40;color:#fff;font-weight:700;padding:3px 4px;font-size:12px'>"
        + ln_names.get(c, "") + (sub.format(names[kmap[c]]) if names.get(kmap.get(c) or "") else "") + "</td>"
        for c in range(g["cols"])) + "<td style='font-size:11px;padding:2px 6px'>lane</td></tr>") if ln_names else ""
    h.append(lane_row)
    for r in range(g["rows"]):
        h.append("<tr>")
        c = 0
        while c < g["cols"]:
            if arows and c == g["cols"] - 1:                    # the turned AEON line: one tall cell
                if r == 0:
                    a_pcs = int(sum(x[2] for s_ in a_line for x in s_["segs"]))
                    col_tot[c] += a_pcs
                    items = "".join(
                        f"<div style='border-bottom:1px solid #ccc;padding:2px'>{'⭐ ' if s_['first'] else ''}"
                        f"{i + 1}. {s_['segs'][-1][0]:%d/%m} {' '.join(sorted({x[3] for x in s_['segs'] if len(x) > 3}) or [s_['b']])}"
                        f" · <b>{int(sum(x[2] for x in s_['segs'])):,}</b></div>" for i, s_ in enumerate(a_line))
                    h.append(f"<td rowspan='{g['rows']}' style='{bd}background:#fff4e6;vertical-align:top;padding:4px;"
                             f"min-width:120px;font-size:12px'><b>🛒 AEON line</b><br>{len(a_line)} / {arows} places used · 1 bun per place · "
                             f"crates turned · front (OUT) first<br>{items or '–'}</td>")
                c += 1
                continue
            if (r, c) in g["blocked"]:
                lab, span = g["blocked"][(r, c)], 1
                while c + span < g["cols"] and g["blocked"].get((r, c + span)) == lab and (r, c + span) in g["blocked"]:
                    span += 1
                bg = "#ED7D31" if not lab else ("#e9ecef" if lab == RAW_LABEL else "#fff3bf" if lab == WALK_LABEL else "#fff")
                h.append(f"<td colspan='{span}' style='{bd}background:{bg};padding:6px'>"
                         f"{'🚶' if lab == WALK_LABEL else lab}</td>")
                c += span
                continue
            s = cells.get((r, c))
            if s:
                top = s["segs"][-1][0]
                pcs = sum(x[2] for x in s["segs"])
                mix = sorted({x[3] for x in s["segs"] if len(x) > 3})
                col_tot[c] += pcs
                star = "⭐ " if s["first"] else ("⚠️ " if s.get("spill") else "")
                k_new = (new or {}).get((r, c))
                mark = (f"<br><span style='background:#2f9e44;color:#fff;border-radius:4px;padding:0 4px;font-size:11px'>"
                        f"🆕 put {k_new} cr</span>") if k_new else ""
                k_take = (take or {}).get((r, c))
                if k_take:
                    mark += (f"<br><span style='background:#e8590c;color:#fff;border-radius:4px;padding:0 4px;"
                             f"font-size:11px'>🚚 take {k_take} cr</span>")
                edge = ("outline:3px solid #2f9e44;outline-offset:-3px;" if k_new else
                        "outline:3px solid #e8590c;outline-offset:-3px;" if k_take else "")
                h.append(f"<td style='{bd}{edge}background:{COLORS.get(s['b'], '#fff')};padding:4px 6px;min-width:70px'>"
                         f"{star}{'🧺 ' if mix else ''}{top:%d/%m} {' '.join(mix) if mix else s['b']}<br><b>{pcs:,}</b>{mark}</td>")
            elif (r, c) in (reserve or {}):
                k_res = reserve.get((r, c)) if isinstance(reserve, dict) else ""
                h.append(f"<td style='{bd}background:#d3f9d8;padding:4px 6px;min-width:70px;color:#2b8a3e'>"
                         f"📥 new {lane_label(k_res) if k_res else ''}</td>")
            else:
                h.append(f"<td style='{bd}padding:4px 6px;min-width:70px;color:#999'>–</td>")
            c += 1
        h.append("<td></td></tr>")
    tot = sum(col_tot)
    h.append("<tr>" + "".join(f"<td style='{bd}background:#FFF2CC;font-weight:700;text-align:right;padding:4px 6px'>{v:,}</td>"
                              for v in col_tot)
             + f"<td style='{bd}background:#FFF2CC;font-weight:700;padding:4px 8px'>{tot:,} នំសរុប</td></tr>")
    out_txt = "door out" if room["door_out"].startswith("front") else ""
    h.append(lane_row.replace("#343a40", "#868e96"))
    h.append(f"<tr><td colspan='{g['cols']}' style='padding:4px'>⬇️ FRONT · take here first · {out_txt}</td><td></td></tr>"
             "</table></div>")
    return "".join(h), tot


def room_sheet_excel(room, g, stacks, plan=None):
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
    cells = {(s["r"], s["c"]): s for s in stacks if not s.get("aeon")}
    a_line = sorted([s for s in stacks if s.get("aeon")], key=lambda s: -s["r"])
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
    for c, nm in _lane_names(g, plan).items():               # the lane names, at the front
        x = ws.cell(tr + 1, 1 + c, nm)
        x.font, x.alignment, x.border = Font(bold=True, color="FFFFFF"), mid, box
        x.fill = PatternFill("solid", fgColor="343A40")
    ws.cell(tr + 1, 1 + g["cols"], "lane")
    ws.cell(tr + 2, 1 + g["cols"] // 2, "FRONT · take here first · door out")
    ws.cell(2, 1 + g["cols"], "Door in")
    from openpyxl.utils import get_column_letter
    for c in range(g["cols"] + 2):
        ws.column_dimensions[get_column_letter(c + 1)].width = 12
    if a_line:                                              # the AEON line (turned crates), front first
        ar = tr + 4
        ws.cell(ar, 1, "🛒 AEON line (front / OUT first)").font = Font(bold=True)
        for i, s_ in enumerate(a_line):
            ws.cell(ar + 1 + i, 1, i + 1)
            ws.cell(ar + 1 + i, 2, f"{s_['segs'][-1][0]:%d/%m}")
            ws.cell(ar + 1 + i, 3, " ".join(sorted({x[3] for x in s_["segs"] if len(x) > 3}) or [s_["b"]]))
            ws.cell(ar + 1 + i, 4, int(sum(x[2] for x in s_["segs"]))).number_format = "#,##0"
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
    plans = room_plans(cfg, rooms, geoms, buns, speed)      # the fixed lanes (the same for every day of the replay)
    is_admin = st.session_state.get("p_role") == "admin"
    if is_admin:                                         # sizes: Admin only (staff just look)
        with st.expander("📐 Adjust sizes — room grid, doors, crate, room / order / pcs per crate of each bun (Admin only)"):
            rn = st.session_state.get("room_n", 0)
            new_vals = rooms_settings(cfg, buns, names, rn, kp="rm", speed=speed)
            if st.button("💾 Save sizes", type="primary", key="rm_save"):
                try:
                    update_settings(new_vals)
                    audit("room sizes saved", " · ".join(
                        f"{r['name']} {r['cols']}×{r['rows']} stacks, {r['high']} high"
                        + (f" (AEON line {r['aeon_rows']} × {r['aeon_high']} high)" if r.get("aeon_rows") else "")
                        + f", blocked [{r['blocked']}], "
                        f"in {r['door_in']}, out {r['door_out']}" for r in new_vals["rooms"])
                        + " | crate " + "×".join(f"{v:g}" for v in new_vals["crate"].values()) + " cm")
                    st.session_state["room_n"] = rn + 1
                    st.session_state.pop("rm_lane_auto_on", None)
                    st.session_state["room_flash"] = "✅ Sizes saved — the 3D view uses them now."
                    st.rerun()
                except Exception as e:
                    st.error(f"Not saved: {e}")
    show_flash("room_flash")
    c1, c2 = st.columns([1, 3])
    back = c1.selectbox("Days to replay", [7, 14, 3, 1], key="room_back", format_func=lambda n: f"last {n} days")
    days = [t - timedelta(days=i) for i in range(int(back) - 1, -1, -1)]
    lots, lot_i, out_days, today_stacks = [], {}, [], {}
    overflow_today, moved_today, today_reserve = {}, {}, {}
    for d in days:
        pl_d, _s, _h, _nc, _b = compute_places(buns, prod, counts, adjs, sales, d)
        rd = {}
        filled = fill_rooms(cfg, rooms, geoms, buns, pl_d, speed, plans)
        for r in rooms:
            stacks, overflow = filled[r["name"]]["stacks"], filled[r["name"]]["overflow"]
            for s in stacks:
                for seg in s["segs"]:
                    if seg[0] not in lot_i:
                        lot_i[seg[0]] = len(lots)
                        lots.append(seg[0].isoformat())
            rd[r["name"]] = {"reserve": [[x[0], x[1], lane_label(k)] for x, k in
                                         (filled[r["name"]].get("reserve") or {}).items()],
                             "stacks": [[s["c"], s["r"], s["b"], [[lot_i[x[0]], x[1], x[2]] + ([x[3]] if len(x) > 3 else [])
                                                                    for x in s["segs"]], s["first"], int(bool(s.get("aeon")))]
                                        for s in stacks],
                             "used": sum(x[1] for s in stacks for x in s["segs"]),
                             "pcs": int(sum(x[2] for s in stacks for x in s["segs"]))}
            if d == t:
                today_stacks[r["name"]] = stacks
                today_reserve[r["name"]] = filled[r["name"]].get("reserve") or {}
                overflow_today[r["name"]] = overflow
                moved_today[r["name"]] = filled[r["name"]]["moved_out"]
        out_days.append({"iso": d.isoformat(), "label": ("Today · " if d == t else "") + f"{d:%a %d %b}", "rooms": rd})
    today = out_days[-1]["rooms"]
    sp_today = next((v["space"] for v in filled.values() if v.get("space")), None)
    tiles([(r["name"], f"{today[r['name']]['used']:,} / {geoms[r['name']]['capacity']:,}",
            f"crates · {geoms[r['name']]['places']} stacks × {geoms[r['name']]['high']} high · "
            f"{today[r['name']]['pcs']:,} pcs · {today[r['name']]['used'] / max(geoms[r['name']]['capacity'], 1) * 100:.0f}% full")
           for r in rooms])
    for i, r in enumerate(rooms[:-1]):
        mv = moved_today.get(r["name"]) or {}
        if mv:
            st.info(f"🔄 **Their lanes in {r['name']} are full** → the newest crates are shown in "
                    f"**{rooms[i + 1]['name']}**: " + ", ".join(f"{short(b)} {n} crates" for b, n in mv.items())
                    + f" (total {sum(mv.values()):,} crates). The oldest crates stay at the front of each lane.")
    if sp_today and sp_today["daily"]:
        (st.success if sp_today["ok"] else st.error)(
            f"📥 {sp_today['room']}: **{sp_today['free']} free stacks ≈ {sp_today['free_pcs']:,} pcs** for new production "
            f"(green 📥 places at the back of each bun's lanes) — needed every day: {sp_today['need']} stacks for "
            f"{int(sp_today['daily']):,} pcs"
            + ("" if sp_today["ok"] else " — ⚠️ not enough for: " + ", ".join(
                f"{lane_label(k)} −{n}" for k, n in sp_today["short_by"].items()) + " stacks — use this evening's 🚚 move list."))
    if is_admin and not all(p_["saved"] for p_ in plans.values()):
        st.info("🔒 The lanes are set **automatically from sales** right now. Admin: open 📐 Adjust sizes → "
                "**Lanes** and press 💾 Save, so every bun keeps the **same lane every day**.")
    parts = [f"**{r['name']}**: " + ", ".join(f"{short(b)} {n}" for b, n in overflow_today[r["name"]].items())
             for r in rooms if overflow_today.get(r["name"])]
    if parts:
        st.warning("⚠️ No place today for these crates — " + " · ".join(parts)
                   + ". Move a bun to the other room" + (", or adjust the room grid (📐)." if is_admin else "."))
    present = [b for b in buns if any(s["b"] == b or any(len(g_) > 3 and g_[3] == b for g_ in s["segs"])
                                      for x in today_stacks.values() for s in x)]
    data = {"days": out_days, "lots": lots, "crate": cr, "gap": GRID_GAP,
            "rooms": [{"name": r["name"], "cols": geoms[r["name"]]["cols"], "rows": geoms[r["name"]]["rows"],
                       "arows": geoms[r["name"]].get("aeon_rows", 0),
                       "lanes": [[c, nm] for c, nm in _lane_names(geoms[r["name"]], plans[r["name"]]).items()],
                       "w": geoms[r["name"]]["w"], "l": geoms[r["name"]]["l"], "h": geoms[r["name"]]["h"],
                       "cap": geoms[r["name"]]["capacity"], "din": r["door_in"], "dout": r["door_out"],
                       "blocked": [[k[0], k[1], v if v and (k[0], k[1] - 1) not in geoms[r["name"]]["blocked"]
                                    or v and geoms[r["name"]]["blocked"].get((k[0], k[1] - 1)) != v else ("" if not v else " "),
                                    1 if v == RAW_LABEL else 2 if v == WALK_LABEL else 0]
                                   for k, v in sorted(geoms[r["name"]]["blocked"].items())]} for r in rooms],
            "buns": [{"code": b, "label": f"{b} {names.get(b, '')}".strip(), "color": CRATE_COLORS.get(b, EXTRA_COLORS[i % 7])}
                     for i, b in enumerate(present)],
            "shelf": {b: int(cfg.get("shelf_by_bun", {}).get(b, cfg.get("shelf_days", 10))) for b in buns}}
    h = 430 if st.session_state.get("phone_mode") else 600
    components.html(tr_js(ROOM3D_HTML.replace("__DATA__", json.dumps(data, ensure_ascii=False)).replace("__H__", str(h)))
                    .replace("__START__", ""), height=h + 190)

    st.markdown("#### 📋 Room sheet — your Excel layout (today)")
    pick = st.radio("Room sheet", [r["name"] for r in rooms], horizontal=True, key="room_sheet",
                    label_visibility="collapsed")
    room = next(r for r in rooms if r["name"] == pick)
    html, tot = room_sheet_html(room, geoms[pick], today_stacks.get(pick, []), names,
                                reserve=today_reserve.get(pick, {}), plan=plans[pick])
    st.markdown(html, unsafe_allow_html=True)
    st.download_button(f"⬇️ {pick} sheet (Excel)", room_sheet_excel(room, geoms[pick], today_stacks.get(pick, []),
                                                                      plan=plans[pick]),
                       file_name=f"room_stock_{t}.xlsx",
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", key="room_xlsx")
    c_name = rooms[0]["name"]
    st.markdown(f"#### 📤 Tomorrow's take-out · {c_name}")
    fc_t = forecast(sales, buns, t + timedelta(days=1), 1, int(cfg["lookback_days"]))
    pl_df = pick_list(cfg, plans[c_name], today_stacks.get(c_name, []), buns, names,
                      {b: fc_t.get((t + timedelta(days=1), b), 0) for b in buns})
    st.caption("Expected sales for tomorrow → the crates to take, **oldest production date first** (L = lane from the "
               "left · front = at the door). '(of 15)' = take only part of that stack; the rest stays at the front.")
    if pl_df.empty:
        st.info("No sales expected tomorrow.")
    else:
        st.dataframe(pl_df, hide_index=True, width="stretch")
    st.markdown(f"#### 📤 Take-out order · {pick}")
    st.caption("For each bun: take the stacks in this order — **oldest production date first** (L = lane, counted "
               "from the left; front = the stack at the door). 1 stack = 1 bun + 1 production date.")
    tg = take_guide(plans[pick], today_stacks.get(pick, []), buns, names)
    if tg.empty:
        st.info("No stock in this room today.")
    else:
        st.dataframe(tg, hide_index=True, width="stretch")
    st.caption("FIFO lanes: **1 lane = 1 bun, always the same lane** (name under each column). Take only from the "
               "**FRONT** of the lane (⭐ = oldest, take first); push new crates in at the **BACK** of the bun's own "
               "lane — never in front of older crates, never in another bun's lane. A bun with 2+ lanes: every lane "
               "has its oldest at the front. 🧺 = a lane shared by 2–3 small buns: still 1 stack = 1 bun. Use the Day slider / ▶ Play "
               "to see how it moved.")


def rooms_settings(cfg, buns, names, n, kp="set", speed=None):
    """Room grid (stacks across × deep, blocked places, doors), crate size, and room / order / pcs per crate per bun."""
    if kp == "set":
        st.markdown("#### 🧊 Rooms and crates (for 🧊 3D rooms)")
    st.caption("A room = a grid of stack places like your sheet. Across = columns, Deep = rows (row 1 = back, at the IN "
               "side). Blocked = places with no stock, e.g. `1:5-8=Cooling fan; 1:9-10` (row:columns=name).")
    rdf = pd.DataFrame([{"Room": r["name"], "Stacks across": r["cols"], "Stacks deep": r["rows"], "Crates high": r["high"],
                         "AEON line high": r["aeon_high"], "Height (m)": r["h"], "Empty at back (m)": r["back_m"], "AEON line places": r["aeon_rows"],
                         "Walkway before AEON (m)": r["aisle_m"],
                         "Blocked places": r["blocked"],
                         "Door IN": r["door_in"], "Door OUT": r["door_out"]} for r in rooms_of(cfg)])
    hi_opts = sorted({12, 15} | {int(r["high"]) for r in rooms_of(cfg)} | {int(r["aeon_high"]) for r in rooms_of(cfg)})
    red = st.data_editor(rdf, hide_index=True, width="stretch", num_rows="dynamic", key=f"{kp}_rooms3_{n}",
                         column_config={"Room": st.column_config.TextColumn("Room", required=True),
                                        **{c: st.column_config.NumberColumn(c, min_value=1, max_value=60, step=1, required=True)
                                           for c in ["Stacks across", "Stacks deep"]},
                                        "Crates high": st.column_config.SelectboxColumn(
                                            "📏 Crates high", options=hi_opts, required=True,
                                            help="How many crates in one stack: 12 or 15"),
                                        "AEON line high": st.column_config.SelectboxColumn(
                                            "🛒 AEON line high", options=hi_opts, required=True,
                                            help="Crates in one stack in the AEON line: 12 or 15"),
                                        "Height (m)": st.column_config.NumberColumn("Height (m)", min_value=1.0,
                                                                                    max_value=20.0, step=0.1, format="%.1f"),
                                        "Empty at back (m)": st.column_config.NumberColumn(
                                            "Empty at back (m)", min_value=0.0, max_value=50.0, step=0.1, format="%.1f",
                                            help="Kept free at the back (row 1 side), e.g. 1.6 m for raw material"),
                                        "AEON line places": st.column_config.NumberColumn(
                                            "🛒 AEON line places", min_value=0, max_value=40, step=1,
                                            help="Right-hand line for the AEON stock with the crates turned (e.g. 11). "
                                                 "0 = no AEON line in this room"),
                                        "Walkway before AEON (m)": st.column_config.NumberColumn(
                                            "🚶 Walkway before AEON (m)", min_value=0.0, max_value=3.0, step=0.1,
                                            format="%.1f", help="Free path between the frozen lanes and the AEON line "
                                                                "(whole stack columns, ~0.49 m each). 0 = none"),
                                        "Blocked places": st.column_config.TextColumn("Blocked places"),
                                        "Door IN": st.column_config.SelectboxColumn("🟢 Door IN", options=DOOR_SPOTS, required=True),
                                        "Door OUT": st.column_config.SelectboxColumn("🟠 Door OUT", options=DOOR_SPOTS, required=True)})
    rooms = []
    for r in red.to_dict("records"):
        if str(r.get("Room") or "").strip():
            try:
                rooms.append({"name": str(r["Room"]).strip(), "cols": int(r["Stacks across"]), "rows": int(r["Stacks deep"]),
                              "high": int(r.get("Crates high") or 15),
                              "aeon_high": int(r.get("AEON line high") or r.get("Crates high") or 15),
                              "h": float(r.get("Height (m)") or 3.0),
                              "back_m": float(r.get("Empty at back (m)") or 0),
                              "aeon_rows": int(r.get("AEON line places") or 0),
                              "aisle_m": float(r.get("Walkway before AEON (m)") or 0),
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
        f"{r['name']} ≈ {g['w']} × {g['l']} m = {g['places']} stacks × {g['high']} high"
        + (f" (AEON line {g['aeon_rows']} × {g['aeon_high']} high)" if g["aeon_rows"] else "")
        + f" = {g['capacity']:,} crates"
        + (f" (back {g['back_rows']} rows = {g['back_rows'] * (cr['l'] + GRID_GAP):.2f} m kept empty)" if g["back_rows"] else "")
        + (f" (🚶 walkway {g['walk_m']:.2f} m before the AEON line)" if g.get("walk_cols") else "")
        for r in rooms for g in [room_geom(r, cr)]))
    st.caption("Which room: ❄️ cooling stock → the first room · 🧊 frozen stock → the second room · 🛒 AEON stock → "
               "its own line on the right of the frozen room (from the evening counts and 🚚 moves).")
    bdf = pd.DataFrame([{"Bun": x, "Name": names.get(x, ""),
                         "Order": int(room_order(cfg, x)), "Pcs per crate": crate_pcs(cfg, x)} for x in buns])
    bed = st.data_editor(bdf, hide_index=True, width="stretch", num_rows="fixed", disabled=["Bun", "Name"],
                         key=f"{kp}_bunroom_{n}",
                         column_config={"Order": st.column_config.NumberColumn("↔️ Order (1 = first column)", min_value=1,
                                                                               max_value=99, step=1, required=True),
                                        "Pcs per crate": st.column_config.NumberColumn("📦 Pcs per crate", min_value=1,
                                                                                       max_value=2000, step=1, required=True)})
    recs = bed.to_dict("records")
    order = {r["Bun"]: int(r["Order"] or 99) for r in recs}
    cpcs = {r["Bun"]: int(r["Pcs per crate"] or 60) for r in recs}

    # 🛣️ the lanes: 1 column = 1 bun, fixed every day
    st.markdown("##### 🛣️ Lanes — 1 lane (column) = 1 bun, the same every day")
    st.caption("Staff take only from the FRONT of a lane and push new crates in at the BACK. Type the bun of each "
               "lane: one code (e.g. `N1`; a big seller can have 2–3 lanes side by side), or small buns sharing one "
               "🧺 lane joined with + (e.g. `N22+N23`), or empty = spare. Press 💾 Save to fix the lanes.")
    if speed is None:
        try:
            _p, _c, _a, sales_, _n, _b = get_data(cfg)
            speed, _sn = sales_speed(sales_, buns, today_kh(), int(cfg["lookback_days"]))
        except Exception:
            speed = {}
    cfg2 = {**cfg, "room_order": order, "crate_pcs": cpcs}
    lanes_out = {}
    ln_n = st.session_state.get(f"{kp}_lane_n", 0)
    if st.button("↺ Lanes automatic from sales", key=f"{kp}_lane_auto"):
        st.session_state[f"{kp}_lane_n"] = ln_n + 1
        st.session_state[f"{kp}_lane_auto_on"] = True
        st.rerun()
    use_auto = st.session_state.get(f"{kp}_lane_auto_on", False)
    known = {b.upper(): b for b in buns}
    for r in rooms:
        g = room_geom(r, cr)
        cfg3 = {k: v for k, v in cfg2.items() if k != "lanes"} if use_auto else cfg2
        plan = room_plan(cfg3, g, buns, speed)
        ldf = pd.DataFrame([{"Lane": i + 1, "Column": ln["c"] + 1, "Places": len(ln["rows"]),
                             "Bun(s)": str(ln.get("key") or "")} for i, ln in enumerate(plan["lanes"])])
        st.markdown(f"**{r['name']}** · {len(plan['lanes'])} lanes"
                    + (" · ✅ saved" if plan["saved"] and not use_auto else " · ⚙️ automatic (not saved yet)"))
        if ldf.empty:
            continue
        led = st.data_editor(ldf, hide_index=True, width="stretch", num_rows="fixed",
                             disabled=["Lane", "Column", "Places"], key=f"{kp}_lanes_{r['name']}_{n}_{ln_n}",
                             column_config={"Bun(s)": st.column_config.TextColumn(
                                 "Bun(s) of this lane", help="N1 · or N22+N23 for a shared 🧺 lane · empty = spare")})
        keys, bad = [], []
        for x in led.to_dict("records"):
            parts = [p_.strip().upper() for p_ in re.split(r"[+,/ ]+", str(x.get("Bun(s)") or "")) if p_.strip()]
            bad += [p_ for p_ in parts if p_ not in known]
            keys.append("+".join(dict.fromkeys(known[p_] for p_ in parts if p_ in known)))
        lanes_out[r["name"]] = keys
        has = {b for k in keys for b in lane_members(k)}
        no_lane = [b for b in buns if b not in has and float(speed.get(b, 0) or 0) > 0]
        if bad:
            st.warning("⚠️ Unknown bun code: " + ", ".join(sorted(set(bad))))
        if no_lane:
            st.warning("⚠️ No lane for: " + ", ".join(no_lane) + " — add them to a lane (e.g. `N22+" + no_lane[0] + "`).")
    return {"rooms": rooms, "crate": {"w": cw, "l": cl, "h": ch}, "room_order": order, "crate_pcs": cpcs,
            "lanes": lanes_out}


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
# 🤖 AUTO-FIX BOT — checks the data files by itself, repairs what is safe, catches page errors
# ==========================================
ERROR_FILE = "production_errors.csv"
ERROR_COLS = ["Time", "User", "Page", "Error", "Where", "Result"]
BOT_ISSUES_FILE = "production_bot_issues.json"            # problems the bot could not fix alone (for Admin)
BOT_EVERY_S = 15 * 60
DATE_FORMATS = ["%Y-%m-%d", "%d/%m/%Y", "%d-%m-%Y", "%Y/%m/%d", "%d.%m.%Y", "%m/%d/%Y", "%d/%m/%y", "%Y-%m-%d %H:%M:%S"]
BOT_FILES = [  # file, columns, date columns (must), date columns (may be empty), id column, can pcs be negative
    (PROD_FILE, PROD_COLS, ["Prod_Date"], [], "Entry_Id", False),
    (COUNT_FILE, COUNT_COLS, ["Count_Date", "Prod_Date"], [], "Count_Id", False),
    (ADJ_FILE, ADJ_COLS, ["Date"], ["Prod_Date"], "Adj_Id", True),
    (MOVE_FILE, MOVE_COLS, ["Date", "Prod_Date"], [], "Move_Id", False),
]


def _fix_date(v):
    """Any usual way of writing a date -> 'YYYY-MM-DD' (None = cannot understand it)."""
    t = str(v).strip()
    if not t:
        return None
    for f in DATE_FORMATS:
        try:
            return datetime.strptime(t[:19] if "%H" in f else t[:10] if f == "%Y-%m-%d" else t, f).date().isoformat()
        except ValueError:
            continue
    try:
        x = pd.to_datetime(t, dayfirst=True, errors="raise")
        return x.date().isoformat()
    except Exception:
        return None


def _fix_pcs(v):
    """' 1,200 ' / '1200.0' / '1 200' -> '1200'  (None = not a number)."""
    t = str(v).strip().replace(",", "").replace(" ", "").replace(" ", "")
    if re.fullmatch(r"[+-]?\d+(\.0+)?", t or "x"):
        return str(int(float(t)))
    return None


def bot_audit(action, detail):
    row = {"Time": now_kh().strftime("%Y-%m-%d %H:%M:%S"), "User": "bot", "Name": "🤖 Auto-fix bot",
           "Action": action, "Detail": str(detail)[:500]}
    try:
        modify_csv(AUDIT_FILE, AUDIT_COLS, lambda df: pd.concat([df, pd.DataFrame([row])], ignore_index=True))
    except Exception:
        pass


def _bot_backup(name):
    """A copy before the bot changes anything (Dropbox: backups/bot_<time>_<file>)."""
    try:
        data, _rev = read_bytes(name, max_age=0)
        if not data:
            return
        bname = f"bot_{now_kh():%Y-%m-%d_%H%M}_{name}"
        if USE_DROPBOX:
            import dropbox
            _dbx().files_upload(data, f"{DROPBOX_FOLDER}/backups/{bname}", mode=dropbox.files.WriteMode.overwrite,
                                mute=True)
        else:
            os.makedirs(os.path.join(LOCAL_DIR, "backups"), exist_ok=True)
            with open(os.path.join(LOCAL_DIR, "backups", bname), "wb") as f:
                f.write(data)
    except Exception:
        pass


def _merge_bad_line(fields, header):
    """Repairs the usual broken line: a number typed with a comma (1,200) split into two columns.
    Returns the repaired fields or None when it is not clear."""
    extra = len(fields) - len(header)
    if extra >= 1 and "Pcs" in header:
        p = header.index("Pcs")
        joined = ",".join(fields[p:p + extra + 1])
        if re.fullmatch(r"\s*[+-]?\d{1,3}(,\d{3})+\s*", joined):          # only a real 1,200 / 12,500 / 1,250,000
            return fields[:p] + [joined.strip()] + fields[p + extra + 1:]
    if extra == -1 and header and header[-1] in ("Team", "Place", "Note"):
        return fields + [""]                                # only the last (optional) column is missing
    return None


def _write_lines(name, cols, header, new_rows_by_bad, rev_check=True):
    """Puts repaired broken lines back as normal lines (or drops them). new_rows_by_bad: {tuple(bad): fields|None}."""
    for attempt in range(4):
        df, rev, hdr, bad = _load_csv(name, cols, max_age=0)
        add, keep_bad = [], []
        for r in bad:
            k = tuple(r)
            if k in new_rows_by_bad:
                if new_rows_by_bad[k] is not None:
                    add.append(dict(zip(hdr, new_rows_by_bad[k])))
            else:
                keep_bad.append(r)
        if add:
            df = pd.concat([df, pd.DataFrame(add).reindex(columns=cols).fillna("")], ignore_index=True)
        try:
            write_bytes(name, _csv_bytes(df, cols, keep_bad), rev)
            return
        except Conflict:
            time.sleep(0.4 * (attempt + 1))
    raise RuntimeError("The file was being saved by someone else. Try again.")


def bot_scan(cfg, fix=True):
    """Looks at every data file. Safe problems are repaired at once (after a backup);
    the others are returned for Admin. Returns (fixed: [text], issues: [dict])."""
    known = set(DEFAULT_BUNS) | set((cfg.get("target_days") or {}).keys()) | set((cfg.get("crate_pcs") or {}).keys())
    fixed, issues = [], []
    for name, cols, must_dates, may_dates, idcol, neg_ok in BOT_FILES:
        df, _rev, header, bad = _load_csv(name, cols, max_age=0)
        # 1) broken lines (wrong number of columns): repair the clear ones, keep the rest for Admin
        if bad:
            repaired = {tuple(r): _merge_bad_line(r, header) for r in bad}
            ok = {k: v for k, v in repaired.items() if v is not None}
            for k, v in repaired.items():
                if v is None:
                    issues.append({"kind": "line", "file": name, "fields": list(k), "header": header,
                                   "what": f"broken line ({len(k)} columns, needs {len(header)})", "value": ",".join(k),
                                   "line": ",".join(k)[:160]})
            if ok and fix:
                _bot_backup(name)
                try:
                    _write_lines(name, cols, header, ok)
                    fixed.append(f"{name}: {len(ok)} broken line(s) repaired (a number typed with a comma)")
                    bot_audit("bot fixed", fixed[-1] + " · " + " | ".join(",".join(v) for v in list(ok.values())[:3]))
                    df, _rev, header, bad = _load_csv(name, cols, max_age=0)
                except Exception:
                    pass
        if df.empty:
            continue
        work = df.copy()
        notes = []

        def cell_issue(i, col, value, what):
            issues.append({"kind": "cell", "file": name, "row": dict(df.loc[i]), "col": col, "value": str(value),
                           "what": what, "line": _line(work, i)})
        for c in must_dates + may_dates:                   # dates written another way -> YYYY-MM-DD
            for i, v in work[c].items():
                if not str(v).strip():
                    if c in must_dates:
                        cell_issue(i, c, "", "date is empty")
                    continue
                good = _fix_date(v)
                if good is None:
                    cell_issue(i, c, v, "date cannot be read")
                elif good != str(v):
                    work.at[i, c] = good
                    notes.append(f"{c} '{v}' → {good}")
        for i, v in work["Pcs"].items():                   # numbers typed with commas / spaces / .0
            good = _fix_pcs(v)
            if good is None:
                cell_issue(i, "Pcs", v, "pcs is not a number")
            else:
                if good != str(v):
                    work.at[i, "Pcs"] = good
                    notes.append(f"Pcs '{v}' → {good}")
                if not neg_ok and int(good) < 0:
                    cell_issue(i, "Pcs", good, "pcs is below 0")
        for i, v in work["Bun"].items():                   # 'n1 ' -> 'N1'
            good = str(v).strip().upper().replace(" ", "")
            if good in known:
                if good != str(v):
                    work.at[i, "Bun"] = good
                    notes.append(f"Bun '{v}' → {good}")
            else:
                cell_issue(i, "Bun", v, "unknown bun code")
        empty_id = work[idcol].astype(str).str.strip() == ""
        if empty_id.any():                                  # lines without an id cannot be fixed / undone
            for i in work.index[empty_id]:
                work.at[i, idcol] = "bot" + uuid.uuid4().hex[:8]
            notes.append(f"{int(empty_id.sum())} line(s) got a missing {idcol}")
        dup = work.duplicated(keep="first")                 # exactly the same line twice (a double save)
        if dup.any():
            notes.append(f"{int(dup.sum())} exact double line(s) removed")
            work = work[~dup]
        if notes and fix:
            _bot_backup(name)
            before = df.copy()

            def apply(cur, work=work, before=before):
                if len(cur) != len(before) or not cur.reset_index(drop=True).equals(before.reset_index(drop=True)):
                    raise Conflict("changed")              # someone saved meanwhile: the bot fixes it next time
                return work
            try:
                modify_csv(name, cols, apply)
                fixed.append(f"{name}: " + "; ".join(notes[:6]) + (f" … (+{len(notes) - 6})" if len(notes) > 6 else ""))
                bot_audit("bot fixed", fixed[-1])
            except Exception:
                pass
    # settings: values of the wrong type (text where a number must be, broken lists) -> repaired
    try:
        data, _r = read_bytes(SETTINGS_FILE, max_age=0)
        raw = json.loads(data.decode("utf-8")) if data else {}
        bad_s = _settings_problems(raw)
        if bad_s and fix:
            _bot_backup(SETTINGS_FILE)
            update_settings(_repair_settings)
            fixed.append("settings: " + "; ".join(bad_s[:6]))
            bot_audit("bot fixed", fixed[-1])
    except json.JSONDecodeError:
        issues.append({"kind": "info", "file": SETTINGS_FILE, "value": "", "col": "",
                       "what": "settings file is broken — the app uses the default settings",
                       "line": "Open ⚙️ Settings and press 💾 Save settings to write a good file again."})
    except Exception:
        pass
    return fixed, issues


def _line(df, i):
    r = df.loc[i]
    return " · ".join(f"{c} {r[c]}" for c in ("Saved_At", "Prod_Date", "Count_Date", "Date", "Bun", "Pcs", "By")
                      if c in r and str(r[c]).strip())[:160]


def _settings_problems(raw):
    out = []
    for k in ("max_total", "target_default", "shelf_days", "lookback_days", "round_to", "max_prod_per_day"):
        if k in raw:
            try:
                int(raw[k])
                if isinstance(raw[k], str):
                    out.append(f"{k} was text")
            except (TypeError, ValueError):
                out.append(f"{k} was not a number")
    for k in ("target_days", "shelf_by_bun", "crate_pcs"):
        for b, v in (raw.get(k) or {}).items() if isinstance(raw.get(k), dict) else []:
            try:
                int(v)
                if isinstance(v, str):
                    out.append(f"{k} {b} was text")
            except (TypeError, ValueError):
                out.append(f"{k} {b} was not a number")
    for b, v in (raw.get("prod_days") or {}).items() if isinstance(raw.get("prod_days"), dict) else []:
        if not isinstance(v, list) or any(not isinstance(x, int) or not 0 <= x <= 6 for x in v):
            out.append(f"prod_days {b} broken")
    return out


def _repair_settings(cur):
    for k in ("max_total", "target_default", "shelf_days", "lookback_days", "round_to", "max_prod_per_day"):
        if k in cur:
            try:
                cur[k] = int(float(cur[k]))
            except (TypeError, ValueError):
                cur[k] = DEFAULT_SETTINGS.get(k, 0)
    for k in ("target_days", "shelf_by_bun", "crate_pcs"):
        if isinstance(cur.get(k), dict):
            good = {}
            for b, v in cur[k].items():
                try:
                    good[b] = int(float(v))
                except (TypeError, ValueError):
                    pass                                    # dropped: the bun uses the default value
            cur[k] = good
    if isinstance(cur.get("prod_days"), dict):
        cur["prod_days"] = {b: sorted({int(x) for x in v if str(x).lstrip("-").isdigit() and 0 <= int(x) <= 6})
                            for b, v in cur["prod_days"].items() if isinstance(v, list)}


def bot_tick(cfg):
    """Runs the check by itself at most every 15 min (for the whole app, not per person)."""
    m = _mem()
    if time.time() - m.get("bot_t", 0) < BOT_EVERY_S:
        return
    m["bot_t"] = time.time()
    try:
        fixed, issues = bot_scan(cfg, fix=True)
        m["bot_last"] = {"t": now_kh().strftime("%d %b %H:%M"), "fixed": fixed, "issues": issues}
    except Exception as e:
        m["bot_last"] = {"t": now_kh().strftime("%d %b %H:%M"), "fixed": [], "issues": [],
                         "err": f"check could not finish: {e}"}


def log_error(page, err):
    tb = traceback.extract_tb(err.__traceback__)
    where = next((f"line {f.lineno} in {f.name}" for f in reversed(tb) if f.filename.endswith(".py")
                  and "site-packages" not in f.filename), "")
    m = _mem()
    key = (page, type(err).__name__, str(err)[:80])
    if time.time() - m.setdefault("err_seen", {}).get(key, 0) < 600:    # the same error: once per 10 min
        return
    m["err_seen"][key] = time.time()
    row = {"Time": now_kh().strftime("%Y-%m-%d %H:%M:%S"), "User": st.session_state.get("p_name", ""), "Page": page,
           "Error": f"{type(err).__name__}: {err}"[:300], "Where": where, "Result": ""}
    try:
        modify_csv(ERROR_FILE, ERROR_COLS, lambda df: pd.concat([df, pd.DataFrame([row])], ignore_index=True))
    except Exception:
        pass


def guarded(fn, page):
    """Runs a page. If it breaks: the bot clears the cache, repairs the data and tries once more by itself.
    Only if it still breaks is a short message shown (and the error kept for Admin / the developer)."""
    def run(*a, **k):
        heal = st.session_state.setdefault("_heal", {})
        try:
            fn(*a, **k)
            heal.pop(page, None)
        except Exception as err:
            log_error(page, err)
            if heal.get(page, 0) < 1:
                heal[page] = 1
                try:
                    m = _mem()
                    with m["lock"]:
                        m["files"].clear()
                        m["list"] = None
                    st.cache_data.clear()
                    bot_scan(a[0] if a and isinstance(a[0], dict) else load_settings()[0], fix=True)
                except Exception:
                    pass
                st.toast("🤖 A problem was found — the bot repaired the data and is trying again…")
                _rerun_here()
            heal.pop(page, None)
            st.error(f"⚠️ This part could not load: {err}. The 🤖 bot already tried to repair it and kept the error "
                     "for Admin. Your saved data is safe — try again in a minute.")
            if st.session_state.get("p_role") == "admin":
                with st.expander("Details for Admin"):
                    st.exception(err)
    run.__name__ = getattr(fn, "__name__", "page")
    run.__qualname__ = f"guarded_{run.__name__}"           # each page keeps its own fragment
    return run


def page_bot(cfg):
    st.subheader("🤖 Auto-fix bot")
    st.caption("The bot checks the data files by itself every 15 minutes and whenever a page breaks. It repairs safe "
               "problems at once (always keeping a backup first) and lists here what needs a person.")
    show_flash("bot_flash")
    c1, c2 = st.columns([1, 3])
    if c1.button("🔍 Check now", type="primary", width="stretch", key="bot_now"):
        with st.spinner("Checking every file…"):
            fixed, issues = bot_scan(cfg, fix=True)
        _mem()["bot_last"] = {"t": now_kh().strftime("%d %b %H:%M"), "fixed": fixed, "issues": issues}
        _mem()["bot_t"] = time.time()
    last = _mem().get("bot_last")
    if last:
        c2.markdown(f"Last check: **{last['t']}** · fixed **{len(last['fixed'])}** · need you **{len(last['issues'])}**"
                    + (f" · ⚠️ {last['err']}" if last.get("err") else ""))
        for f in last["fixed"]:
            st.success("🔧 " + f)
        issues = last["issues"]
        if issues:
            st.markdown("#### 🙋 Needs a person")
            for k, it in enumerate(issues[:40]):
                with st.container(border=True):
                    a, b = st.columns([3, 2])
                    a.markdown(f"**{it['what']}** · `{it['file']}`" + (f" · value: `{it['value']}`"
                                                                        if it["value"] and it["kind"] == "cell" else ""))
                    a.caption(it["line"])
                    if it["kind"] == "info":
                        continue
                    if it["kind"] == "line":
                        newv = b.text_input("Correct line", value=",".join(it["fields"]), key=f"bot_v_{k}",
                                            help="Columns: " + ",".join(it["header"]) + ' — put "quotes" around a '
                                                 "number with a comma, or remove the comma.",
                                            label_visibility="collapsed")
                    elif it["col"] == "Pcs":
                        newv = b.text_input("Right pcs", key=f"bot_v_{k}", placeholder="e.g. 1200",
                                            label_visibility="collapsed")
                    elif it["col"] == "Bun":
                        newv = b.selectbox("Right bun", sorted(set(DEFAULT_BUNS) | set(cfg.get("target_days") or {})),
                                           index=None, key=f"bot_v_{k}", placeholder="Choose the bun",
                                           label_visibility="collapsed")
                    else:
                        d = b.date_input("Right date", value=None, key=f"bot_v_{k}", label_visibility="collapsed")
                        newv = d.isoformat() if d else None
                    x, y = b.columns(2)
                    if x.button("✅ Fix", key=f"bot_fix_{k}", disabled=not newv, width="stretch"):
                        _bot_fix(it, newv, delete=False)
                    if y.button("🗑️ Delete line", key=f"bot_del_{k}", width="stretch"):
                        _bot_fix(it, None, delete=True)
        elif not last.get("err"):
            st.info("✅ Nothing needs you — all data files are fine.")
    else:
        st.info("The first check runs within a minute of opening the app — or press 🔍 Check now.")
    st.markdown("#### ⚠️ Page errors kept by the bot")
    errs, _r = read_csv(ERROR_FILE, ERROR_COLS, max_age=5)
    if errs.empty:
        st.caption("No page errors. 👍")
    else:
        errs = errs.sort_values("Time", ascending=False)
        st.dataframe(errs.head(100), hide_index=True, width="stretch")
        st.caption("Errors the bot cannot repair by itself are mistakes in the program — send this list (or a screenshot) "
                   "to get the program fixed. Tick them off below when solved.")
        if st.button("🧹 Clear the error list", key="bot_clear_err"):
            modify_csv(ERROR_FILE, ERROR_COLS, lambda df: df.iloc[0:0])
            audit("bot errors cleared", f"{len(errs)} errors")
            st.session_state["bot_flash"] = "🧹 Error list cleared."
            _rerun_here()
    log, _r = read_csv(AUDIT_FILE, AUDIT_COLS, max_age=5)
    mine = log[log["User"] == "bot"].sort_values("Time", ascending=False) if not log.empty else log
    if not mine.empty:
        st.markdown("#### 🔧 What the bot repaired")
        st.dataframe(mine[["Time", "Action", "Detail"]].head(100), hide_index=True, width="stretch")


def _bot_fix(it, val, delete):
    """Admin's one-tap fix of one problem the bot could not repair alone (a backup is kept first)."""
    name = it["file"]
    cols = next(x[1] for x in BOT_FILES if x[0] == name)
    try:
        if it["kind"] == "line":
            new_fields = None
            if not delete:
                new_fields = next(csv.reader(io.StringIO(val)), [])
                if len(new_fields) != len(it["header"]):
                    st.error(f"The line has {len(new_fields)} columns — it needs {len(it['header'])}. "
                             'Put "quotes" around a number with a comma (e.g. "1,200") or remove the comma.')
                    return
            _bot_backup(name)
            _write_lines(name, cols, it["header"], {tuple(it["fields"]): new_fields})
        else:
            if not delete and it["col"] == "Pcs":
                val = _fix_pcs(val)
                if val is None:
                    st.error("Type numbers only.")
                    return

            def ch(df):
                m = pd.Series(True, index=df.index)
                for c, v in it["row"].items():               # exactly that line (all columns the same)
                    m &= df[c].astype(str) == str(v)
                hit = df.index[m]
                if not len(hit):
                    return df
                if delete:
                    return df.drop(hit[:1])
                df.loc[hit[:1], it["col"]] = val
                return df
            _bot_backup(name)
            modify_csv(name, cols, ch)
        audit("bot issue " + ("deleted" if delete else "fixed"),
              f"{name}: {it['line']} · {it.get('col') or 'line'} → {'deleted' if delete else val}")
        last = _mem().get("bot_last") or {}
        last["issues"] = [x for x in last.get("issues", []) if x is not it]
        st.session_state["bot_flash"] = "✅ Done — " + ("line deleted." if delete else "fixed.")
        _rerun_here()
    except Exception as e:
        st.error(f"Not changed: {e}")


def bot_banner():
    """Admin: one line at the top when the bot needs you or saw errors today."""
    last = _mem().get("bot_last") or {}
    need = len(last.get("issues", []))
    try:
        errs, _r = read_csv(ERROR_FILE, ERROR_COLS)
        today_errs = int((errs["Time"].astype(str).str[:10] == today_kh().isoformat()).sum()) if not errs.empty else 0
    except Exception:
        today_errs = 0
    if need or today_errs:
        st.warning(f"🤖 Bot: {need} data problem(s) need you · {today_errs} page error(s) today — open **🤖 Bot**.")


# ==========================================
# MAIN
# ==========================================
st.markdown(CSS, unsafe_allow_html=True)
_logged = bool(st.session_state.get("p_user")) or restore_login()
# 🌐 English / ខ្មែរ — remembered per person (and in the link: ?lang=km)
if "lang" not in st.session_state:
    try:
        _q = st.query_params.get("lang", "")
    except Exception:
        _q = ""
    st.session_state["lang"] = _q if _q in LANGS else "en"
if _logged and not st.session_state.get("lang_user_done"):
    st.session_state["lang_user_done"] = True
    try:
        _pref = (load_settings()[0].get("lang_by_user") or {}).get(st.session_state.get("p_user"))
        if _pref in LANGS and not st.session_state.get("lang_dirty"):
            st.session_state["lang"] = _pref
    except Exception:
        pass
_l1, _l2 = st.columns([5, 2])
_l2.radio("🌐", list(LANGS), format_func=lambda x: LANGS[x], key="lang", horizontal=True,
          label_visibility="collapsed", on_change=lambda: st.session_state.update(lang_dirty=True))
try:
    st.query_params["lang"] = st.session_state["lang"]
except Exception:
    pass
if not _logged:
    login_box()
if st.session_state.get("p_tok") and (st.session_state.pop("p_cookie_set", False)
                                      or time.time() - st.session_state.get("p_cookie_t", 0) > 600):
    _js(_js_set_cookie(st.session_state["p_tok"]))           # written again every 10 min (iPhone Safari keeps it fresh)
    st.session_state["p_cookie_t"] = time.time()
cfg, _srev = load_settings()
me_user, me_role = st.session_state["p_user"], st.session_state.get("p_role", "staff")
if st.session_state.pop("lang_dirty", False) and (cfg.get("lang_by_user") or {}).get(me_user) != lang():
    try:                                                     # remember the language of this person
        update_settings(lambda c: c.setdefault("lang_by_user", {}).update({me_user: lang()}))
    except Exception:
        pass
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
bot_tick(cfg)                                       # 🤖 checks / repairs the data files by itself (every 15 min)
if me_role == "admin":
    bot_banner()
pages = ["📊 Live stock", "🏭 Log production", "📦 Stock count", "🧊 3D rooms", "📋 Tasks", "📅 Next week plan",
         "🕘 History"]
if me_role == "admin":
    pages += ["🤖 Bot", "⚙️ Settings"]
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

if page == "📊 Live stock":
    live = st.toggle("🔄 Update by itself every 60 s", value=True, key="live_on")
    frag = st.fragment(run_every=60)(guarded(page_live, page)) if live else st.fragment(guarded(page_live, page))
    frag(cfg, can_edit)
elif page == "🏭 Log production":
    st.fragment(guarded(page_production, page))(cfg, can_edit, me)
elif page == "📦 Stock count":
    st.fragment(guarded(page_count, page))(cfg, can_edit, me)
elif page == "📅 Next week plan":
    st.fragment(guarded(page_plan, page))(cfg, can_edit)
elif page == "🧊 3D rooms":
    st.fragment(guarded(page_rooms, page))(cfg)
elif page == "📋 Tasks":
    guarded(page_tasks, page)(cfg, can_edit, me)
elif page == "🕘 History":
    st.fragment(guarded(page_history, page))(cfg, me)
elif page == "🤖 Bot":
    st.fragment(guarded(page_bot, page))(cfg)
else:
    guarded(page_settings, page)(cfg, me)
