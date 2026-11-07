import os
import io
import csv
import re
import html
import json
import hashlib
import hmac
import smtplib
from difflib import SequenceMatcher
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
from email.message import EmailMessage
import urllib3
import requests
import fitz  # PyMuPDF

# Suppress warnings when bypassing DoD SSL certificate verification
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# Configuration
DEFAULT_LAST_NAME = os.getenv("STUDENT_LAST_NAME", "Hagemaster")
DEFAULT_FIRST_NAME = os.getenv("STUDENT_FIRST_NAME", "Cameron")
GMAIL_USER = os.environ["GMAIL_USER"].strip()
GMAIL_APP_PASSWORD = os.environ["GMAIL_APP_PASSWORD"].strip()
ROSTER_CSV_URL = os.getenv("ROSTER_CSV_URL", "").strip()
SIGNUP_FORM_URL = os.getenv("SIGNUP_FORM_URL", "").strip()
GITHUB_REPO_URL = "https://github.com/syttix/vt10-sked-bot"
# Secret key for anonymizing per-student data in the public state.json. A plain hash of a
# name could be reversed by hashing every name on the (public) CNATRA PDF, so a keyed HMAC
# is used instead. Defaults to the Gmail app password; set STATE_HMAC_KEY to decouple them.
STATE_HMAC_KEY = (os.getenv("STATE_HMAC_KEY", "").strip() or GMAIL_APP_PASSWORD).encode("utf-8")

STATE_FILE = "state.json"
QOD_BANK_FILE = "qod_bank.json"
TZ = ZoneInfo("America/Chicago")

RANKS = r"(?:CIV|ENS|LTJG|LT|LCDR|CDR|CAPT|Capt|Maj|LtCol|Col|1stLt|2ndLt|2LT|CWO\d|ctr)"
NAME_PATTERN = rf"[A-Za-z'\-]+,\s*[A-Za-z\.]+,\s*{RANKS}"
SIM_KEYWORDS = ("UTD", "OFT", "IFT", "VTD", "SIM", "MCS", "2B47", "2F198", "ACA")
WATCH_KEYWORDS_REGEX = r"\b(ASDO|AFDO|SDO|CDO|ODO|FDO|Duty\s+Officer|SUPER|WHEELS\s+WATCH|DUTY\s+DRIVER|Watches|STANDBY|STDBY|STBY|ADMIN\s+HOLD)\b"


def get_target_dates(now: datetime) -> list[datetime]:
    test_date = os.getenv("TEST_DATE", "").strip()
    if test_date:
        return [datetime.strptime(test_date, "%Y-%m-%d").replace(tzinfo=TZ)]

    if now.hour < 6:
        now = now - timedelta(hours=6)

    weekday = now.weekday()
    if weekday == 4:  # Friday
        return [now + timedelta(days=i) for i in (1, 2, 3)]
    elif weekday == 5:  # Saturday
        return [now + timedelta(days=i) for i in (1, 2)]
    else:  # Mon-Thu (or Sunday)
        return [now + timedelta(days=1)]


def load_state() -> dict:
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except json.JSONDecodeError:
            return {}
    return {}


def save_state(state: dict) -> None:
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f, indent=2, sort_keys=True)


def get_date_state(state: dict, date_str: str) -> tuple[str | None, dict]:
    """
    Returns (pdf_hash, student_fingerprints) for a date.
    Handles the legacy format where the value was just the PDF hash string
    (no per-student fingerprints -> everyone is treated as changed).
    """
    entry = state.get(date_str)
    if isinstance(entry, str):
        return entry, {}
    if isinstance(entry, dict):
        return entry.get("pdf_hash"), dict(entry.get("students", {}))
    return None, {}


def _keyed_hash(kind: str, value: str) -> str:
    return hmac.new(STATE_HMAC_KEY, f"{kind}:{value}".encode("utf-8"), hashlib.sha256).hexdigest()[:16]


def student_state_key(last_name: str, first_name: str) -> str:
    """Anonymized per-student key (state.json is committed to a public repo)."""
    raw = f"{last_name.strip().lower()}_{(first_name or '').strip().lower()}"
    return _keyed_hash("student", raw)


def student_schedule_fingerprint(parsed: dict) -> str:
    """
    Hash of only the student-specific parts of the schedule. Questions of the day
    are excluded since they are shared by everyone and not 'their' information.
    """
    relevant = {
        k: parsed[k]
        for k in ("flights_and_sims", "ground_events", "watches", "duties_and_notes", "leave_tad")
    }
    # For unscheduled students the phone-muster note decides their status, so it counts as theirs
    if not any(relevant.values()):
        relevant["phone_muster_required"] = parsed.get("phone_muster_required", False)
    blob = json.dumps(relevant, sort_keys=True, ensure_ascii=False)
    # Keyed so the public value can't be matched against fingerprints computed from the PDF
    return _keyed_hash("schedule", blob)


def load_qod_bank() -> dict:
    if os.path.exists(QOD_BANK_FILE):
        try:
            with open(QOD_BANK_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except json.JSONDecodeError as e:
            print(f"Warning: Failed to parse {QOD_BANK_FILE}: {e}")
    return {}


def load_roster(is_manual_test: bool) -> tuple[list[dict], dict]:
    """
    Loads students from the live Google Sheet CSV (ROSTER_CSV_URL).
    Stores full first_name and derived first_initial for multi-squadron compatibility.
    TEST SAFETY LOCK: If is_manual_test is True, routes ONLY to GMAIL_USER (the SkedBot email).
    """
    diag = {
        "csv_configured": bool(ROSTER_CSV_URL),
        "csv_fetch_ok": False,
        "raw_rows_processed": 0,
        "unsubscribed_count": 0,
        "active_count": 0,
        "error": None,
    }

    if is_manual_test:
        test_student = os.getenv("TEST_STUDENT", "").strip() or DEFAULT_LAST_NAME
        print("[TEST MODE ACTIVE] Routing test schedule strictly to SkedBot inbox.")
        test_roster = [{
            "last_name": test_student,
            "first_name": "",
            "first_initial": "",
            "email": GMAIL_USER,
            "is_admin": True,
        }]
        diag["active_count"] = 1
        return test_roster, diag

    roster_by_key: dict[str, dict] = {}

    if ROSTER_CSV_URL:
        try:
            resp = requests.get(ROSTER_CSV_URL, timeout=15)
            resp.raise_for_status()
            diag["csv_fetch_ok"] = True
            reader = csv.DictReader(io.StringIO(resp.text))
            for row in reader:
                diag["raw_rows_processed"] += 1
                norm_row = {k.strip().lower(): (v or "").strip() for k, v in row.items() if k}
                last_name = next((v for k, v in norm_row.items() if "last" in k), "")
                first_name = next(
                    (v for k, v in norm_row.items() if "first" in k or "initial" in k), ""
                )
                email = next(
                    (v for k, v in norm_row.items() if "email" in k or "mail" in k), ""
                )
                action = next(
                    (v for k, v in norm_row.items() if "action" in k or "status" in k),
                    "subscribe",
                )

                if not last_name or not email:
                    continue

                first_name_clean = first_name.strip()
                first_init = first_name_clean[:1].upper()
                key = f"{last_name.lower()}_{first_name_clean.lower()}"

                if "unsub" in action.lower() or "stop" in action.lower():
                    if key in roster_by_key:
                        roster_by_key.pop(key, None)
                        diag["unsubscribed_count"] += 1
                else:
                    roster_by_key[key] = {
                        "last_name": last_name,
                        "first_name": first_name_clean,
                        "first_initial": first_init,
                        "email": email,
                        "is_admin": last_name.lower() == DEFAULT_LAST_NAME.lower(),
                    }
        except Exception as e:
            diag["error"] = str(e)
            print(f"Warning: Failed to fetch ROSTER_CSV_URL: {e}")

    roster = list(roster_by_key.values())

    if not roster:
        roster = [{
            "last_name": DEFAULT_LAST_NAME,
            "first_name": DEFAULT_FIRST_NAME,
            "first_initial": DEFAULT_FIRST_NAME[:1].upper(),
            "email": GMAIL_USER,
            "is_admin": True,
        }]

    diag["active_count"] = len(roster)
    return roster, diag


def normalize_q_text(text: str) -> str:
    t = text.upper()
    t = re.sub(r"\((?:COMTRAWINGSIX|TRARONTEN|CNAF|FAR|PG).*?\)", " ", t)
    t = re.sub(r"_+", " ", t)
    t = re.sub(r"[^A-Z0-9\s]", " ", t)
    return re.sub(r"\s+", " ", t).strip()


def lookup_qod_answer(category: str, question_text: str, qod_bank: dict) -> str | None:
    if not question_text or question_text.upper() in ("N/A", "NONE", "-"):
        return None

    norm_q = normalize_q_text(question_text)
    if not norm_q:
        return None

    candidates = list(qod_bank.get(category, []))
    for cat, items in qod_bank.items():
        if cat != category:
            candidates.extend(items)

    best_answer = None
    best_score = 0.0
    q_tokens = set(norm_q.split())

    for item in candidates:
        norm_cand = normalize_q_text(item["q"])
        if not norm_cand:
            continue

        if norm_q == norm_cand:
            return item["a"]
        if len(norm_cand) >= 4 and (norm_cand in norm_q or norm_q in norm_cand):
            score = 0.92
        else:
            seq_ratio = SequenceMatcher(None, norm_q, norm_cand).ratio()
            cand_tokens = set(norm_cand.split())
            overlap = (
                len(q_tokens & cand_tokens) / max(len(q_tokens), len(cand_tokens))
                if q_tokens and cand_tokens
                else 0.0
            )
            score = max(seq_ratio, overlap * 0.95)

        if score > best_score:
            best_score = score
            best_answer = item["a"]

    return best_answer if best_score >= 0.58 else None


def is_simulator_event(device: str, event_code: str) -> bool:
    dev_upper = device.upper()
    evt_upper = event_code.upper()
    if any(k in dev_upper for k in SIM_KEYWORDS):
        return True
    if re.search(r"[A-Z]+\d{4}", evt_upper) and len(evt_upper) >= 7:
        digit_part = re.search(r"\d{4}", evt_upper).group(0)
        if digit_part.startswith(("1", "2", "3")):
            return True
    return False


def fetch_valid_pdf(date_str: str) -> bytes | None:
    url = f"https://www.cnatra.navy.mil/scheds/TW6/SQ-VT-10/!{date_str}!VT-10!Frontpage.pdf"
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"
        ),
        "Accept": "application/pdf,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    }

    try:
        resp = requests.get(url, headers=headers, timeout=25, verify=False)
    except requests.RequestException as e:
        print(f"[{date_str}] Network error reaching CNATRA: {e}")
        return None

    if resp.status_code != 200:
        print(f"[{date_str}] HTTP {resp.status_code} - Not posted yet.")
        return None

    if b"%PDF-" not in resp.content[:1024] or len(resp.content) < 2000:
        snippet = resp.text[:120].replace("\n", " ").strip()
        print(f"[{date_str}] Not a PDF yet (Server returned: {snippet!r})")
        return None

    try:
        doc = fitz.open(stream=resp.content, filetype="pdf")
        if doc.page_count == 0:
            return None
        first_page_text = doc[0].get_text("text")
        if "CNATRA website error" in first_page_text or "VT-10" not in first_page_text:
            print(f"[{date_str}] PDF failed VT-10 content verification.")
            return None
    except Exception as e:
        print(f"[{date_str}] Invalid PDF stream: {e}")
        return None

    return resp.content


def parse_questions_of_the_day(page1_text: str) -> dict:
    questions = {"EOD": "N/A", "IOD": "N/A", "QOD": "N/A", "SOP": "N/A", "WOD": "N/A"}

    block_match = re.search(
        r"Questions:(.*?)(?:DUTY/WATCH|AC IN REPORTING|TIME\s+EVENT)",
        page1_text,
        re.DOTALL | re.IGNORECASE,
    )
    search_area = block_match.group(1) if block_match else page1_text
    normalized = re.sub(r"\s+", " ", search_area)

    patterns = {
        "EOD": r"EOD:\s*(.*?)(?=\s+(?:IOD|QOD|SOP|WOD):|$)",
        "IOD": r"IOD:\s*(.*?)(?=\s+(?:QOD|SOP|WOD):|$)",
        "QOD": r"QOD:\s*(.*?)(?=\s+(?:SOP|WOD):|$)",
        "SOP": r"SOP:\s*(.*?)(?=\s+(?:WOD):|$)",
        "WOD": r"WOD:\s*(.*?)(?=$)",
    }
    for key, pat in patterns.items():
        m = re.search(pat, normalized, re.IGNORECASE)
        if m:
            questions[key] = m.group(1).strip()

    return questions


def parse_flight_or_sim_line(line: str, last_name: str) -> dict:
    m = re.match(r"^(\d{4})\s+(\d{4})\s+(\d{4})\s+(.*)", line)
    if not m:
        return {"raw": line, "is_sim": False}

    brief, to_time, land, rest = m.groups()
    names = list(re.finditer(NAME_PATTERN, rest))
    device = "N/A"
    instructor = "N/A"
    student = last_name
    tail = rest

    if len(names) >= 2:
        device = rest[: names[0].start()].strip()
        instructor = names[0].group(0).strip()
        student = names[1].group(0).strip()
        tail = rest[names[1].end() :].strip()
    elif len(names) == 1:
        device = rest[: names[0].start()].strip()
        matched_name = names[0].group(0).strip()
        if last_name.lower() in matched_name.lower():
            student = matched_name
            instructor = "Solo / None"
        else:
            instructor = matched_name
        tail = rest[names[0].end() :].strip()

    tail_match = re.match(r"^(\S+)\s+(\d+\.\d+)\s*(.*)", tail)
    if tail_match:
        event_code, hours, remarks = tail_match.groups()
    else:
        parts = tail.split(maxsplit=1)
        event_code = parts[0] if parts else "EVENT"
        hours = "N/A"
        remarks = parts[1] if len(parts) > 1 else ""

    clean_device = device or "Aircraft / Sim"
    is_sim = is_simulator_event(clean_device, event_code)

    return {
        "brief": brief,
        "to": to_time,
        "land": land,
        "device": clean_device,
        "instructor": instructor,
        "student": student,
        "event": event_code,
        "hours": hours,
        "remarks": remarks.strip() or "None",
        "is_sim": is_sim,
        "raw": line,
    }


def parse_ground_block(lines: list[str]) -> dict:
    combined = " ".join(lines)
    m = re.match(r"^(\d{4}-\d{4})\s+(\S+)\s+(Room\s+\S+|\S+)\s+(.*)", combined)
    if not m:
        return {"raw": combined}

    time_range, event_code, location, remainder = m.groups()
    start_t, end_t = time_range.split("-")

    all_names = list(re.finditer(NAME_PATTERN, remainder))
    instructor = "See PDF"
    remarks = "None"

    upper_names = [
        n for n in all_names if n.group(0).split(",")[0].strip().isupper()
    ]
    if upper_names:
        inst_match = upper_names[-1]
        instructor = inst_match.group(0).strip()
        after_inst = remainder[inst_match.end() :].strip()
        if after_inst:
            remarks = after_inst

    return {
        "time": time_range,
        "start": start_t,
        "end": end_t,
        "event": event_code,
        "location": location,
        "instructor": instructor,
        "remarks": remarks,
        "raw": combined,
    }


def is_watch_or_duty_line(line: str) -> bool:
    if re.search(WATCH_KEYWORDS_REGEX, line, re.IGNORECASE):
        return True
    if re.match(r"^\d{4}-\d{4}:", line):
        return True
    return False


def parse_watch_or_duty_line(line: str, last_name: str) -> dict:
    role_match = re.search(WATCH_KEYWORDS_REGEX, line, re.IGNORECASE)
    watch_type = role_match.group(1).upper() if role_match else "DUTY / WATCH"
    if watch_type in ("STBY", "STDBY"):
        watch_type = "STANDBY"

    time_match = re.search(r"(\d{4})\s*-\s*(\d{4})", line)
    if time_match:
        start_t, end_t = time_match.group(1), time_match.group(2)
        time_window = f"{start_t}-{end_t}"
    else:
        two_four_digits = re.findall(r"\b(\d{4})\b", line)
        if len(two_four_digits) >= 2:
            start_t, end_t = two_four_digits[0], two_four_digits[1]
            time_window = f"{start_t}-{end_t}"
        elif len(two_four_digits) == 1:
            start_t = two_four_digits[0]
            end_t = "TBD"
            time_window = start_t
        else:
            start_t = "See PDF"
            end_t = "See PDF"
            time_window = "All Day / See PDF"

    names = [m.group(0).strip() for m in re.finditer(NAME_PATTERN, line)]
    student_entry = last_name
    other_personnel = []
    for n in names:
        if last_name.lower() in n.lower():
            student_entry = n
        else:
            other_personnel.append(n)

    location = (
        "Quarterdeck / ASDO Desk"
        if "ASDO" in watch_type or "SDO" in watch_type
        else "Squadron / Ready Room"
    )

    return {
        "watch_type": watch_type,
        "time": time_window,
        "start": start_t,
        "end": end_t,
        "student": student_entry,
        "other_personnel": ", ".join(other_personnel) if other_personnel else "None listed",
        "location": location,
        "raw": line,
    }


def extract_pdf_lines(pdf_bytes: bytes, qod_bank: dict) -> dict:
    doc = fitz.open(stream=pdf_bytes, filetype="pdf")
    full_text_pages = [page.get_text("text") for page in doc]

    questions = (
        parse_questions_of_the_day(full_text_pages[0]) if full_text_pages else {}
    )
    answers = {
        key: lookup_qod_answer(key, q_text, qod_bank)
        for key, q_text in questions.items()
    }

    pages_logical_lines = []
    for page in doc:
        page_text = page.get_text("text")
        if "Build Report by Go's" in page_text:
            continue

        words = page.get_text("words")
        lines_by_y = {}
        for w in words:
            y_key = round(w[1] / 3.0) * 3
            lines_by_y.setdefault(y_key, []).append(w)

        logical_lines = [
            " ".join(w[4] for w in sorted(lines_by_y[y], key=lambda item: item[0]))
            for y in sorted(lines_by_y.keys())
        ]
        pages_logical_lines.append(logical_lines)

    # Phone muster is only shown for unscheduled weekday students when the schedule
    # notes actually call for it (some days unscheduled students have other tasking).
    # Expected note: "0700-0800: PHONE MUSTER (ASDO 850-452-4669) ALL UNSCHEDULED STUDENTS"
    muster_lines = [
        line
        for logical_lines in pages_logical_lines
        for line in logical_lines
        if re.search(r"\bPHONE\s+MUSTER\b", line, re.IGNORECASE)
        and re.search(r"\bALL\s+UNSCHEDULED\s+STUDENTS\b", line, re.IGNORECASE)
    ]

    return {
        "page_count": doc.page_count,
        "questions": questions,
        "answers": answers,
        "pages_lines": pages_logical_lines,
        "phone_muster_required": bool(muster_lines),
        "muster_lines": muster_lines,
    }


def build_student_name_regex(last_name: str, first_name: str = "") -> re.Pattern:
    """
    Matches:
    - "Lastname, Firstname" (VT-2 full first name style, with optional #)
    - "Lastname, F" (VT-10 first initial style)
    - Standalone "Lastname" when NOT followed by a comma and a different initial/name
      (so "DET ASDO Barr" or "LEAVE/TAD: HAGEMASTER" matches, while a sibling/classmate
      with the same last name but different first name/initial is excluded).
    """
    clean_first = re.sub(r"[^A-Za-z]", "", first_name or "")
    if not clean_first:
        return re.compile(rf"\b{re.escape(last_name)}\b", re.IGNORECASE)

    first_init = clean_first[0]
    pattern = (
        rf"\b{re.escape(last_name)}"
        rf"(?:"
        rf",\s*{re.escape(clean_first)}\b"
        rf"|,\s*{re.escape(first_init)}(?:\b|\.)"
        rf"|(?![,\s]+[A-Za-z])"
        rf")"
    )
    return re.compile(pattern, re.IGNORECASE)


UNSCHEDULED_STATUSES = ("WEEKEND OFF", "PHONE MUSTER", "UNSCHEDULED")


def determine_schedule_status(parsed: dict, is_weekend: bool) -> str:
    """
    Returns the primary status tag for the email subject and header badge:
    - Both Flight/Sim/Ground AND Watch -> 'SCHEDULED + WATCH'
    - Only Watch -> 'WATCH'
    - Flight/Sim/Ground/Note/Leave -> 'SCHEDULED'
    - Unscheduled Weekend -> 'WEEKEND OFF'
    - Unscheduled Weekday, schedule notes mention muster -> 'PHONE MUSTER'
    - Unscheduled Weekday, no muster note -> 'UNSCHEDULED'
    """
    has_watch = bool(parsed["watches"])
    has_other_events = any([
        parsed["flights_and_sims"],
        parsed["ground_events"],
        parsed["duties_and_notes"],
        parsed["leave_tad"],
    ])
    if has_watch and has_other_events:
        return "SCHEDULED + WATCH"
    if has_watch:
        return "WATCH"
    if has_other_events:
        return "SCHEDULED"
    if is_weekend:
        return "WEEKEND OFF"
    return "PHONE MUSTER" if parsed.get("phone_muster_required") else "UNSCHEDULED"


def parse_student_schedule(extracted_pdf: dict, last_name: str, first_name: str = "") -> dict:
    parsed = {
        "student_name": last_name,
        "first_name": first_name,
        "questions": extracted_pdf["questions"],
        "answers": extracted_pdf["answers"],
        "flights_and_sims": [],
        "ground_events": [],
        "watches": [],
        "duties_and_notes": [],
        "leave_tad": False,
        "phone_muster_required": extracted_pdf.get("phone_muster_required", False),
    }

    name_regex = build_student_name_regex(last_name, first_name)

    for logical_lines in extracted_pdf["pages_lines"]:
        current_ground_lines = []
        in_ground_block = False

        for line in logical_lines:
            if line.startswith("LEAVE/TAD:") and name_regex.search(line):
                parsed["leave_tad"] = True

            # Ground Event block start (excludes watch lines like '0730-1530 ASDO ...')
            if re.match(
                r"^\d{4}-\d{4}\s+(?!(?:ASDO|AFDO|SDO|ODO|CDO|FDO|DUTY|WATCH|STBY|STDBY|STANDBY)\b)[A-Z0-9]{3,}",
                line,
                re.IGNORECASE,
            ):
                if in_ground_block and name_regex.search(" ".join(current_ground_lines)):
                    parsed["ground_events"].append(parse_ground_block(current_ground_lines))
                in_ground_block = True
                current_ground_lines = [line]
                continue

            if in_ground_block:
                if (
                    "---" in line
                    or line.startswith("LEAVE/TAD")
                    or "SCHEDULES OFFICER" in line
                    or re.match(r"^\d{4}-\d{4}:", line)
                    or is_watch_or_duty_line(line)
                ):
                    if name_regex.search(" ".join(current_ground_lines)):
                        parsed["ground_events"].append(parse_ground_block(current_ground_lines))
                    in_ground_block = False
                    current_ground_lines = []
                else:
                    current_ground_lines.append(line)
                    continue

            if name_regex.search(line):
                if re.match(r"^\d{4}\s+\d{4}\s+\d{4}", line):
                    parsed["flights_and_sims"].append(parse_flight_or_sim_line(line, last_name))
                elif is_watch_or_duty_line(line):
                    parsed["watches"].append(parse_watch_or_duty_line(line, last_name))
                elif not line.startswith("LEAVE/TAD:"):
                    parsed["duties_and_notes"].append(line)

        if in_ground_block and name_regex.search(" ".join(current_ground_lines)):
            parsed["ground_events"].append(parse_ground_block(current_ground_lines))

    return parsed


def build_checkered_strip_html() -> str:
    num_cols = 16
    row1_cells = []
    row2_cells = []
    for i in range(num_cols):
        c1 = "#005a32" if i % 2 == 0 else "#ffffff"
        c2 = "#ffffff" if i % 2 == 0 else "#005a32"
        row1_cells.append(
            f'<td width="{100/num_cols:.2f}%" height="10" bgcolor="{c1}" '
            f'style="background-color:{c1}; font-size:1px; line-height:1px;">&nbsp;</td>'
        )
        row2_cells.append(
            f'<td width="{100/num_cols:.2f}%" height="10" bgcolor="{c2}" '
            f'style="background-color:{c2}; font-size:1px; line-height:1px;">&nbsp;</td>'
        )
    return f"""
    <table width="100%" cellpadding="0" cellspacing="0" border="0" style="border-collapse:collapse;">
      <tr>{''.join(row1_cells)}</tr>
      <tr>{''.join(row2_cells)}</tr>
    </table>
    """


def build_plain_text_body(target_dt: datetime, parsed: dict, is_update: bool, filename: str) -> str:
    date_str = target_dt.strftime("%A, %b %d, %Y")
    pdf_url = (
        f"https://www.cnatra.navy.mil/scheds/TW6/SQ-VT-10/"
        f"!{target_dt.strftime('%Y-%m-%d')}!VT-10!Frontpage.pdf"
    )
    is_weekend = target_dt.weekday() >= 5
    status_tag = determine_schedule_status(parsed, is_weekend)
    has_events = status_tag not in UNSCHEDULED_STATUSES

    lines = []
    if is_update:
        lines.append("SCHEDULE UPDATE DETECTED (Revised PDF posted — your schedule changed)\n")

    lines.append(f"VT-10 Schedule Summary for {parsed['student_name']} — {date_str}")
    lines.append("=" * 54)

    if not has_events:
        if is_weekend:
            lines.append("\nSTATUS: UNSCHEDULED — Weekend (No phone muster required).")
        elif status_tag == "PHONE MUSTER":
            lines.append("\nSTATUS: UNSCHEDULED — 0700-0800 Phone Muster required (ASDO 850-452-4669).")
        else:
            lines.append("\nSTATUS: UNSCHEDULED — See the schedule notes in the attached PDF.")
    else:
        for f in parsed["flights_and_sims"]:
            icon = "🖥️ SIM" if f.get("is_sim") else "✈️ FLIGHT"
            if "event" in f:
                lines.append(
                    f"\n{icon}: {f['event']} ({f['device']})\n"
                    f"   • Brief:      {f['brief']} | T/O: {f['to']} | Land: {f['land']} ({f['hours']} hrs)\n"
                    f"   • Instructor: {f['instructor']}\n"
                    f"   • Remarks:    {f['remarks']}"
                )
            else:
                lines.append(f"\n{icon}: {f['raw']}")

        for w in parsed["watches"]:
            lines.append(
                f"\n🛡️ WATCH / DUTY: {w['watch_type']} ({w['location']})\n"
                f"   • Window:     {w['time']}\n"
                f"   • Assigned:   {w['student']}\n"
                f"   • Co-Watch:   {w['other_personnel']}\n"
                f"   • Raw Line:   {w['raw']}"
            )

        for g in parsed["ground_events"]:
            if "event" in g:
                lines.append(
                    f"\n🎓 GROUND: {g['event']} ({g['location']})\n"
                    f"   • Time:       {g['time']}\n"
                    f"   • Instructor: {g['instructor']}\n"
                    f"   • Remarks:    {g['remarks']}"
                )
            else:
                lines.append(f"\n🎓 {g['raw']}")

        for d in parsed["duties_and_notes"]:
            lines.append(f"\nNOTE: {d}")

    q = parsed["questions"]
    a = parsed.get("answers", {})
    lines.append("\n" + "-" * 54)
    lines.append("QUESTIONS OF THE DAY (+ STUDY ANSWERS):")
    for key in ("EOD", "IOD", "QOD", "SOP", "WOD"):
        q_val = q.get(key, "N/A")
        if key == "WOD" and q_val == "N/A":
            continue
        ans_val = a.get(key) or "Not in QOD bank yet"
        lines.append(f"\n• {key}: {q_val}\n  ↳ ANS: {ans_val}")

    lines.append("\n" + "=" * 54)
    lines.append(f"Attached: {filename}  |  Open Direct CNATRA Link: {pdf_url}")
    if SIGNUP_FORM_URL:
        lines.append(f"Manage Subscription (Sign Up / Update / Unsubscribe): {SIGNUP_FORM_URL}")
    lines.append(f"Bot Contact: {GMAIL_USER}")
    lines.append(f"Created by ENS Hagemaster  |  GitHub: {GITHUB_REPO_URL}")
    return "\n".join(lines)


def build_html_body(target_dt: datetime, parsed: dict, is_update: bool, filename: str) -> str:
    date_str = target_dt.strftime("%A, %B %d, %Y")
    pdf_url = (
        f"https://www.cnatra.navy.mil/scheds/TW6/SQ-VT-10/"
        f"!{target_dt.strftime('%Y-%m-%d')}!VT-10!Frontpage.pdf"
    )
    is_weekend = target_dt.weekday() >= 5
    status_tag = determine_schedule_status(parsed, is_weekend)
    has_events = status_tag not in UNSCHEDULED_STATUSES

    # Dynamic Header Gradient & Badge Colors based on schedule status
    if status_tag == "WATCH":
        header_bg = "#78350f"
        header_grad = "linear-gradient(135deg, #451a03 0%, #92400e 55%, #b45309 100%)"
        sub_color = "#fde68a"
        badge_bg, badge_fg, badge_text = "#fef3c7", "#78350f", "WATCH"
    elif has_events:
        header_bg = "#004d2c"
        header_grad = "linear-gradient(135deg, #032b19 0%, #005a32 55%, #0d9488 100%)"
        sub_color = "#a7f3d0"
        badge_bg, badge_fg, badge_text = "#ffffff", "#005a32", status_tag
    elif is_weekend:
        header_bg = "#1e293b"
        header_grad = "linear-gradient(135deg, #063b22 0%, #0f172a 45%, #334155 100%)"
        sub_color = "#cbd5e1"
        badge_bg, badge_fg, badge_text = "#e2e8f0", "#0f172a", "WEEKEND OFF"
    elif status_tag == "UNSCHEDULED":
        header_bg = "#1e293b"
        header_grad = "linear-gradient(135deg, #063b22 0%, #1e293b 50%, #475569 100%)"
        sub_color = "#cbd5e1"
        badge_bg, badge_fg, badge_text = "#e2e8f0", "#1e293b", "UNSCHEDULED"
    else:
        header_bg = "#78350f"
        header_grad = "linear-gradient(135deg, #043921 0%, #78350f 50%, #d97706 100%)"
        sub_color = "#fde68a"
        badge_bg, badge_fg, badge_text = "#fef3c7", "#92400e", "PHONE MUSTER"

    update_banner = ""
    if is_update:
        update_banner = """
        <div style="background-color:#fef2f2; border-left:4px solid #dc2626; padding:12px 16px; margin-bottom:16px; border-radius:6px; color:#991b1b; font-size:14px; font-weight:600;">
          SCHEDULE UPDATE DETECTED — A revised PDF was posted to CNATRA and your schedule changed.
        </div>
        """

    cards_html = []

    if not has_events:
        if is_weekend:
            cards_html.append(f"""
            <div style="background:#f8fafc; border:1px solid #e2e8f0; border-radius:8px; padding:20px; text-align:center; color:#334155;">
              <div style="font-size:16px; font-weight:700; margin-bottom:4px;">Unscheduled — Weekend</div>
              <div style="font-size:14px; color:#64748b;">No events found for <b>{html.escape(parsed['student_name'])}</b>. Enjoy your weekend!</div>
            </div>
            """)
        elif status_tag == "UNSCHEDULED":
            cards_html.append(f"""
            <div style="background:#f8fafc; border:1px solid #e2e8f0; border-left:5px solid #475569; border-radius:8px; padding:18px; color:#334155;">
              <div style="font-size:16px; font-weight:700; margin-bottom:4px;">Unscheduled</div>
              <div style="font-size:14px; color:#64748b;">No events found for <b>{html.escape(parsed['student_name'])}</b>. See the schedule notes in the attached PDF.</div>
            </div>
            """)
        else:
            cards_html.append("""
            <div style="background:#fffbeb; border:1px solid #fde68a; border-left:5px solid #d97706; border-radius:8px; padding:18px; color:#92400e;">
              <div style="font-size:16px; font-weight:700; margin-bottom:6px;">Unscheduled — Phone Muster Required</div>
              <div style="font-size:14px; line-height:1.5;">
                Muster window: <b>0700–0800</b><br>
                ASDO Phone: <a href="tel:8504524669" style="color:#b45309; font-weight:700; text-decoration:underline;">850-452-4669</a>
              </div>
            </div>
            """)

    for f in parsed["flights_and_sims"]:
        if "event" not in f:
            cards_html.append(f"<div style='padding:12px; background:#f1f5f9; border-radius:6px; margin-bottom:12px;'>{html.escape(f['raw'])}</div>")
            continue

        is_sim = f.get("is_sim", False)
        card_icon = "🖥️" if is_sim else "✈️"
        type_label = "SIMULATOR" if is_sim else "FLIGHT"
        card_head_bg = "linear-gradient(135deg, #1e1b4b 0%, #312e81 100%)" if is_sim else "linear-gradient(135deg, #042f1d 0%, #005a32 100%)"
        card_head_fallback = "#1e1b4b" if is_sim else "#005a32"
        pill_bg = "#4f46e5" if is_sim else "#15803d"
        start_label = "Sim Start" if is_sim else "Takeoff"
        end_label = "Sim End" if is_sim else "Land"

        remarks_style = (
            "background:#fef9c3; color:#854d0e; padding:3px 8px; border-radius:4px; font-weight:700; display:inline-block;"
            if f["remarks"] != "None"
            else "color:#64748b;"
        )

        cards_html.append(f"""
        <div style="border:1px solid #cbd5e1; border-radius:10px; overflow:hidden; margin-bottom:16px; background:#ffffff; box-shadow:0 1px 3px rgba(0,0,0,0.04);">
          <div style="background-color:{card_head_fallback}; background-image:{card_head_bg}; color:#ffffff; padding:12px 16px;">
            <table width="100%" cellpadding="0" cellspacing="0" border="0">
              <tr>
                <td style="color:#ffffff; font-size:17px; font-weight:800; letter-spacing:0.3px;">
                  {card_icon} {html.escape(f['event'])}
                  <span style="font-size:10px; font-weight:700; opacity:0.8; margin-left:6px; text-transform:uppercase; letter-spacing:0.6px;">{type_label}</span>
                </td>
                <td align="right">
                  <span style="background:{pill_bg}; color:#ffffff; padding:4px 10px; border-radius:999px; font-size:12px; font-weight:700;">
                    {html.escape(f['device'])}
                  </span>
                </td>
              </tr>
            </table>
          </div>

          <table width="100%" cellpadding="0" cellspacing="0" border="0" style="background:#f1f5f9; border-bottom:1px solid #e2e8f0; text-align:center;">
            <tr>
              <td width="33%" style="padding:10px 4px; border-right:1px solid #e2e8f0;">
                <div style="font-size:10px; font-weight:700; color:#64748b; text-transform:uppercase; letter-spacing:0.5px;">Brief</div>
                <div style="font-size:17px; font-weight:800; color:#0f172a; margin-top:2px;">{html.escape(f['brief'])}</div>
              </td>
              <td width="34%" style="padding:10px 4px; border-right:1px solid #e2e8f0;">
                <div style="font-size:10px; font-weight:700; color:#64748b; text-transform:uppercase; letter-spacing:0.5px;">{start_label}</div>
                <div style="font-size:17px; font-weight:800; color:#0f172a; margin-top:2px;">{html.escape(f['to'])}</div>
              </td>
              <td width="33%" style="padding:10px 4px;">
                <div style="font-size:10px; font-weight:700; color:#64748b; text-transform:uppercase; letter-spacing:0.5px;">{end_label}</div>
                <div style="font-size:17px; font-weight:800; color:#0f172a; margin-top:2px;">{html.escape(f['land'])}</div>
              </td>
            </tr>
          </table>

          <table width="100%" cellpadding="8" cellspacing="0" border="0" style="padding:8px 12px; font-size:14px;">
            <tr>
              <td width="32%" style="color:#64748b; font-weight:600; border-bottom:1px solid #f1f5f9;">Instructor</td>
              <td style="color:#0f172a; font-weight:700; border-bottom:1px solid #f1f5f9;">{html.escape(f['instructor'])}</td>
            </tr>
            <tr>
              <td style="color:#64748b; font-weight:600; border-bottom:1px solid #f1f5f9;">Student</td>
              <td style="color:#334155; border-bottom:1px solid #f1f5f9;">{html.escape(f['student'])}</td>
            </tr>
            <tr>
              <td style="color:#64748b; font-weight:600; border-bottom:1px solid #f1f5f9;">Duration</td>
              <td style="color:#334155; border-bottom:1px solid #f1f5f9;">{html.escape(f['hours'])} hrs</td>
            </tr>
            <tr>
              <td style="color:#64748b; font-weight:600;">Remarks</td>
              <td><span style="{remarks_style}">{html.escape(f['remarks'])}</span></td>
            </tr>
          </table>
        </div>
        """)

    for w in parsed["watches"]:
        cards_html.append(f"""
        <div style="border:1px solid #fcd34d; border-radius:10px; overflow:hidden; margin-bottom:16px; background:#ffffff; box-shadow:0 1px 3px rgba(0,0,0,0.04);">
          <div style="background-color:#78350f; background-image:linear-gradient(135deg, #451a03 0%, #92400e 60%, #b45309 100%); color:#ffffff; padding:12px 16px;">
            <table width="100%" cellpadding="0" cellspacing="0" border="0">
              <tr>
                <td style="color:#ffffff; font-size:17px; font-weight:800; letter-spacing:0.3px;">
                  🛡️ {html.escape(w['watch_type'])}
                  <span style="font-size:10px; font-weight:700; opacity:0.85; margin-left:6px; text-transform:uppercase; letter-spacing:0.6px;">DUTY / WATCH</span>
                </td>
                <td align="right">
                  <span style="background:#d97706; color:#ffffff; padding:4px 10px; border-radius:999px; font-size:12px; font-weight:700;">
                    {html.escape(w['location'])}
                  </span>
                </td>
              </tr>
            </table>
          </div>

          <table width="100%" cellpadding="0" cellspacing="0" border="0" style="background:#fffbeb; border-bottom:1px solid #fde68a; text-align:center;">
            <tr>
              <td width="50%" style="padding:10px 4px; border-right:1px solid #fde68a;">
                <div style="font-size:10px; font-weight:700; color:#92400e; text-transform:uppercase; letter-spacing:0.5px;">Report / Start</div>
                <div style="font-size:17px; font-weight:800; color:#451a03; margin-top:2px;">{html.escape(w['start'])}</div>
              </td>
              <td width="50%" style="padding:10px 4px;">
                <div style="font-size:10px; font-weight:700; color:#92400e; text-transform:uppercase; letter-spacing:0.5px;">Relief / End</div>
                <div style="font-size:17px; font-weight:800; color:#451a03; margin-top:2px;">{html.escape(w['end'])}</div>
              </td>
            </tr>
          </table>

          <table width="100%" cellpadding="8" cellspacing="0" border="0" style="padding:8px 12px; font-size:14px;">
            <tr>
              <td width="32%" style="color:#64748b; font-weight:600; border-bottom:1px solid #f1f5f9;">Watch / Duty</td>
              <td style="color:#0f172a; font-weight:800; border-bottom:1px solid #f1f5f9;">{html.escape(w['watch_type'])} ({html.escape(w['time'])})</td>
            </tr>
            <tr>
              <td style="color:#64748b; font-weight:600; border-bottom:1px solid #f1f5f9;">Assigned</td>
              <td style="color:#0f172a; font-weight:700; border-bottom:1px solid #f1f5f9;">{html.escape(w['student'])}</td>
            </tr>
            <tr>
              <td style="color:#64748b; font-weight:600; border-bottom:1px solid #f1f5f9;">Co-Watch / Relief</td>
              <td style="color:#334155; border-bottom:1px solid #f1f5f9;">{html.escape(w['other_personnel'])}</td>
            </tr>
            <tr>
              <td style="color:#64748b; font-weight:600;">Schedule Line</td>
              <td style="color:#475569; font-size:12.5px; font-family:monospace;">{html.escape(w['raw'])}</td>
            </tr>
          </table>
        </div>
        """)

    for g in parsed["ground_events"]:
        if "event" not in g:
            cards_html.append(f"<div style='padding:12px; background:#f1f5f9; border-radius:6px; margin-bottom:12px;'>{html.escape(g['raw'])}</div>")
            continue

        cards_html.append(f"""
        <div style="border:1px solid #cbd5e1; border-radius:10px; overflow:hidden; margin-bottom:16px; background:#ffffff;">
          <div style="background-color:#0f766e; background-image:linear-gradient(135deg, #134e4a 0%, #0f766e 100%); color:#ffffff; padding:12px 16px;">
            <table width="100%" cellpadding="0" cellspacing="0" border="0">
              <tr>
                <td style="color:#ffffff; font-size:17px; font-weight:800;">
                  🎓 {html.escape(g['event'])}
                  <span style="font-size:10px; font-weight:700; opacity:0.8; margin-left:6px; text-transform:uppercase; letter-spacing:0.6px;">GROUND</span>
                </td>
                <td align="right">
                  <span style="background:#0d9488; color:#ffffff; padding:4px 10px; border-radius:999px; font-size:12px; font-weight:700;">
                    {html.escape(g['location'])}
                  </span>
                </td>
              </tr>
            </table>
          </div>
          <table width="100%" cellpadding="8" cellspacing="0" border="0" style="padding:8px 12px; font-size:14px;">
            <tr>
              <td width="32%" style="color:#64748b; font-weight:600; border-bottom:1px solid #f1f5f9;">Time</td>
              <td style="color:#0f172a; font-weight:800; border-bottom:1px solid #f1f5f9;">{html.escape(g['time'])}</td>
            </tr>
            <tr>
              <td style="color:#64748b; font-weight:600; border-bottom:1px solid #f1f5f9;">Location</td>
              <td style="color:#0f172a; font-weight:700; border-bottom:1px solid #f1f5f9;">{html.escape(g['location'])}</td>
            </tr>
            <tr>
              <td style="color:#64748b; font-weight:600; border-bottom:1px solid #f1f5f9;">Instructor</td>
              <td style="color:#0f172a; font-weight:700; border-bottom:1px solid #f1f5f9;">{html.escape(g['instructor'])}</td>
            </tr>
            <tr>
              <td style="color:#64748b; font-weight:600;">Remarks</td>
              <td style="color:#334155;">{html.escape(g['remarks'])}</td>
            </tr>
          </table>
        </div>
        """)

    for d in parsed["duties_and_notes"]:
        cards_html.append(f"""
        <div style="background:#fff7ed; border:1px solid #fed7aa; border-left:4px solid #ea580c; border-radius:8px; padding:12px 16px; margin-bottom:12px; font-size:14px; color:#9a3412;">
          <b>Schedule Note:</b> {html.escape(d)}
        </div>
        """)

    # Questions of the Day + Answers Table
    q = parsed["questions"]
    a = parsed.get("answers", {})
    q_rows = ""
    badge_specs = [
        ("EOD", "#dc2626"),
        ("IOD", "#2563eb"),
        ("QOD", "#7c3aed"),
        ("SOP", "#0d9488"),
        ("WOD", "#475569"),
    ]

    for key, badge_color in badge_specs:
        raw_q = q.get(key, "N/A")
        if key == "WOD" and raw_q == "N/A":
            continue

        val = html.escape(raw_q)
        raw_ans = a.get(key)

        if raw_ans:
            ans_formatted = html.escape(raw_ans).replace("\n", "<br>")
            ans_html = f"""
            <div style="margin-top:6px; padding:8px 10px; background:#ecfdf5; border-left:3px solid #10b981; border-radius:4px; color:#065f46; font-size:12.5px; line-height:1.45;">
              <b>Answer:</b> {ans_formatted}
            </div>
            """
        else:
            ans_html = """
            <div style="margin-top:4px; font-size:11.5px; color:#94a3b8; font-style:italic;">
              Answer not found in qod_bank.json
            </div>
            """

        q_rows += f"""
        <tr>
          <td width="55" valign="top" style="padding:12px 8px 12px 12px; border-bottom:1px solid #e2e8f0;">
            <span style="background:{badge_color}; color:#ffffff; font-size:11px; font-weight:800; padding:3px 7px; border-radius:4px; display:inline-block;">{key}</span>
          </td>
          <td valign="top" style="padding:12px 12px 12px 4px; border-bottom:1px solid #e2e8f0; color:#0f172a; font-size:13px; line-height:1.45;">
            <div style="font-weight:700;">{val}</div>
            {ans_html}
          </td>
        </tr>
        """

    checkerboard_html = build_checkered_strip_html()

    form_links_html = ""
    if SIGNUP_FORM_URL:
        safe_form_url = html.escape(SIGNUP_FORM_URL)
        form_links_html = f"""
        <div style="margin-top:10px; padding-top:10px; border-top:1px dashed #e2e8f0;">
          <a href="{safe_form_url}" style="color:#005a32; text-decoration:underline; font-weight:700;">
            Manage Subscription (Sign Up / Update / Unsubscribe)
          </a>
        </div>
        """

    return f"""
    <!DOCTYPE html>
    <html>
      <body style="margin:0; padding:12px; background-color:#f1f5f9; font-family:-apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Helvetica, Arial, sans-serif;">
        <div style="max-width:600px; margin:0 auto; background:#ffffff; border-radius:12px; overflow:hidden; border:1px solid #cbd5e1; box-shadow:0 4px 12px rgba(15,23,42,0.06);">

          <!-- VT-10 Green & White Checkered Top Border -->
          {checkerboard_html}

          <!-- Dynamic Gradient Header Banner -->
          <div style="background-color:{header_bg}; background-image:{header_grad}; padding:20px; color:#ffffff; border-top:2px solid #022c22;">
            <table width="100%" cellpadding="0" cellspacing="0" border="0">
              <tr>
                <td>
                  <div style="font-size:11px; text-transform:uppercase; letter-spacing:1.2px; color:{sub_color}; font-weight:800;">
                    VT-10 Wildcats • {html.escape(parsed['student_name'])}
                  </div>
                  <div style="font-size:20px; font-weight:800; margin-top:4px; color:#ffffff;">
                    {html.escape(date_str)}
                  </div>
                </td>
                <td align="right" valign="top">
                  <span style="background:{badge_bg}; color:{badge_fg}; font-size:11px; font-weight:800; padding:6px 11px; border-radius:6px; display:inline-block; white-space:nowrap; box-shadow:0 1px 2px rgba(0,0,0,0.15);">
                    {badge_text}
                  </span>
                </td>
              </tr>
            </table>
          </div>

          <!-- Main Content -->
          <div style="padding:20px;">
            {update_banner}
            {''.join(cards_html)}

            <!-- Questions of the Day -->
            <div style="margin-top:24px;">
              <div style="font-size:12px; font-weight:800; text-transform:uppercase; letter-spacing:0.8px; color:#475569; margin-bottom:8px;">
                Questions of the Day &amp; Study Answers
              </div>
              <table width="100%" cellpadding="0" cellspacing="0" border="0" style="background:#f8fafc; border:1px solid #e2e8f0; border-radius:8px; overflow:hidden;">
                {q_rows}
              </table>
            </div>

            <!-- Footer -->
            <div style="margin-top:22px; padding-top:14px; border-top:1px solid #e2e8f0; font-size:12px; color:#64748b; text-align:center; line-height:1.6;">
              <div>
                Attached: <b>{html.escape(filename)}</b> &nbsp;|&nbsp;
                <a href="{pdf_url}" style="color:#005a32; text-decoration:none; font-weight:700;">Open Direct CNATRA Link ↗</a>
              </div>
              {form_links_html}
              <div style="margin-top:8px; font-size:11.5px; color:#94a3b8;">
                Bot Contact: <a href="mailto:{html.escape(GMAIL_USER)}" style="color:#64748b; text-decoration:none;">{html.escape(GMAIL_USER)}</a>
                &nbsp;&bull;&nbsp;
                Created by <b>ENS Hagemaster</b> (<a href="{GITHUB_REPO_URL}" style="color:#005a32; text-decoration:none; font-weight:600;">GitHub Repo ↗</a>)
              </div>
            </div>
          </div>

        </div>
      </body>
    </html>
    """

def build_diagnostic_recap_email(
    now: datetime,
    target_dt: datetime,
    pdf_hash: str,
    pdf_size_bytes: int,
    page_count: int,
    is_update: bool,
    extracted_pdf: dict,
    roster_diag: dict,
    delivery_results: list[dict],
) -> tuple[str, str, str]:
    date_code = target_dt.strftime("%Y-%m-%d")
    date_pretty = target_dt.strftime("%a %m/%d/%Y")

    sent_count = sum(1 for r in delivery_results if r["sent"])
    failed_count = sum(1 for r in delivery_results if r["error"])
    skipped_count = sum(1 for r in delivery_results if r.get("skipped_unchanged"))
    unsent_count = len(delivery_results) - sent_count - failed_count - skipped_count
    scheduled_count = sum(
        1 for r in delivery_results if r["status_tag"] in ("SCHEDULED", "WATCH", "SCHEDULED + WATCH")
    )

    q = extracted_pdf["questions"]
    a = extracted_pdf["answers"]
    active_q_keys = [k for k in ("EOD", "IOD", "QOD", "SOP", "WOD") if q.get(k, "N/A") != "N/A"]
    matched_q_count = sum(1 for k in active_q_keys if a.get(k))
    missing_q_keys = [k for k in active_q_keys if not a.get(k)]
    muster_lines = extracted_pdf.get("muster_lines", [])
    muster_summary = (
        f"Required — note found: {muster_lines[0]}" if muster_lines
        else "Not mentioned in schedule notes (unscheduled weekday students shown as UNSCHEDULED)"
    )

    subject = (
        f"[DIAGNOSTIC] VT-10 SkedBot Recap ({target_dt.strftime('%a %m/%d')}): "
        f"{sent_count}/{len(delivery_results)} Sent"
        f"{f' ({skipped_count} Unchanged)' if skipped_count else ''}"
        f" | {scheduled_count} Active Events/Watch"
    )

    plain_lines = [
        f"VT-10 SkedBot System Diagnostic & Recap — {date_pretty}",
        "=" * 60,
        f"Run Timestamp:    {now.strftime('%Y-%m-%d %H:%M:%S %Z')}",
        f"Schedule Date:    {date_code} ({'REVISED PDF UPDATE' if is_update else 'Initial Release'})",
        f"PDF SHA-256:      {pdf_hash[:16]}... ({pdf_size_bytes / 1024:.1f} KB, {page_count} pages)",
        f"Roster CSV Sync:  {'OK' if roster_diag['csv_fetch_ok'] else 'FALLBACK/WARNING'} "
        f"({roster_diag['active_count']} active, {roster_diag['unsubscribed_count']} unsubscribed)",
        f"Delivery Totals:  {sent_count} Sent, {skipped_count} Unchanged (skipped), "
        f"{unsent_count} Unsent, {failed_count} Failed",
        f"QOD Bank Matches: {matched_q_count}/{len(active_q_keys)} matched "
        f"{'(Missing: ' + ', '.join(missing_q_keys) + ')' if missing_q_keys else '(100%)'}",
        f"Phone Muster:     {muster_summary}",
        "\nRECIPIENT BREAKDOWN:",
        "-" * 60,
    ]
    for r in delivery_results:
        display_name = (
            f"{r['last_name']}, {r['first_name']}"
            if r.get("first_name")
            else r["last_name"]
        )
        if r["sent"]:
            smtp_status = "SENT OK"
        elif r["error"]:
            smtp_status = f"ERROR: {r['error']}"
        elif r.get("skipped_unchanged"):
            smtp_status = "SKIPPED (UNCHANGED FROM PREVIOUS PDF)"
        else:
            smtp_status = "UNSENT (DIAGNOSTIC ONLY)"
            if r.get("unchanged"):
                smtp_status += " — unchanged from previous PDF"

        plain_lines.append(
            f"• {display_name} ({r['email']}): {r['status_tag']} | "
            f"{r['summary']} | {smtp_status}"
        )

    rows_html = ""
    for r in delivery_results:
        if "WATCH" in r["status_tag"]:
            status_badge_color = "#b45309"
        elif r["status_tag"] == "SCHEDULED":
            status_badge_color = "#16a34a"
        else:
            status_badge_color = "#64748b"

        if r["sent"]:
            deliv_badge = '<span style="color:#15803d; font-weight:700;">✓ Sent</span>'
        elif r["error"]:
            deliv_badge = f'<span style="color:#dc2626; font-weight:700;">✗ {html.escape(str(r["error"]))}</span>'
        elif r.get("skipped_unchanged"):
            deliv_badge = '<span style="color:#0369a1; font-weight:700;">= Unchanged (skipped)</span>'
        elif r.get("unchanged"):
            deliv_badge = '<span style="color:#64748b; font-weight:700;">— Unsent (unchanged)</span>'
        else:
            deliv_badge = '<span style="color:#64748b; font-weight:700;">— Unsent</span>'

        display_name = (
            f"{r['last_name']}, {r['first_name']}"
            if r.get("first_name")
            else r["last_name"]
        )
        rows_html += f"""
        <tr>
          <td style="padding:8px 10px; border-bottom:1px solid #e2e8f0; font-weight:700; color:#0f172a;">
            {html.escape(display_name)}
          </td>
          <td style="padding:8px 10px; border-bottom:1px solid #e2e8f0; color:#475569; font-size:12px;">
            {html.escape(r['email'])}
          </td>
          <td style="padding:8px 10px; border-bottom:1px solid #e2e8f0;">
            <span style="background:{status_badge_color}; color:#ffffff; font-size:10px; font-weight:800; padding:2px 6px; border-radius:4px;">
              {html.escape(r['status_tag'])}
            </span>
          </td>
          <td style="padding:8px 10px; border-bottom:1px solid #e2e8f0; color:#334155; font-size:12.5px;">
            {html.escape(r['summary'])}
          </td>
          <td style="padding:8px 10px; border-bottom:1px solid #e2e8f0; font-size:12.5px;">
            {deliv_badge}
          </td>
        </tr>
        """

    q_diag_rows = ""
    for k in active_q_keys:
        matched = bool(a.get(k))
        status_pill = (
            '<span style="color:#15803d; font-weight:700;">✓ Matched</span>'
            if matched
            else '<span style="color:#d97706; font-weight:700;">⚠️ Missing in qod_bank.json</span>'
        )
        q_diag_rows += f"""
        <tr>
          <td style="padding:6px 10px; border-bottom:1px solid #e2e8f0; font-weight:700; width:50px;">{k}</td>
          <td style="padding:6px 10px; border-bottom:1px solid #e2e8f0; font-size:12px; color:#334155;">{html.escape(q.get(k, ''))}</td>
          <td style="padding:6px 10px; border-bottom:1px solid #e2e8f0; font-size:12px; width:150px;">{status_pill}</td>
        </tr>
        """

    html_body = f"""
    <!DOCTYPE html>
    <html>
      <body style="margin:0; padding:14px; background:#f1f5f9; font-family:-apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;">
        <div style="max-width:680px; margin:0 auto; background:#ffffff; border:1px solid #cbd5e1; border-radius:10px; overflow:hidden;">
          <div style="background:#0f172a; color:#ffffff; padding:16px 20px;">
            <div style="font-size:11px; text-transform:uppercase; letter-spacing:1px; color:#38bdf8; font-weight:700;">
              VT-10 SkedBot • System Diagnostic &amp; Daily Recap
            </div>
            <div style="font-size:18px; font-weight:800; margin-top:4px;">
              Schedule Target: {html.escape(date_pretty)} ({'Revised Update' if is_update else 'Initial Release'})
            </div>
          </div>

          <div style="padding:18px 20px;">
            <table width="100%" cellpadding="6" cellspacing="0" border="0" style="background:#f8fafc; border:1px solid #e2e8f0; border-radius:8px; font-size:13px; margin-bottom:18px;">
              <tr>
                <td width="30%" style="color:#64748b; font-weight:600;">Run Timestamp</td>
                <td style="color:#0f172a; font-weight:700;">{html.escape(now.strftime('%Y-%m-%d %H:%M:%S %Z'))}</td>
              </tr>
              <tr>
                <td style="color:#64748b; font-weight:600;">PDF Integrity</td>
                <td style="color:#0f172a; font-family:monospace; font-size:12px;">
                  SHA256: {pdf_hash[:20]}... ({pdf_size_bytes / 1024:.1f} KB • {page_count} pages)
                </td>
              </tr>
              <tr>
                <td style="color:#64748b; font-weight:600;">Google Sheet Roster</td>
                <td style="color:#0f172a;">
                  <b>{'✓ Synced' if roster_diag['csv_fetch_ok'] else '⚠️ Fallback/Error'}</b> —
                  {roster_diag['active_count']} active subscribers ({roster_diag['raw_rows_processed']} form rows, {roster_diag['unsubscribed_count']} unsubscribed)
                  {f"<br><span style='color:#dc2626;'>Error: {html.escape(str(roster_diag['error']))}</span>" if roster_diag['error'] else ""}
                </td>
              </tr>
              <tr>
                <td style="color:#64748b; font-weight:600;">Phone Muster</td>
                <td style="color:#0f172a;">{html.escape(muster_summary)}</td>
              </tr>
              <tr>
                <td style="color:#64748b; font-weight:600;">Delivery Totals</td>
                <td style="color:#0f172a;">
                  <b>{sent_count} Sent</b>, {skipped_count} Unchanged (skipped), {unsent_count} Unsent, {failed_count} Failed &nbsp;|&nbsp;
                  <b>{scheduled_count} Active Events/Watch</b>, {len(delivery_results) - scheduled_count} Unscheduled
                </td>
              </tr>
            </table>

            <div style="font-size:12px; font-weight:800; text-transform:uppercase; color:#475569; margin-bottom:6px;">
              Recipient Distribution Log ({len(delivery_results)})
            </div>
            <table width="100%" cellpadding="0" cellspacing="0" border="0" style="border:1px solid #e2e8f0; border-radius:8px; overflow:hidden; margin-bottom:18px;">
              <tr style="background:#f1f5f9; font-size:11px; text-transform:uppercase; color:#475569; text-align:left;">
                <th style="padding:8px 10px;">Student</th>
                <th style="padding:8px 10px;">Email</th>
                <th style="padding:8px 10px;">Status</th>
                <th style="padding:8px 10px;">Parsed Events</th>
                <th style="padding:8px 10px;">SMTP</th>
              </tr>
              {rows_html}
            </table>

            <div style="font-size:12px; font-weight:800; text-transform:uppercase; color:#475569; margin-bottom:6px;">
              QOD / WOD Bank Coverage ({matched_q_count}/{len(active_q_keys)} Matched)
            </div>
            <table width="100%" cellpadding="0" cellspacing="0" border="0" style="border:1px solid #e2e8f0; border-radius:8px; overflow:hidden;">
              {q_diag_rows}
            </table>
          </div>
        </div>
      </body>
    </html>
    """
    return subject, "\n".join(plain_lines), html_body


def build_email_message(
    recipient_email: str,
    subject: str,
    plain_body: str,
    html_body: str,
    pdf_bytes: bytes | None = None,
    filename: str | None = None,
) -> EmailMessage:
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = GMAIL_USER
    msg["To"] = recipient_email

    msg.set_content(plain_body)
    msg.add_alternative(html_body, subtype="html")
    if pdf_bytes and filename:
        msg.add_attachment(
            pdf_bytes,
            maintype="application",
            subtype="pdf",
            filename=filename,
        )
    return msg


def summarize_student_events(parsed: dict) -> str:
    parts = []
    for f in parsed["flights_and_sims"]:
        label = "Sim" if f.get("is_sim") else "Flt"
        parts.append(f"{label}:{f.get('event', 'EVT')}")
    for w in parsed["watches"]:
        parts.append(f"Watch:{w.get('watch_type', 'DUTY')}")
    for g in parsed["ground_events"]:
        parts.append(f"Gnd:{g.get('event', 'GND')}")
    for _ in parsed["duties_and_notes"]:
        parts.append("Note")
    if parsed["leave_tad"]:
        parts.append("LEAVE/TAD")
    return ", ".join(parts) if parts else "Unscheduled"


def main():
    now = datetime.now(TZ)
    state = load_state()
    qod_bank = load_qod_bank()
    state_modified = False

    is_manual_test = bool(os.getenv("TEST_DATE", "").strip())
    force_diagnostic = os.getenv("FORCE_DIAGNOSTIC", "false").strip().lower() in ("true", "1", "yes")

    # Fetch the live Google Sheet CSV whenever in normal mode OR force_diagnostic mode
    roster, roster_diag = load_roster(is_manual_test and not force_diagnostic)
    target_dates = get_target_dates(now)

    print(f"Current Central Time: {now.strftime('%Y-%m-%d %H:%M %Z')}")
    if force_diagnostic:
        print("Mode: FORCE DIAGNOSTIC (Dry-run roster & PDF check -> SkedBot Inbox ONLY)")
    elif is_manual_test:
        print("Mode: TEST MODE (Single student preview -> SkedBot Inbox ONLY)")
    else:
        print("Mode: LIVE NORMAL MODE")

    print(f"Target dates to check: {[d.strftime('%Y-%m-%d') for d in target_dates]}")
    print(f"Active recipients: {len(roster)} subscribed student(s)")

    diagnostic_sent = False

    for target_dt in target_dates:
        date_str = target_dt.strftime("%Y-%m-%d")
        pdf_bytes = fetch_valid_pdf(date_str)

        if pdf_bytes is None:
            continue

        pdf_hash = hashlib.sha256(pdf_bytes).hexdigest()
        previous_hash, prev_fingerprints = get_date_state(state, date_str)

        if previous_hash == pdf_hash and not is_manual_test and not force_diagnostic:
            print(f"[{date_str}] Already processed and unchanged (hash match). Skipping.")
            continue

        is_update = (previous_hash is not None) and (previous_hash != pdf_hash)
        extracted_pdf = extract_pdf_lines(pdf_bytes, qod_bank)
        filename = f"VT-10_{date_str}_Frontpage.pdf"
        delivery_results = []
        # Carry forward prior fingerprints; only overwritten after a successful send so
        # failed sends / skipped students keep comparing against what they last received.
        new_fingerprints = dict(prev_fingerprints)

        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
            smtp.login(GMAIL_USER, GMAIL_APP_PASSWORD)

            for idx, student in enumerate(roster, start=1):
                last_name = student["last_name"]
                first_name = student.get("first_name", "")
                first_initial = student.get("first_initial", "")

                parsed = parse_student_schedule(extracted_pdf, last_name, first_name)
                is_weekend = target_dt.weekday() >= 5
                status_tag = determine_schedule_status(parsed, is_weekend)
                skey = student_state_key(last_name, first_name)
                fingerprint = student_schedule_fingerprint(parsed)
                # No prior fingerprint (new subscriber, failed send, legacy state) -> treated as changed
                unchanged = prev_fingerprints.get(skey) == fingerprint

                # Default state is UNSENT (sent: False)
                result_entry = {
                    "last_name": last_name,
                    "first_name": first_name,
                    "first_initial": first_initial,
                    "email": student["email"],
                    "status_tag": status_tag,
                    "summary": summarize_student_events(parsed),
                    "sent": False,
                    "error": None,
                    "unchanged": unchanged,
                    "skipped_unchanged": False,
                }

                # In forced diagnostic mode, skip sending so "sent" remains False
                if force_diagnostic:
                    print(f"[{date_str}] Diagnostic check ({idx}/{len(roster)}) — Status: {status_tag}")
                    delivery_results.append(result_entry)
                    continue

                # Revised PDF but this student's info is identical to what they already got
                if unchanged and not is_manual_test:
                    result_entry["skipped_unchanged"] = True
                    print(f"[{date_str}] Skipped ({idx}/{len(roster)}) — schedule unchanged — Status: {status_tag}")
                    delivery_results.append(result_entry)
                    continue

                recipient_email = GMAIL_USER if is_manual_test else student["email"]
                result_entry["email"] = recipient_email
                prefix = "[TEST -> SkedBot Inbox] " if is_manual_test else ("[UPDATED] " if is_update else "")
                subject = (
                    f"{prefix}VT-10 Sked ({target_dt.strftime('%a %m/%d')} - "
                    f"{last_name}): {status_tag}"
                )

                plain_body = build_plain_text_body(target_dt, parsed, is_update, filename)
                html_body = build_html_body(target_dt, parsed, is_update, filename)

                try:
                    msg = build_email_message(
                        recipient_email, subject, plain_body, html_body, pdf_bytes, filename
                    )
                    smtp.send_message(msg)
                    result_entry["sent"] = True  # Only flips to True after actual SMTP send
                    new_fingerprints[skey] = fingerprint
                    print(f"[{date_str}] Sent schedule email ({idx}/{len(roster)}) — Status: {status_tag}")
                except Exception as e:
                    result_entry["error"] = str(e)  # full detail goes only to the private diagnostic email
                    # Log only the exception type: SMTP errors can echo the recipient address
                    print(f"[{date_str}] ERROR sending schedule email ({idx}/{len(roster)}): {type(e).__name__}")

                delivery_results.append(result_entry)

            # Send Diagnostic Recap to SkedBot inbox on normal daily runs OR when force_diagnostic is True
            if not is_manual_test or force_diagnostic:
                diag_subj, diag_plain, diag_html = build_diagnostic_recap_email(
                    now=now,
                    target_dt=target_dt,
                    pdf_hash=pdf_hash,
                    pdf_size_bytes=len(pdf_bytes),
                    page_count=extracted_pdf["page_count"],
                    is_update=is_update,
                    extracted_pdf=extracted_pdf,
                    roster_diag=roster_diag,
                    delivery_results=delivery_results,
                )
                if force_diagnostic:
                    diag_subj = f"[FORCED DIAGNOSTIC] {diag_subj.removeprefix('[DIAGNOSTIC] ')}"
                diag_msg = build_email_message(
                    GMAIL_USER, diag_subj, diag_plain, diag_html, pdf_bytes, filename
                )
                smtp.send_message(diag_msg)
                diagnostic_sent = True
                print(f"[{date_str}] Sent System Diagnostic Recap to SkedBot inbox.")

        if not is_manual_test and not force_diagnostic:
            state[date_str] = {"pdf_hash": pdf_hash, "students": new_fingerprints}
            state_modified = True

    # Fallback if force_diagnostic was triggered without a test_date and tomorrow's PDF isn't posted yet
    if force_diagnostic and not diagnostic_sent and state:
        latest_known_date = sorted(state.keys())[-1]
        print(f"[FORCE DIAGNOSTIC] Target dates not posted yet; falling back to latest known PDF ({latest_known_date}).")
        fallback_dt = datetime.strptime(latest_known_date, "%Y-%m-%d").replace(tzinfo=TZ)
        pdf_bytes = fetch_valid_pdf(latest_known_date)
        if pdf_bytes:
            pdf_hash = hashlib.sha256(pdf_bytes).hexdigest()
            extracted_pdf = extract_pdf_lines(pdf_bytes, qod_bank)
            filename = f"VT-10_{latest_known_date}_Frontpage.pdf"
            delivery_results = []
            for idx, student in enumerate(roster, start=1):
                parsed = parse_student_schedule(extracted_pdf, student["last_name"], student.get("first_name", ""))
                status_tag = determine_schedule_status(parsed, fallback_dt.weekday() >= 5)
                print(f"[{latest_known_date}] Diagnostic check ({idx}/{len(roster)}) — Status: {status_tag}")
                delivery_results.append({
                    "last_name": student["last_name"],
                    "first_name": student.get("first_name", ""),
                    "first_initial": student.get("first_initial", ""),
                    "email": student["email"],
                    "status_tag": status_tag,
                    "summary": summarize_student_events(parsed),
                    "sent": False,
                    "error": None,
                })
            with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
                smtp.login(GMAIL_USER, GMAIL_APP_PASSWORD)
                diag_subj, diag_plain, diag_html = build_diagnostic_recap_email(
                    now=now,
                    target_dt=fallback_dt,
                    pdf_hash=pdf_hash,
                    pdf_size_bytes=len(pdf_bytes),
                    page_count=extracted_pdf["page_count"],
                    is_update=False,
                    extracted_pdf=extracted_pdf,
                    roster_diag=roster_diag,
                    delivery_results=delivery_results,
                )
                diag_subj = f"[FORCED DIAGNOSTIC] {diag_subj.removeprefix('[DIAGNOSTIC] ')}"
                diag_msg = build_email_message(
                    GMAIL_USER, diag_subj, diag_plain, diag_html, pdf_bytes, filename
                )
                smtp.send_message(diag_msg)
                print(f"[{latest_known_date}] Sent Fallback System Diagnostic Recap to SkedBot inbox.")

    if state_modified:
        trimmed_state = dict(sorted(state.items())[-15:])
        save_state(trimmed_state)

if __name__ == "__main__":
    main()
