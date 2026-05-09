"""
E等公務園 自動上課輔助工具 v1.8.8
- 自動管理瀏覽器驅動版本（永遠不會版本不符）
- 支援 E等公務人員（我的e政府）/ 人事服務網eCPA 登入
- 多組帳號記憶與快速切換
- 自動掃描未完成課程 → 循環上課 → 自動關彈窗
- v1.8.0：登入後自動 prefetch 待考課程題庫（roddayeye 痞客幫）
- v1.8.1：修「已填問卷誤點修改問卷」/「[ ] CSS selector 失敗」
- v1.8.7：盲考生強化套件
   * 題目文字 reverse DOM walk（解決抓不到題目）
   * 押題：以上皆是優先 / 一定絕對排除 / TF 對否語意 / 多選預設全選
   * Cycling：失敗後絕不重蹈覆轍（option-label hash 跨 attempt 穩定）
   * 失敗後 _harvest_from_result_page 持續學習（從結果頁挖正解）
   * 失敗 dump 整份 page_source + 截圖（找隱藏正解）
   * 重考改 30 次（pass / 系統限制 / 連續 8 次零學習才停）
     —「學習」= harvester 收成 + cycling 新排除錯選項
   * 本次執行統計（含 options_eliminated）
   * 問卷快速跳出：偵測「修改問卷／查看問卷」立刻 return，不空等
- v1.8.8：Gemini AI 答題 ⭐ 痞客幫無此課時的第二道防線
   * 題庫 miss → 呼叫 Google Gemini API（免費版 gemini-1.5-flash）
   * 傳送「課程名＋題目＋選項」，AI 直接判斷正解
   * 命中後立即寫入 qa_bank，下次同題直接命中不再呼叫 API
   * API key 存於 eclass_config.json（gemini_api_key 欄位）
   * 超額（429）時自動停用本 session，不影響押題 fallback
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, simpledialog
import threading
import time
import json
import os
import re
import sys
import random
import urllib.request
import urllib.parse
from html.parser import HTMLParser
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed

from selenium import webdriver
from selenium.webdriver.edge.options   import Options as EdgeOptions
from selenium.webdriver.chrome.options import Options as ChromeOptions
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.common.exceptions import (
    NoSuchElementException, TimeoutException,
    WebDriverException, StaleElementReferenceException
)

# v1.8.0：roddayeye 痞客幫題庫爬蟲
try:
    from qa_scraper import fetch_index, fuzzy_lookup, fetch_and_parse
    _SCRAPER_AVAILABLE = True
except Exception as _e:
    _SCRAPER_AVAILABLE = False
    _SCRAPER_IMPORT_ERR = str(_e)

# v1.8.8：Gemini AI 答題（用 urllib 直連 REST API，避免 SDK 啟動拖慢）
GEMINI_API_URL = ("https://generativelanguage.googleapis.com/v1beta/"
                  "models/gemini-flash-lite-latest:generateContent")
GEMINI_MIN_INTERVAL = 4.5   # v1.8.13: free tier 15 RPM → 每次呼叫至少間隔 4 秒
# v1.8.20: Gemini Flash-Lite 預估費用（USD per token）— UI 顯示用，免費版實際 $0
GEMINI_PRICE_IN  = 0.10 / 1_000_000   # 輸入 $0.10 / 1M tokens
GEMINI_PRICE_OUT = 0.40 / 1_000_000   # 輸出 $0.40 / 1M tokens
GEMINI_FREE_RPD  = 1500               # 免費版每日請求上限（進度條滿格）

VERSION = "1.8.48"

# v1.8.7: 全專案固定 User-Agent（Selenium CDP override + qa_scraper HTTP request 同源）
#   避免不同機器 UA 差異、也避免 HeadlessChrome 特徵殘留
FIXED_USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/120.0.6099.109 Safari/537.36")
# 打包成 exe 時用 sys.executable 定位，避免存到暫存目錄
if getattr(sys, 'frozen', False):
    _BASE_DIR = os.path.dirname(sys.executable)
else:
    _BASE_DIR = os.path.dirname(os.path.abspath(__file__))
_DATA_DIR   = os.path.join(_BASE_DIR, "data")
os.makedirs(_DATA_DIR, exist_ok=True)
CONFIG_FILE = os.path.join(_DATA_DIR, "eclass_config.json")
QA_BANK_FILE = os.path.join(_DATA_DIR, "qa_bank.json")
QA_MISS_FILE = os.path.join(_DATA_DIR, "qa_missed.json")
QA_INDEX_FILE = os.path.join(_DATA_DIR, "course_index.json")

ELEARN_HOME   = "https://elearn.hrd.gov.tw/mooc/index.php"
ECPA_LOGIN    = "https://ecpa.dgpa.gov.tw/uIAM/clogin.asp?destid=CrossHRD"
DASHBOARD_URL = "https://elearn.hrd.gov.tw/mooc/user/learn_dashboard.php"


# ══════════════════════════════════════════════════════════
# QABank：題庫（JSON 格式，使用者可手動編輯）
# 檔案：data/qa_bank.json
# 結構：{
#   "正規化題目hash key": {
#     "q":     "題目原文",
#     "type":  "TF" | "SC" | "MC",
#     "a":     ["正解選項文字1", ...],
#     "course": "課程名稱（記錄用）"
#   }
# }
# ══════════════════════════════════════════════════════════
class QABank:
    def __init__(self, path):
        self.path = path
        self.data = {}
        self._dirty = False
        # bug #41: prefetch worker 用 ThreadPoolExecutor(max_workers=4) 並行改 self.data，
        # 同時 save()/find() 可能在另一 thread 執行 → 產生 `dictionary changed size during iteration`
        # 或寫出損毀的 JSON。加 RLock 保護所有讀寫。
        self._lock = threading.RLock()
        self._option_index = None   # v1.8.9: lazy built by find_correct_options()
        try:
            if os.path.exists(path):
                with open(path, "r", encoding="utf-8") as f:
                    self.data = json.load(f)
        except Exception:
            self.data = {}

    @staticmethod
    def normalize(text):
        """正規化題目：移除空白、標點、序號、前後空格，便於匹配"""
        if not text:
            return ""
        s = text
        # 去序號（前綴 1. / (1) / 第1題 / 一、 等）
        s = re.sub(r'^[\s　]*[（(\[【]?\s*'
                   r'(\d+|[一二三四五六七八九十]+)\s*'
                   r'[)）\]】．]?[、\.]?[\s　]*', '', s)
        # 去常見答題前綴
        s = re.sub(r'^(題目[:：]|問[:：]|Q\d*[:：]?)\s*', '', s, flags=re.I)
        # 去全部空白與常見標點
        s = re.sub(r'[\s　\u3000]+', '', s)
        s = re.sub(r'[，,。.；;：:！!？?\'"\'""「」『』（）()\[\]【】<>《》/\-]', '', s)
        return s

    def find(self, question_text):
        """查詢；找到回傳 dict {q, type, a, course}，找不到回傳 None"""
        key = self.normalize(question_text)
        if not key:
            return None
        with self._lock:
            # 完全比對
            if key in self.data:
                return self.data[key]
            # bug #43: 原本只要 len(k) >= 12 且互為子字串就回傳，太寬：
            #   題庫「公務人員應遵守保密義務不得洩漏機密資料」會被「公務人員應遵守保密義務」（前綴）誤配。
            # 改為：長度差距比例 < 0.25 + difflib ratio > 0.88 才視為同題。
            try:
                import difflib
                ratio_fn = difflib.SequenceMatcher
            except Exception:
                ratio_fn = None
            best = None
            best_score = 0.0
            for k, v in self.data.items():
                if len(k) < 12:
                    continue
                # v1.8.7 bug #2: 原本 `longer == 0` 是死碼（string != 0），且嵌套 if 等於把候選
                # 限制成必須互為子字串，閹割了 ratio fuzzy。改成：長度差距 >=25% 直接 skip，
                # 其餘全交 difflib 判定。
                longer, shorter = (k, key) if len(k) >= len(key) else (key, k)
                len_ratio = len(shorter) / max(1, len(longer))
                if len_ratio < 0.75:
                    continue
                if ratio_fn is not None:
                    sim = ratio_fn(None, k, key).ratio()
                    if sim < 0.88:
                        continue
                    if sim > best_score:
                        best_score = sim
                        best = v
                else:
                    best = v
            return best

    @staticmethod
    def _course_match(a, b, threshold=0.6):
        """v1.8.9：寬鬆課程名比對（包含關係 or difflib 0.6）"""
        if not a or not b:
            return False
        an = re.sub(r'[\s　/／\-]+', '', a)
        bn = re.sub(r'[\s　/／\-]+', '', b)
        if an in bn or bn in an:
            return True
        try:
            import difflib
            return difflib.SequenceMatcher(None, an, bn).ratio() >= threshold
        except Exception:
            return False

    def find_correct_options(self, course_hint=""):
        """v1.8.9：回傳該課程所有已知正解選項的 normalized text set（選項池直配用）
        v1.8.12：跨課汙染處理 — 若 hint 提供，優先收嚴格命中（包含關係或 ratio>=0.85）
        的課程；只有零命中時才退回寬鬆 0.6。並對短答案另存 short_pool，避免短詞誤配長題。
        """
        import difflib
        with self._lock:
            strict_pool, loose_pool = set(), set()
            for v in self.data.values():
                course = v.get("course", "") or ""
                ans_list = v.get("a") or []
                if not course_hint:
                    for ans in ans_list:
                        norm = self.normalize(ans)
                        if norm:
                            strict_pool.add(norm)
                    continue
                # strict: 包含或 difflib >= 0.85
                a_n = re.sub(r'[\s　/／\-]+', '', course)
                b_n = re.sub(r'[\s　/／\-]+', '', course_hint)
                strict_hit = (a_n and b_n and
                              (a_n in b_n or b_n in a_n or
                               difflib.SequenceMatcher(None, a_n, b_n).ratio() >= 0.75))
                loose_hit = strict_hit or self._course_match(course, course_hint)
                if strict_hit:
                    for ans in ans_list:
                        norm = self.normalize(ans)
                        if norm:
                            strict_pool.add(norm)
                elif loose_hit:
                    for ans in ans_list:
                        norm = self.normalize(ans)
                        if norm:
                            loose_pool.add(norm)
            return strict_pool if strict_pool else loose_pool

    def add(self, question_text, answers, qtype="SC", course="", overwrite=True):
        """新增/更新一題
        v1.8.7 bug #5：加 overwrite 參數（預設 True 保留原行為）。
          harvester 從結果頁挖到正解 → upsert（高信任度）
          prefetch 從痞客幫抓到 → add_if_absent（低信任度，不覆蓋既有）
        v1.8.46:保留既有 wrong 欄位(cycling 持久化),避免被覆寫清空。
        """
        key = self.normalize(question_text)
        if not key:
            return
        with self._lock:
            if (not overwrite) and key in self.data:
                return
            # v1.8.46:救出舊 entry 的 wrong list,避免 add 覆寫時遺失
            existing_wrong = []
            if key in self.data:
                existing_wrong = list(self.data[key].get("wrong") or [])
            entry = {
                "q": question_text[:300],
                "type": qtype,
                "a": list(answers) if isinstance(answers, (list, tuple)) else [answers],
                "course": course or "",
            }
            if existing_wrong:
                entry["wrong"] = existing_wrong
            self.data[key] = entry
            self._option_index = None   # v1.8.9: invalidate cache
            self._dirty = True

    def add_if_absent(self, question_text, answers, qtype="SC", course=""):
        """v1.8.7 bug #5：prefetch 專用 — 既有就不覆蓋"""
        return self.add(question_text, answers, qtype=qtype, course=course, overwrite=False)

    def has_exact(self, question_text):
        """v1.8.7 bug #4：精確比對（不走 fuzzy），供 harvester existing check 用"""
        key = self.normalize(question_text)
        if not key:
            return False
        with self._lock:
            return key in self.data

    def add_wrong(self, question_text, wrong_label):
        """v1.8.45：持久化 cycling 試錯結果。
        把 wrong_label 加到該題的 wrong list（去重 normalize key,跨 session 累積）。
        若該題尚未有 entry,建立一個只有 wrong 的骨架 entry(a 留空表示沒正解)。
        """
        key = self.normalize(question_text)
        wn  = self.normalize(wrong_label)
        if not key or not wn:
            return
        with self._lock:
            entry = self.data.get(key)
            if entry is None:
                entry = {"q": question_text[:300], "type": "SC", "a": [], "course": "", "wrong": []}
                self.data[key] = entry
            wlist = entry.get("wrong") or []
            if wn not in (self.normalize(w) for w in wlist):
                wlist.append(wrong_label[:200])
                entry["wrong"] = wlist
                self._dirty = True

    def get_wrong(self, question_text):
        """v1.8.45：回傳該題已知錯選項的 normalized set;沒有就空 set。"""
        key = self.normalize(question_text)
        if not key:
            return set()
        with self._lock:
            entry = self.data.get(key)
            if not entry:
                return set()
            return {self.normalize(w) for w in (entry.get("wrong") or []) if w}

    def save(self):
        with self._lock:
            if not self._dirty:
                return
            # 於 lock 內 snapshot 資料，避免在寫檔期間其他 thread 繼續改 self.data 造成 JSON 損毀
            snapshot = dict(self.data)
            self._dirty = False
        try:
            os.makedirs(os.path.dirname(self.path), exist_ok=True)
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(snapshot, f, ensure_ascii=False, indent=2)
        except Exception:
            # 寫失敗 → 再次標 dirty 讓下次重試
            with self._lock:
                self._dirty = True

    def count(self):
        with self._lock:
            return len(self.data)


# ══════════════════════════════════════════════════════════
class EClassApp:
    def __init__(self):
        self.driver   = None
        self.running  = False
        self.cycle_count = 0
        self._tried_hrefs = set()   # 本次執行已嘗試過的課程 href，避免無限迴圈
        # 登入後彈窗讀到的待辦數量（真相來源；-1 表示未知）
        self.popup_pending_course = -1
        self.popup_pending_exam   = -1
        self.popup_pending_survey = -1
        self.config   = self._load_config()
        self.qa_bank  = QABank(QA_BANK_FILE)
        self._gemini  = None              # v1.8.8: Gemini AI client
        self._current_course_title = ""   # 答題自動學習用
        # v1.8.23/24：本門課程的權威狀態（從課程清單卡片抓取，主導 _process_current_course_page）
        # v1.8.24：needs 改三態 None/True/False — None=沒抓到 step(不可短路),True/False=明確
        self._current_needs       = {"reading": None, "exam": None, "survey": None}
        self._current_exam_score  = None  # 該課實際測驗分數（None=未知）
        self._current_exam_pass   = None  # 該課及格門檻（每課不同，None=未知）
        self._current_already_min = None  # 該課已上時數（分鐘，None=未知）
        # 累計本次執行所有「題庫沒命中」題目，stop 時 dump 到 qa_missed.json
        self._missed_questions = {}
        # v1.8.7：選項 cycling — 記錄每題試過的選項，避免下一次重蹈覆轍
        # key = options_signature  (依題目選項組合 hash，跨 attempt 穩定)
        # value = set of normalized option labels already tried
        self._exam_session_tried = {}
        # v1.8.7：本次測驗的零學習計數（連續多次 attempt 無題庫成長 → 放棄）
        self._exam_no_learn_streak = 0
        # v1.8.7：執行期統計
        self._stats = {
            "courses_attempted": 0, "courses_passed": 0, "courses_failed": 0,
            "exam_attempts": 0, "exams_passed": 0,
            "questions_total": 0, "db_hits": 0, "option_hits": 0, "fallbacks": 0,
            "ai_hits": 0,       # v1.8.8: Gemini AI 答題命中
            "harvested_questions": 0, "options_eliminated": 0,
            # v1.8.20: AI Token 用量追蹤（session 內累計，重啟歸零）
            "prompt_tokens": 0,
            "completion_tokens": 0,
            "ai_calls_total": 0,
            "started_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        }
        # v1.8.0：prefetch 狀態
        self._prefetch_status = {}        # normalized_title -> 'queued'|'fetching'|'done'|'miss'|'err'
        self._prefetch_events = {}        # normalized_title -> threading.Event()
        self._prefetch_lock   = threading.Lock()
        # v1.8.48:config 寫入鎖(避免 worker + main thread 同時 _save_config 互踩)
        self._cfg_lock = threading.Lock()
        self._prefetch_thread = None
        self._prefetch_index  = None
        self._init_gemini()   # v1.8.8

        self.root = tk.Tk()
        self.root.title(f"E等公務園 自動上課工具 v{VERSION}")
        self.root.geometry("540x720")
        self.root.resizable(False, False)
        self.root.configure(bg="#f0f0f0")

        self._build_gui()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ── 設定讀寫 ──────────────────────────────────────────

    def _load_config(self):
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return {"accounts": [], "last_account": "", "check_interval": 5}

    def _save_config(self):
        # v1.8.8：保留所有未列舉欄位（如 gemini_api_key）避免被覆蓋
        # v1.8.48:加 _cfg_lock 避免 worker + main thread 並發互踩
        # 注意:本 method 應從 main thread 呼叫(會讀 Tkinter StringVar);
        # worker thread 改用 self.root.after_idle(self._save_config) 排到 main
        with self._cfg_lock:
            cfg = dict(self.config)
            cfg["accounts"]     = self.config.get("accounts", [])
            try:
                cfg["last_account"] = self.account_var.get()
                cfg["browser"]      = self.browser_type.get()
            except Exception:
                # 萬一在 worker thread 被誤呼(_init_gemini 階段),不讓 StringVar
                # 存取例外打斷寫入 — 用 config 既有值兜底
                cfg["last_account"] = self.config.get("last_account", "")
                cfg["browser"]      = self.config.get("browser", "edge")
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(cfg, f, ensure_ascii=False, indent=2)

    # ── v1.8.8: Gemini AI (直連 REST API，零 SDK) ────────────

    def _init_gemini(self):
        # v1.8.45:支援多筆 key 主備 fallback;v1.8.47:加 stats_id per-key 累積
        # 優先讀 gemini_api_keys: [{label, key, stats_id}, ...]
        # 沒設則 fallback 舊 gemini_api_key 欄位(視為單把「主」)
        import uuid
        self._gemini_keys = []
        self._gemini_key_idx = 0
        ks = self.config.get("gemini_api_keys")
        if isinstance(ks, list):
            for i, item in enumerate(ks):
                if isinstance(item, dict):
                    k = (item.get("key") or "").strip()
                    if k:
                        # v1.8.47:沒 stats_id 就生成,寫回 config
                        sid = item.get("stats_id") or uuid.uuid4().hex[:12]
                        item["stats_id"] = sid
                        self._gemini_keys.append({
                            "label": item.get("label") or f"key{i+1}",
                            "key": k,
                            "stats_id": sid,
                        })
        # 向後相容:舊 gemini_api_key 視為「主」(若未已包含於 keys 列)
        legacy = (self.config.get("gemini_api_key") or "").strip()
        if legacy and not any(k["key"] == legacy for k in self._gemini_keys):
            self._gemini_keys.insert(0, {
                "label": "主(legacy)",
                "key": legacy,
                "stats_id": uuid.uuid4().hex[:12],
            })
        # 把 stats_id 同步寫回 config(讓下次啟動穩定)
        self.config["gemini_api_keys"] = [
            {"label": k["label"], "key": k["key"], "stats_id": k["stats_id"]}
            for k in self._gemini_keys
        ]
        # v1.8.48:legacy gemini_api_key 已遷移到 gemini_api_keys list
        # → pop 掉避免使用者刪 key 後又被舊欄位重生
        self.config.pop("gemini_api_key", None)
        # 設目前生效 key
        self._gemini = self._gemini_keys[0]["key"] if self._gemini_keys else None
        # 確保 gemini_stats 容器存在(per-key 累積)
        self.config.setdefault("gemini_stats", {})
        # v1.8.13: RPM 節流 + 連續 429 計數
        self._gemini_last_call = 0.0
        self._gemini_429_streak = 0

    def _current_gemini_stats_id(self):
        """v1.8.47:取目前生效 key 的 stats_id;沒有 key 回 None"""
        if not self._gemini_keys or self._gemini_key_idx >= len(self._gemini_keys):
            return None
        return self._gemini_keys[self._gemini_key_idx].get("stats_id")

    def _update_gemini_persistent_stats(self, in_t, out_t):
        """v1.8.47:把單次呼叫的 token 用量寫到 config.gemini_stats[stats_id]
        per-key 累積 + by_date 分日。session 累積仍走 self._stats(既有)。
        """
        sid = self._current_gemini_stats_id()
        if not sid:
            return
        try:
            stats_root = self.config.setdefault("gemini_stats", {})
            entry = stats_root.setdefault(sid, {
                "calls": 0, "in_tokens": 0, "out_tokens": 0,
                "first_seen": "", "last_seen": "", "by_date": {},
            })
            entry["calls"] = int(entry.get("calls", 0)) + 1
            entry["in_tokens"] = int(entry.get("in_tokens", 0)) + int(in_t or 0)
            entry["out_tokens"] = int(entry.get("out_tokens", 0)) + int(out_t or 0)
            from datetime import date
            today = date.today().isoformat()
            if not entry.get("first_seen"):
                entry["first_seen"] = today
            entry["last_seen"] = today
            day_root = entry.setdefault("by_date", {}).setdefault(today, {
                "calls": 0, "in_tokens": 0, "out_tokens": 0,
            })
            day_root["calls"] = int(day_root.get("calls", 0)) + 1
            day_root["in_tokens"] = int(day_root.get("in_tokens", 0)) + int(in_t or 0)
            day_root["out_tokens"] = int(day_root.get("out_tokens", 0)) + int(out_t or 0)
            # v1.8.48:本 method 從 worker thread 呼叫 → 排到 main thread 寫檔
            try:
                self.root.after_idle(self._save_config)
            except Exception:
                # root 未建立(極早期)→ 直接 lock-protected save
                self._save_config()
        except Exception:
            pass

    def _switch_gemini_key(self, reason=""):
        """v1.8.45:切換到下一把備用 key,回傳是否切成;v1.8.47:同步 UI Combobox。"""
        if not self._gemini_keys:
            return False
        if self._gemini_key_idx + 1 >= len(self._gemini_keys):
            self.log(f"⚠ Gemini 所有 key 皆耗盡{('(' + reason + ')') if reason else ''},本 session 停用 AI")
            self._gemini = None
            return False
        old_label = self._gemini_keys[self._gemini_key_idx]["label"]
        self._gemini_key_idx += 1
        nk = self._gemini_keys[self._gemini_key_idx]
        self._gemini = nk["key"]
        self._gemini_429_streak = 0   # 切到新 key 重設計數
        self.log(f"🔄 Gemini「{old_label}」失效{('(' + reason + ')') if reason else ''} → 切到「{nk['label']}」")
        # v1.8.47:UI 同步(主執行緒)
        try:
            new_idx = self._gemini_key_idx
            def _ui_sync():
                try:
                    if hasattr(self, "gemini_key_selector"):
                        self.gemini_key_selector.current(new_idx)
                except Exception:
                    pass
                try:
                    self._update_ai_stats()
                except Exception:
                    pass
            self.root.after_idle(_ui_sync)
        except Exception:
            pass
        return True

    def _gemini_call(self, prompt, timeout=15):
        """POST Gemini REST API。回傳 (text, http_status) 或 (None, status)。
        v1.8.13: 加 RPM 節流 + 503 重試一次"""
        # RPM 節流
        try:
            elapsed = time.time() - self._gemini_last_call
            if elapsed < GEMINI_MIN_INTERVAL:
                time.sleep(GEMINI_MIN_INTERVAL - elapsed)
        except Exception:
            pass

        body = json.dumps({
            "contents": [{"parts": [{"text": prompt}]}]
        }).encode("utf-8")
        url = f"{GEMINI_API_URL}?key={self._gemini}"

        def _do_call():
            req = urllib.request.Request(url, data=body,
                                         headers={"Content-Type": "application/json"})
            try:
                with urllib.request.urlopen(req, timeout=timeout) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
                # v1.8.20: 從 usageMetadata 抓 token 用量並更新 UI
                usage = data.get("usageMetadata") or {}
                in_t  = int(usage.get("promptTokenCount") or 0)
                out_t = int(usage.get("candidatesTokenCount") or 0)
                self._stats["prompt_tokens"]     += in_t
                self._stats["completion_tokens"] += out_t
                self._stats["ai_calls_total"]    += 1
                # v1.8.47:per-key 持久累積(寫 config.gemini_stats[stats_id])
                try:
                    self._update_gemini_persistent_stats(in_t, out_t)
                except Exception:
                    pass
                try:
                    self._update_ai_stats()
                except Exception:
                    pass
                cands = data.get("candidates") or []
                if not cands:
                    return "", 200
                parts = cands[0].get("content", {}).get("parts") or []
                text = "".join(p.get("text", "") for p in parts)
                return text, 200
            except urllib.error.HTTPError as e:
                try:
                    body_e = e.read().decode("utf-8", errors="ignore")[:300]
                except Exception:
                    body_e = ""
                return None, (e.code, body_e)
            except Exception as e:
                return None, (0, str(e))

        text, status = _do_call()
        # 503 transient → 等 6 秒重試一次
        if text is None and isinstance(status, tuple) and status[0] == 503:
            try:
                self.log("⚠ Gemini 503 high demand，6 秒後重試一次")
            except Exception:
                pass
            time.sleep(6)
            text, status = _do_call()
        self._gemini_last_call = time.time()
        return text, status

    def _ask_ai(self, qtext, opts):
        """v1.8.8: 呼叫 Gemini API 答題。回傳命中的 (inp, lab, itype) list。"""
        if not self._gemini or not qtext:
            return []
        course = getattr(self, "_current_course_title", "") or ""
        opt_lines = "\n".join(
            f"{chr(65 + i)}. {lab}"
            for i, (_, lab, _) in enumerate(opts) if lab
        )
        prompt = (
            f"你是台灣公務員訓練考試的答題助手。\n"
            f"課程：{course}\n"
            f"題目：{qtext}\n"
            f"選項：\n{opt_lines}\n\n"
            f"請直接回答「正確選項的完整文字」，若有多個正解請每行一個，不要任何解釋。"
        )
        text, status = self._gemini_call(prompt)
        if text is None:
            code, body = status if isinstance(status, tuple) else (0, "")
            is_quota = (code == 429 or "quota" in str(body).lower()
                        or "resource_exhausted" in str(body).lower())
            is_auth  = (code in (401, 403) or "api key not valid" in str(body).lower()
                        or "permission_denied" in str(body).lower())
            if is_quota:
                # v1.8.13: 連續兩次 429 → v1.8.45 改成切備用 key,而非直接停用
                self._gemini_429_streak += 1
                if self._gemini_429_streak >= 2:
                    self.log(f"⚠ Gemini 連續超額兩次: HTTP {code} → 嘗試切備用 key")
                    if not self._switch_gemini_key(reason=f"quota {code}"):
                        # 切不到備用就停用
                        self._gemini = None
                else:
                    self.log(f"⚠ Gemini 超額一次，等 30 秒後續用: HTTP {code}")
                    time.sleep(30)
            elif is_auth:
                # v1.8.45:key 失效(401/403)直接切備用,不重試
                self.log(f"⚠ Gemini key 無效: HTTP {code} → 嘗試切備用 key")
                self._switch_gemini_key(reason=f"auth {code}")
            else:
                self.log(f"⚠ Gemini 錯誤: HTTP {code} {body[:100] if body else ''}")
            return []
        # 成功回應 → reset 429 streak
        self._gemini_429_streak = 0
        if not text:
            return []
        matched = []
        # v1.8.14: 改用 _texts_match — TF 等價 + substring(>=2) + difflib 0.7
        for inp, lab, itype in opts:
            if not lab:
                # v1.8.14: lab 抓不到時用 value 屬性（TF 題 radio 常 value=「對/錯」）
                try:
                    lab = (inp.get_attribute("value") or "").strip()
                except Exception:
                    lab = ""
                if not lab:
                    continue
            for line in text.splitlines():
                line_clean = re.sub(r'^[（(]?[A-Da-d][)）.、]\s*', '',
                                    line.strip())
                if not line_clean:
                    continue
                if self._texts_match(lab, line_clean):
                    matched.append((inp, lab, itype))
                    break
        # v1.8.11: AI 回了但配不到任何選項 → 印 AI 回應頭兩行協助診斷
        if not matched and text:
            _preview = " / ".join(text.splitlines()[:2])[:120]
            self.log(f"⚠ AI 回了但配不到選項：{_preview}")
        return matched

    # ── GUI 建構 ──────────────────────────────────────────

    def _build_gui(self):
        style = ttk.Style()
        style.configure("Title.TLabel", font=("Microsoft JhengHei", 14, "bold"))
        style.configure("Big.TButton",  font=("Microsoft JhengHei", 11))

        main = ttk.Frame(self.root, padding=14)
        main.pack(fill=tk.BOTH, expand=True)

        ttk.Label(main, text="E等公務園 自動上課工具", style="Title.TLabel").pack(pady=(0, 10))

        # ── 帳號管理（合併登入方式+瀏覽器）──
        acc_frame = ttk.LabelFrame(main, text="帳號管理", padding=8)
        acc_frame.pack(fill=tk.X, pady=(0, 6))

        # 第一列：下拉選單 + 按鈕
        row1 = ttk.Frame(acc_frame)
        row1.pack(fill=tk.X, pady=(0, 4))

        self.account_selector = ttk.Combobox(row1, state="readonly")
        self.account_selector.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        self.account_selector.bind("<<ComboboxSelected>>", self._on_account_select)

        ttk.Button(row1, text="＋新增", width=6, command=self._add_account).pack(side=tk.LEFT, padx=(0, 2))
        ttk.Button(row1, text="✎編輯", width=6, command=self._edit_account).pack(side=tk.LEFT, padx=(0, 2))
        ttk.Button(row1, text="✕刪除", width=6, command=self._del_account).pack(side=tk.LEFT)

        # 第二列：目前帳號顯示（唯讀提示）
        row2 = ttk.Frame(acc_frame)
        row2.pack(fill=tk.X)
        ttk.Label(row2, text="目前帳號：", foreground="gray").pack(side=tk.LEFT)
        self.account_var = tk.StringVar()
        self.password_var = tk.StringVar()
        ttk.Label(row2, textvariable=self.account_var, foreground="#1565C0",
                  font=("Microsoft JhengHei", 9, "bold")).pack(side=tk.LEFT)

        self.login_type = tk.StringVar(value="elearn")
        self.browser_type = tk.StringVar(value="edge")

        # ── 控制按鈕（狀態切換：登入前/登入後）──
        self._btn_frame = ttk.Frame(main)
        self._btn_frame.pack(fill=tk.X, pady=(0, 6))

        self.login_btn = ttk.Button(self._btn_frame, text="登入",
                                    style="Big.TButton", command=self._on_login)
        self.start_btn = ttk.Button(self._btn_frame, text="開始上課",
                                    style="Big.TButton", command=self._on_start)
        # v1.8.18 「停止」改為「停止存檔退出」 — 仿 hiv_code 行為
        self.stop_btn  = ttk.Button(self._btn_frame, text="■ 停止存檔退出",
                                    style="Big.TButton", command=self._on_stop)
        self._set_btn_layout("pre_login")  # 初始狀態

        # ── AI Token 用量量表（v1.8.20）+ Gemini Key 管理 (v1.8.47) ──
        ai_frame = ttk.LabelFrame(main, text="🤖 AI Token 使用量", padding=6)
        ai_frame.pack(fill=tk.X, pady=(0, 6))

        # v1.8.47:Gemini Key 管理(仿帳號管理 UI)
        gk_row = ttk.Frame(ai_frame)
        gk_row.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(gk_row, text="Gemini Key：", font=("Microsoft JhengHei", 9)
                  ).pack(side=tk.LEFT)
        self.gemini_key_selector = ttk.Combobox(gk_row, state="readonly", width=24)
        self.gemini_key_selector.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(4, 6))
        self.gemini_key_selector.bind("<<ComboboxSelected>>", self._on_gemini_key_select)
        ttk.Button(gk_row, text="＋", width=3, command=self._add_gemini_key).pack(side=tk.LEFT, padx=1)
        ttk.Button(gk_row, text="✎", width=3, command=self._edit_gemini_key).pack(side=tk.LEFT, padx=1)
        ttk.Button(gk_row, text="✕", width=3, command=self._del_gemini_key).pack(side=tk.LEFT, padx=1)

        # 分隔線
        ttk.Separator(ai_frame, orient="horizontal").pack(fill=tk.X, pady=(2, 4))

        # 該 key 累積(v1.8.47)
        self.ai_persist_var = tk.StringVar(value="該 key 累積：尚未呼叫")
        ttk.Label(ai_frame, textvariable=self.ai_persist_var,
                  foreground="#1565C0",
                  font=("Microsoft JhengHei", 9)).pack(anchor="w")

        # 本 session
        self.ai_stats_var = tk.StringVar(value="本 session：呼叫 0 次　｜　輸入 0　｜　輸出 0 tokens")
        ttk.Label(ai_frame, textvariable=self.ai_stats_var,
                  font=("Microsoft JhengHei", 9)).pack(anchor="w")

        self.ai_cost_var = tk.StringVar(value="預估費用：$0.0000 USD（付費版價格，免費版實際 $0）")
        ttk.Label(ai_frame, textvariable=self.ai_cost_var,
                  foreground="#388E3C",
                  font=("Microsoft JhengHei", 9, "bold")).pack(anchor="w")

        ai_bar_row = ttk.Frame(ai_frame)
        ai_bar_row.pack(fill=tk.X, pady=(4, 0))
        self.ai_progress = ttk.Progressbar(ai_bar_row, maximum=GEMINI_FREE_RPD, length=300)
        self.ai_progress.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.ai_quota_var = tk.StringVar(value=f"0 / {GEMINI_FREE_RPD} 次（該 key 今日）")
        ttk.Label(ai_bar_row, textvariable=self.ai_quota_var,
                  foreground="gray", width=22, anchor="e").pack(side=tk.LEFT, padx=(6, 0))

        # ── 狀態 ──
        self.status_var = tk.StringVar(value="就緒")
        ttk.Label(main, textvariable=self.status_var, foreground="gray").pack(fill=tk.X)

        # ── 日誌 ──
        log_frame = ttk.LabelFrame(main, text="執行日誌", padding=4)
        log_frame.pack(fill=tk.BOTH, expand=True, pady=(4, 0))

        self.log_area = scrolledtext.ScrolledText(log_frame, height=12,
            font=("Consolas", 9), bg="#1e1e1e", fg="#00ff00", insertbackground="#00ff00")
        self.log_area.pack(fill=tk.BOTH, expand=True)

        bot = ttk.Frame(main)
        bot.pack(fill=tk.X, pady=(4, 0))
        ttk.Button(bot, text="清除 Log", command=self._clear_log).pack(side=tk.LEFT)
        ttk.Button(bot, text="儲存 Log", command=self._save_log).pack(side=tk.LEFT, padx=(8, 0))

        # ── 初始化帳號列表 ──
        self._refresh_account_list()
        # v1.8.47:初始化 Gemini Key 列表
        self._refresh_gemini_key_list()

    # ── 按鈕狀態管理 ─────────────────────────────────────

    def _set_btn_layout(self, state):
        """
        state:
          'pre_login'  → 登入 + 停止(disabled)     ← 未登入
          'logging_in' → 登入(disabled) + 停止       ← 登入中
          'ready'      → 開始上課 + 停止(disabled)   ← 已登入待命
          'running'    → 開始上課(disabled) + 停止   ← 上課中
        """
        for b in (self.login_btn, self.start_btn, self.stop_btn):
            b.pack_forget()

        if state == "pre_login":
            self.login_btn.config(state=tk.NORMAL)
            self.stop_btn.config(state=tk.DISABLED)
            self.login_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 4))
            self.stop_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
        elif state == "logging_in":
            self.login_btn.config(state=tk.DISABLED)
            self.stop_btn.config(state=tk.NORMAL)
            self.login_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 4))
            self.stop_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
        elif state == "ready":
            self.start_btn.config(state=tk.NORMAL)
            self.stop_btn.config(state=tk.DISABLED)
            self.start_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 4))
            self.stop_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
        elif state == "running":
            self.start_btn.config(state=tk.DISABLED)
            self.stop_btn.config(state=tk.NORMAL)
            self.start_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 4))
            self.stop_btn.pack(side=tk.LEFT, fill=tk.X, expand=True)

    def _is_logged_in(self):
        """偵測瀏覽器是否已登入 E等公務園
        v1.7.1：先強制切回主視窗 + 跳回 dashboard 再驗證，避免被 popup 殘留誤判
        """
        if not self.driver:
            return False
        try:
            # 先確保 driver 在主視窗
            try:
                handles = self.driver.window_handles
                if handles:
                    self.driver.switch_to.window(handles[0])
                self.driver.switch_to.default_content()
            except Exception:
                pass

            url = (self.driver.current_url or "").lower()
            # 接受所有 elearn.hrd.gov.tw 子網域（mohw / mosw / moe 等）
            if "elearn.hrd.gov.tw" not in url and "hrd.gov.tw" not in url:
                # 嘗試跳回 dashboard 再驗
                try:
                    self.driver.get(DASHBOARD_URL)
                    time.sleep(2)
                    url = (self.driver.current_url or "").lower()
                except Exception:
                    return False
            if "login" in url or "co_login" in url:
                return False
            # 找登入後才會有的元素
            els = self.driver.find_elements(By.CSS_SELECTOR,
                "a[href*='logout'], .logout_btn, a[href*='learn_dashboard'],"
                " a[href*='mycourse'], .user_name, .username")
            if els:
                return True
            # 二次驗證：抓 cookie 名（PHPSESSID 還在就視為登入）
            try:
                cookies = self.driver.get_cookies()
                names = [c.get("name", "") for c in cookies]
                if any("SESS" in n.upper() or "PHPSESS" in n.upper() for n in names):
                    return True
            except Exception:
                pass
            return False
        except Exception:
            return False

    def _ensure_on_dashboard(self):
        """檢查點：頁面偏離時自動回到儀表板，回傳是否執行了跳轉"""
        try:
            url = self.driver.current_url
            if "learn_dashboard" in url:
                return False  # 已在儀表板
            self.log(f"⚠ 頁面偏離（{url[:50]}），回到儀表板...")
            self.driver.get(DASHBOARD_URL)
            time.sleep(3)
            self._dismiss_page_popup()
            return True
        except Exception:
            return False

    # ── 帳號管理 ──────────────────────────────────────────

    def _refresh_account_list(self):
        accounts = self.config.get("accounts", [])
        names = [f"{a['account']} ({a.get('label', a['login_type'])})" for a in accounts]
        self.account_selector["values"] = names
        last = self.config.get("last_account", "")
        if accounts:
            idx = next((i for i, a in enumerate(accounts) if a["account"] == last), 0)
            self.account_selector.current(idx)
            self._load_account(accounts[idx])

    def _load_account(self, acc):
        self.account_var.set(acc.get("account", ""))
        self.password_var.set(acc.get("password", ""))
        self.login_type.set(acc.get("login_type", "elearn"))
        if acc.get("browser"):
            self.browser_type.set(acc["browser"])

    def _on_account_select(self, _=None):
        accounts = self.config.get("accounts", [])
        idx = self.account_selector.current()
        if 0 <= idx < len(accounts):
            self._load_account(accounts[idx])

    def _add_account(self):
        dlg = AccountDialog(self.root, title="新增帳號")
        if dlg.result:
            self.config.setdefault("accounts", []).append(dlg.result)
            self._save_config()
            self._refresh_account_list()

    def _edit_account(self):
        accounts = self.config.get("accounts", [])
        idx = self.account_selector.current()
        if idx < 0 or idx >= len(accounts):
            return
        dlg = AccountDialog(self.root, title="編輯帳號", data=accounts[idx])
        if dlg.result:
            accounts[idx] = dlg.result
            self._save_config()
            self._refresh_account_list()

    def _del_account(self):
        accounts = self.config.get("accounts", [])
        idx = self.account_selector.current()
        if idx < 0 or idx >= len(accounts):
            return
        if messagebox.askyesno("確認", f"刪除帳號 {accounts[idx]['account']}？"):
            accounts.pop(idx)
            self._save_config()
            self._refresh_account_list()

    # ── Gemini Key 管理 (v1.8.47) ────────────────────────────

    @staticmethod
    def _mask_api_key(k):
        """v1.8.47:遮罩顯示 key — 前 4 + ... + 後 4 (不夠就全遮)"""
        if not k:
            return ""
        if len(k) <= 8:
            return "•" * len(k)
        return f"{k[:4]}...{k[-4:]}"

    def _refresh_gemini_key_list(self):
        """v1.8.47:重整 key Combobox + 套用 self._gemini_key_idx 對應 key"""
        keys = self._gemini_keys
        names = [f"{k['label']} ({self._mask_api_key(k['key'])})" for k in keys]
        if hasattr(self, "gemini_key_selector"):
            self.gemini_key_selector["values"] = names
            if keys:
                idx = max(0, min(self._gemini_key_idx, len(keys) - 1))
                self._gemini_key_idx = idx
                self.gemini_key_selector.current(idx)
                self._gemini = keys[idx]["key"]
            else:
                self.gemini_key_selector.set("")
                self._gemini = None
        try:
            self._update_ai_stats()
        except Exception:
            pass

    def _on_gemini_key_select(self, _=None):
        """v1.8.47:UI 切換 key"""
        idx = self.gemini_key_selector.current()
        if 0 <= idx < len(self._gemini_keys):
            self._gemini_key_idx = idx
            self._gemini = self._gemini_keys[idx]["key"]
            self._gemini_429_streak = 0
            self.log(f"🔄 已切換 Gemini key 為「{self._gemini_keys[idx]['label']}」")
        try:
            self._update_ai_stats()
        except Exception:
            pass

    def _add_gemini_key(self):
        dlg = ApiKeyDialog(self.root, title="新增 Gemini Key")
        if not dlg.result:
            return
        import uuid
        sid = uuid.uuid4().hex[:12]
        new_entry = {"label": dlg.result["label"], "key": dlg.result["key"], "stats_id": sid}
        self._gemini_keys.append(new_entry)
        self.config["gemini_api_keys"] = [
            {"label": k["label"], "key": k["key"], "stats_id": k["stats_id"]}
            for k in self._gemini_keys
        ]
        self._save_config()
        self._refresh_gemini_key_list()
        self.log(f"✓ 新增 Gemini key「{new_entry['label']}」")

    def _edit_gemini_key(self):
        idx = self.gemini_key_selector.current()
        if idx < 0 or idx >= len(self._gemini_keys):
            return
        cur = self._gemini_keys[idx]
        dlg = ApiKeyDialog(self.root, title="編輯 Gemini Key",
                           data={"label": cur["label"], "key": cur["key"]})
        if not dlg.result:
            return
        # 保留 stats_id 不變(改名/改 key 不影響該 key 的累積)
        cur["label"] = dlg.result["label"]
        cur["key"]   = dlg.result["key"]
        self.config["gemini_api_keys"] = [
            {"label": k["label"], "key": k["key"], "stats_id": k["stats_id"]}
            for k in self._gemini_keys
        ]
        self._save_config()
        self._refresh_gemini_key_list()
        self.log(f"✓ 編輯 Gemini key「{cur['label']}」(stats 累積保留)")

    def _del_gemini_key(self):
        idx = self.gemini_key_selector.current()
        if idx < 0 or idx >= len(self._gemini_keys):
            return
        cur = self._gemini_keys[idx]
        if not messagebox.askyesno("確認", f"刪除 key「{cur['label']}」?\n(該 key 累積 stats 也會一併移除)"):
            return
        sid = cur.get("stats_id")
        # v1.8.48:索引調整防止 active 漂移
        was_active = (idx == self._gemini_key_idx)
        self._gemini_keys.pop(idx)
        if was_active:
            # 刪到當前生效的 → 退到 idx 0(若還有 key)
            self._gemini_key_idx = 0 if self._gemini_keys else 0
        elif idx < self._gemini_key_idx:
            # 刪除位於 active 之前 → active 索引要 -1 才指到原本那把
            self._gemini_key_idx -= 1
        # 邊界保護(理論上前面已涵蓋,雙保險)
        if self._gemini_key_idx >= len(self._gemini_keys):
            self._gemini_key_idx = max(0, len(self._gemini_keys) - 1)
        if sid:
            self.config.get("gemini_stats", {}).pop(sid, None)
        self.config["gemini_api_keys"] = [
            {"label": k["label"], "key": k["key"], "stats_id": k["stats_id"]}
            for k in self._gemini_keys
        ]
        self._save_config()
        self._refresh_gemini_key_list()
        if was_active and self._gemini_keys:
            self.log(f"✓ 已刪除 Gemini key「{cur['label']}」(原為當前生效,改用「{self._gemini_keys[0]['label']}」)")
        else:
            self.log(f"✓ 已刪除 Gemini key「{cur['label']}」")

    # ── 日誌 ──────────────────────────────────────────────

    def log(self, msg):
        ts = datetime.now().strftime("%H:%M:%S")
        self.log_area.insert(tk.END, f"[{ts}] {msg}\n")
        self.log_area.see(tk.END)

    def _set_status(self, text):
        self.status_var.set(text)

    # v1.8.20: AI Token 用量顯示（worker thread 呼叫，透過 after_idle 切回主執行緒）
    # v1.8.47:加「該 key 累積」+ progress bar 顯示該 key 今日
    def _update_ai_stats(self):
        # 本 session
        in_t  = self._stats.get("prompt_tokens", 0)
        out_t = self._stats.get("completion_tokens", 0)
        calls = self._stats.get("ai_calls_total", 0)
        cost  = (in_t * GEMINI_PRICE_IN) + (out_t * GEMINI_PRICE_OUT)

        # v1.8.47:該 key 累積(從 config 讀)
        sid = self._current_gemini_stats_id() if hasattr(self, "_current_gemini_stats_id") else None
        persist_text = "該 key 累積：尚未呼叫"
        today_calls = 0
        if sid:
            entry = (self.config.get("gemini_stats") or {}).get(sid)
            if entry:
                p_calls = int(entry.get("calls") or 0)
                p_in    = int(entry.get("in_tokens") or 0)
                p_out   = int(entry.get("out_tokens") or 0)
                p_first = entry.get("first_seen") or "—"
                p_last  = entry.get("last_seen") or "—"
                persist_text = (f"該 key 累積：呼叫 {p_calls:,}　｜　輸入 {p_in:,}　｜　"
                                f"輸出 {p_out:,} tokens　({p_first}~{p_last})")
                # 今日計數(progress bar 用)
                try:
                    from datetime import date
                    today = date.today().isoformat()
                    today_calls = int(((entry.get("by_date") or {}).get(today) or {}).get("calls") or 0)
                except Exception:
                    today_calls = p_calls

        def _do():
            try:
                if hasattr(self, "ai_persist_var"):
                    self.ai_persist_var.set(persist_text)
                self.ai_stats_var.set(
                    f"本 session：呼叫 {calls:,} 次　｜　輸入 {in_t:,}　｜　輸出 {out_t:,} tokens"
                )
                self.ai_cost_var.set(
                    f"預估費用：${cost:.4f} USD（付費版價格，免費版實際 $0）"
                )
                # progress bar:該 key 今日(若有 sid),否則退化到本 session
                bar_val = today_calls if sid else calls
                self.ai_progress["value"] = min(bar_val, GEMINI_FREE_RPD)
                self.ai_quota_var.set(
                    f"{bar_val} / {GEMINI_FREE_RPD} 次（該 key 今日）" if sid
                    else f"{bar_val} / {GEMINI_FREE_RPD} 次"
                )
            except Exception:
                pass

        try:
            self.root.after_idle(_do)
        except Exception:
            _do()

    def _clear_log(self):
        self.log_area.delete("1.0", tk.END)

    def _save_log(self):
        ts      = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_dir = os.path.join(_BASE_DIR, "log")
        os.makedirs(log_dir, exist_ok=True)
        path = os.path.join(log_dir, f"log_{ts}.txt")
        with open(path, "w", encoding="utf-8") as f:
            f.write(self.log_area.get("1.0", tk.END))
        self.log(f"日誌已儲存: {path}")

    # ── 瀏覽器啟動 ────────────────────────────────────────

    def _start_driver(self):
        browser = self.browser_type.get()
        self.log(f"啟動 {'Edge' if browser == 'edge' else 'Chrome'} 瀏覽器（自動對應 driver 版本）...")

        # ── 通用反自動化啟動參數 ───────────────────────────
        common_args = [
            "--start-maximized",
            "--disable-notifications",
            "--disable-blink-features=AutomationControlled",
            # 額外指紋一致化
            "--disable-features=IsolateOrigins,site-per-process",
            "--disable-site-isolation-trials",
            "--no-default-browser-check",
            "--no-first-run",
            "--password-store=basic",
            "--use-mock-keychain",
        ]

        if browser == "chrome":
            self.log("⏳ 首次使用 Chrome 需下載 ChromeDriver，可能等 1~2 分鐘，請勿關閉...")
            opts = ChromeOptions()
            for a in common_args:
                opts.add_argument(a)
            opts.add_experimental_option("excludeSwitches",
                                         ["enable-logging", "enable-automation"])
            opts.add_experimental_option("useAutomationExtension", False)
            self.driver = webdriver.Chrome(options=opts)
        else:
            opts = EdgeOptions()
            for a in common_args:
                opts.add_argument(a)
            opts.add_experimental_option("excludeSwitches",
                                         ["enable-logging", "enable-automation"])
            opts.add_experimental_option("useAutomationExtension", False)
            self.driver = webdriver.Edge(options=opts)

        # ── 全套 stealth 注入 ─────────────────────────────
        self._apply_stealth()

        self.log("瀏覽器啟動成功！（已啟用反爬蟲偽裝）")

    def _human_sleep(self, base=1.0, jitter=0.5):
        """模擬人類延遲（避免機器固定節奏）。base 秒 ± jitter 秒隨機。"""
        time.sleep(max(0.1, base + random.uniform(-jitter, jitter)))

    def _apply_stealth(self):
        """全套 stealth：CDP 注入 + 攔截檢舉請求 + UA 正常化
        對付方式：navigator.webdriver, plugins, languages, chrome,
                  permissions, mimeTypes, WebGL, hardwareConcurrency,
                  iframe contentWindow, headless 字串
        """
        # 1. 攔截「檢舉自動化」請求（看到的就只有 record_auto.php，但保險起見多加幾個）
        try:
            self.driver.execute_cdp_cmd("Network.enable", {})
            self.driver.execute_cdp_cmd("Network.setBlockedURLs", {"urls": [
                "*record_auto.php",
                "*record_bot*",
                "*report_bot*",
                "*detect_bot*",
                "*automation_log*",
            ]})
            self.log("✓ 已攔截自動化檢舉請求")
        except Exception as e:
            self.log(f"（注意）攔截檢舉請求失敗：{e}")

        # 2. v1.8.7: User-Agent 固定為一組「乾淨 Windows Chrome 120」字串
        #   原本讀原始 UA 再 strip HeadlessChrome → 每台機器不同、有機器辨識痕跡
        #   改為 setUserAgentOverride 強制固定（Selenium 與 qa_scraper.py 同一字串）+ 一併 spoof Client Hints
        try:
            self.driver.execute_cdp_cmd("Network.setUserAgentOverride", {
                "userAgent": FIXED_USER_AGENT,
                "acceptLanguage": "zh-TW,zh;q=0.9,en-US;q=0.8,en;q=0.7",
                "platform": "Win32",
                "userAgentMetadata": {
                    "brands": [
                        {"brand": "Not_A Brand", "version": "8"},
                        {"brand": "Chromium", "version": "120"},
                        {"brand": "Google Chrome", "version": "120"},
                    ],
                    "fullVersionList": [
                        {"brand": "Not_A Brand", "version": "8.0.0.0"},
                        {"brand": "Chromium", "version": "120.0.6099.109"},
                        {"brand": "Google Chrome", "version": "120.0.6099.109"},
                    ],
                    "fullVersion": "120.0.6099.109",
                    "platform": "Windows",
                    "platformVersion": "10.0.0",
                    "architecture": "x86",
                    "model": "",
                    "mobile": False,
                    "bitness": "64",
                    "wow64": False,
                },
            })
            self.log("✓ User-Agent 已固定（Windows Chrome 120 + Client Hints）")
        except Exception as e:
            self.log(f"⚠ User-Agent 固定失敗：{e}")

        # 3. 全套 JS 注入（在每個新文件、每個 frame 載入前執行）
        stealth_js = r"""
        (() => {
          // ── A. navigator.webdriver = undefined ──
          try {
            Object.defineProperty(Navigator.prototype, 'webdriver',
              {get: () => undefined, configurable: true});
          } catch(e) {}
          try {
            Object.defineProperty(navigator, 'webdriver',
              {get: () => undefined, configurable: true});
          } catch(e) {}

          // ── B. 偽造 plugins（一般瀏覽器至少 3 個） ──
          try {
            const fakePlugins = [
              {name: 'PDF Viewer', filename: 'internal-pdf-viewer',
               description: 'Portable Document Format'},
              {name: 'Chrome PDF Viewer', filename: 'internal-pdf-viewer',
               description: 'Portable Document Format'},
              {name: 'Chromium PDF Viewer', filename: 'internal-pdf-viewer',
               description: 'Portable Document Format'},
              {name: 'Microsoft Edge PDF Viewer', filename: 'internal-pdf-viewer',
               description: 'Portable Document Format'},
              {name: 'WebKit built-in PDF', filename: 'internal-pdf-viewer',
               description: 'Portable Document Format'},
            ];
            fakePlugins.item = i => fakePlugins[i];
            fakePlugins.namedItem = n => fakePlugins.find(p => p.name === n) || null;
            fakePlugins.refresh = () => {};
            Object.defineProperty(navigator, 'plugins',
              {get: () => fakePlugins, configurable: true});
          } catch(e) {}

          // ── C. languages ──
          try {
            Object.defineProperty(navigator, 'languages',
              {get: () => ['zh-TW', 'zh', 'en-US', 'en'], configurable: true});
          } catch(e) {}

          // ── D. mimeTypes ──
          try {
            const fakeMime = [{type: 'application/pdf', suffixes: 'pdf',
                               description: 'Portable Document Format'}];
            fakeMime.item = i => fakeMime[i];
            fakeMime.namedItem = n => fakeMime.find(m => m.type === n) || null;
            Object.defineProperty(navigator, 'mimeTypes',
              {get: () => fakeMime, configurable: true});
          } catch(e) {}

          // ── E. window.chrome stub ──
          try {
            if (!window.chrome) {
              window.chrome = {
                runtime: {}, app: {isInstalled: false},
                csi: function(){}, loadTimes: function(){return {};}
              };
            }
            if (window.chrome && !window.chrome.runtime) {
              window.chrome.runtime = {};
            }
          } catch(e) {}

          // ── F. permissions.query 修正（Notification 不一致 bug） ──
          try {
            const origQuery = navigator.permissions && navigator.permissions.query;
            if (origQuery) {
              navigator.permissions.query = (params) =>
                params && params.name === 'notifications'
                  ? Promise.resolve({state: Notification.permission, onchange: null})
                  : origQuery.call(navigator.permissions, params);
            }
          } catch(e) {}

          // ── G. WebGL Vendor / Renderer 不要露出 SwiftShader / Google ──
          try {
            const getParameter = WebGLRenderingContext.prototype.getParameter;
            WebGLRenderingContext.prototype.getParameter = function(p) {
              if (p === 37445) return 'Intel Inc.';
              if (p === 37446) return 'Intel Iris OpenGL Engine';
              return getParameter.apply(this, arguments);
            };
            if (window.WebGL2RenderingContext) {
              const getParameter2 = WebGL2RenderingContext.prototype.getParameter;
              WebGL2RenderingContext.prototype.getParameter = function(p) {
                if (p === 37445) return 'Intel Inc.';
                if (p === 37446) return 'Intel Iris OpenGL Engine';
                return getParameter2.apply(this, arguments);
              };
            }
          } catch(e) {}

          // ── H. hardwareConcurrency / deviceMemory 給合理值 ──
          try {
            Object.defineProperty(navigator, 'hardwareConcurrency',
              {get: () => 8, configurable: true});
          } catch(e) {}
          try {
            Object.defineProperty(navigator, 'deviceMemory',
              {get: () => 8, configurable: true});
          } catch(e) {}

          // ── I. iframe contentWindow.navigator.webdriver 也要藏 ──
          try {
            const elementDescriptor = Object.getOwnPropertyDescriptor(
                HTMLIFrameElement.prototype, 'contentWindow');
            Object.defineProperty(HTMLIFrameElement.prototype, 'contentWindow', {
              get: function() {
                const win = elementDescriptor.get.call(this);
                try {
                  Object.defineProperty(win.navigator, 'webdriver',
                    {get: () => undefined, configurable: true});
                } catch(e) {}
                return win;
              }
            });
          } catch(e) {}

          // ── J. 移除 Selenium 留下的 cdc_/$cdc 變數痕跡 ──
          try {
            for (const key of Object.keys(window)) {
              if (key.match(/^(cdc_|\$cdc_|__webdriver|__driver|__selenium|__fxdriver)/)) {
                try { delete window[key]; } catch(e) {}
              }
            }
          } catch(e) {}

          // ── K. Notification.permission 在 headless 下會錯亂 ──
          try {
            if (window.Notification && Notification.permission === 'denied') {
              Object.defineProperty(Notification, 'permission',
                {get: () => 'default', configurable: true});
            }
          } catch(e) {}

          // ── L. 把 toString 也假裝成 native ──
          try {
            const nativeToString = Function.prototype.toString;
            Function.prototype.toString = function() {
              if (this === navigator.permissions.query)
                return 'function query() { [native code] }';
              return nativeToString.call(this);
            };
          } catch(e) {}
        })();
        """
        try:
            self.driver.execute_cdp_cmd(
                "Page.addScriptToEvaluateOnNewDocument",
                {"source": stealth_js})
            self.log("✓ 已注入完整 stealth 腳本（12 項偽裝）")
        except Exception as e:
            self.log(f"⚠ stealth 注入失敗：{e}")

    # ── 登入流程 ──────────────────────────────────────────

    def _on_login(self):
        account  = self.account_var.get().strip()
        password = self.password_var.get().strip()
        if not account or not password:
            messagebox.showwarning("提示", "請輸入帳號和密碼（或新增帳號）")
            return
        # 若已登入，直接切就緒狀態
        if self._is_logged_in():
            self.log("已偵測到登入狀態，可直接開始上課")
            self._set_status("已登入 - 可以開始上課")
            self._set_btn_layout("ready")
            return
        self.config["last_account"] = account
        self._save_config()
        self.running = True
        self._set_btn_layout("logging_in")
        threading.Thread(target=self._login_thread, args=(account, password), daemon=True).start()

    def _login_thread(self, account, password):
        try:
            self._start_driver()
            self._login_elearn(account, password)
            ok = self._wait_for_login()
            if ok:
                self.log("登入成功！")
                self._set_status("已登入 - 啟動 Prefetch...")
                # v1.8.0：在開始上課前先掃待考課程清單，背景 prefetch 題庫
                try:
                    titles = self._collect_pending_course_titles()
                    if titles:
                        preview = "、".join(titles[:3]) + (
                            f" ...等 {len(titles)} 門" if len(titles) > 3 else "")
                        self.log(f"🎯 待考課程：{preview}")
                        self._start_prefetch_pending(titles)
                except Exception as e:
                    self.log(f"⚠ 待考清單掃描/Prefetch 啟動失敗：{e}")
                self.log("自動開始上課...")
                self._set_status("已登入 - 自動開始上課")
                self._set_btn_layout("ready")
                self._on_start()   # 登入成功 → 自動開始
            else:
                self.log("⚠ 未偵測到登入成功，請確認瀏覽器狀態")
                self._set_status("登入未確認 - 可手動按「開始上課」")
                self._set_btn_layout("ready")  # 允許手動啟動
        except Exception as e:
            self.log(f"登入失敗: {e}")
            self._set_status("登入失敗")
            self._set_btn_layout("pre_login")

    def _dismiss_page_popup(self, timeout=2):
        """關閉各頁面的「了解，我清楚了」公告彈窗"""
        try:
            btn = WebDriverWait(self.driver, timeout).until(EC.element_to_be_clickable(
                (By.XPATH, "//button[contains(@class,'buttom_btn') and contains(normalize-space(),'了解')]"
                           " | //button[contains(normalize-space(),'了解，我清楚了')]"
                           " | //a[contains(normalize-space(),'了解，我清楚了')]")))
            self.driver.execute_script("arguments[0].click()", btn)
            self.log("已關閉公告彈窗")
        except TimeoutException:
            pass

    def _login_elearn(self, account, password):
        """E等公務園登入 → 我的e政府帳號登入（事件驅動，減少固定等待）"""
        # ── Step 0: 首頁 → 關閉公告 ──
        self.log("導航到 E等公務園...")
        self.driver.get(ELEARN_HOME)
        self._dismiss_page_popup()

        # ── Step 1: 點 .login-btn → 導至 co_login_dialog.php ──
        self.log("點擊登入按鈕...")
        try:
            btn = WebDriverWait(self.driver, 8).until(
                EC.element_to_be_clickable((By.CSS_SELECTOR, "a.login-btn")))
            btn.click()
            WebDriverWait(self.driver, 8).until(
                lambda d: "co_login_dialog" in d.current_url)
        except TimeoutException:
            self.log("直接導航到登入選擇頁...")
            self.driver.get("https://elearn.hrd.gov.tw/mooc/co_login_dialog.php")

        # ── Step 2: 登入選擇頁 → 關閉公告 → 點我的e政府(公務人員) ──
        self._dismiss_page_popup()
        self.log("點擊「我的e政府」（公務人員）...")
        try:
            gov = WebDriverWait(self.driver, 8).until(
                EC.element_to_be_clickable(
                    (By.CSS_SELECTOR, "a.gov_btn[href*='identity=1']")))
            gov.click()
            WebDriverWait(self.driver, 8).until(
                lambda d: "co_gov_login_guide" in d.current_url)
        except TimeoutException:
            self.log("找不到「我的e政府」按鈕")
            return

        # ── Step 3: 說明頁 → 點橘色「登入我的e政府」按鈕 ──
        self.log("點擊「登入我的e政府」...")
        try:
            btn = WebDriverWait(self.driver, 8).until(
                EC.element_to_be_clickable(
                    (By.CSS_SELECTOR, "button.gov-btn, a.gov-btn")))
            btn.click()
        except TimeoutException:
            try:
                btn = WebDriverWait(self.driver, 5).until(EC.element_to_be_clickable(
                    (By.XPATH, "//*[contains(normalize-space(),'登入我的e政府')]")))
                btn.click()
            except TimeoutException:
                self.log("找不到「登入我的e政府」")
                return

        # 等新視窗出現或帳密欄就緒（取代固定等待）
        try:
            WebDriverWait(self.driver, 12).until(
                lambda d: len(d.window_handles) > 1
                          or "aliasid" in d.page_source
                          or "我的E政府帳號登入" in d.page_source)
        except TimeoutException:
            self.log("⚠ 等待eGOV頁面逾時，目前URL: " + self.driver.current_url)
        if len(self.driver.window_handles) > 1:
            self.driver.switch_to.window(self.driver.window_handles[-1])

        # ── Step 4: eGOV 選單 → 點「我的E政府帳號登入」──
        self.log("選擇「我的E政府帳號登入」...")
        try:
            btn = WebDriverWait(self.driver, 10).until(EC.element_to_be_clickable(
                (By.XPATH, "(//a | //button)[contains(normalize-space(),'我的E政府帳號登入')]")))
            btn.click()
            self.log("已點擊「我的E政府帳號登入」")
        except TimeoutException:
            self.log("找不到「我的E政府帳號登入」，直接找帳密欄")

        # ── Step 5: 等帳號欄可點擊後填入帳密 ──
        self.log("填入帳號密碼...")
        try:
            acct = WebDriverWait(self.driver, 10).until(EC.element_to_be_clickable(
                (By.CSS_SELECTOR,
                 "input[placeholder='帳號'], input[name='aliasid'], input[type='text']")))
            acct.clear()
            acct.send_keys(account)
            pwd = self.driver.find_element(By.CSS_SELECTOR,
                "input[placeholder='密碼'], input[name='pas'], input[type='password']")
            pwd.clear()
            pwd.send_keys(password)
            submit = self.driver.find_element(By.XPATH,
                "//button[contains(text(),'登入')] | //input[@type='submit']")
            submit.click()
            self.log("已送出登入，等待回應...")
        except TimeoutException:
            self.log("⚠ 找不到帳號/密碼欄位，目前URL: " + self.driver.current_url)
        except Exception as e:
            self.log(f"⚠ 填入帳密失敗: {e}")

    def _login_ecpa(self, account, password):
        """人事服務網 eCPA 帳密登入"""
        self.log("導航到人事服務網...")
        self.driver.get(ECPA_LOGIN)
        wait = WebDriverWait(self.driver, 15)
        alias = wait.until(EC.presence_of_element_located((By.ID, "aliasid")))
        alias.clear()
        alias.send_keys(account)
        pas = self.driver.find_element(By.ID, "pas")
        pas.clear()
        pas.send_keys(password)
        self.log("填入帳密，送出登入...")
        self.driver.execute_script("startIdPas()")

    def _wait_for_login(self, timeout=60):
        """等待登入成功，回傳 True=成功 / False=逾時"""
        self.log("等待登入回應...")
        try:
            WebDriverWait(self.driver, timeout).until(lambda d:
                "elearn.hrd.gov.tw" in d.current_url and
                "login" not in d.current_url.lower() and
                d.find_elements(By.CSS_SELECTOR,
                    "a[href*='logout'], .logout_btn, [href*='learn_dashboard'], a[href*='mycourse']"))
            self._read_login_popup()
            self._dismiss_popups()
            return True
        except TimeoutException:
            cur = self.driver.current_url if self.driver else "無瀏覽器"
            self.log(f"⚠ 登入逾時，目前停在：{cur}")
            self.log("可手動完成登入後按「開始上課」")
            self._dismiss_popups()
            return False
        except WebDriverException as e:
            self.log(f"⚠ 瀏覽器異常：{e}")
            return False

    def _read_login_popup(self):
        """讀取登入後的統計彈窗資訊（等待彈窗出現）"""
        try:
            # 等待彈窗出現（含「未完成課程數」或「未完成課程」文字）
            time.sleep(2)
            body = self.driver.find_element(By.TAG_NAME, "body").text
            # 支援「未完成課程數: 7」或「未完成課程數\n7」兩種格式
            m_course = re.search(r'未完成課程[數]?\D{0,3}?(\d+)', body)
            m_exam   = re.search(r'待完成測驗[數]?\D{0,3}?(\d+)', body)
            m_survey = re.search(r'待完成問卷[數]?\D{0,3}?(\d+)', body)
            if m_course:
                self.popup_pending_course = int(m_course.group(1))
                self.popup_pending_exam   = int(m_exam.group(1))   if m_exam   else -1
                self.popup_pending_survey = int(m_survey.group(1)) if m_survey else -1
                self.log(f"未完成課程: {m_course.group(1)} 門 | "
                         f"待完成測驗: {m_exam.group(1) if m_exam else '?'} 個 | "
                         f"待完成問卷: {m_survey.group(1) if m_survey else '?'} 份")
            else:
                # 找不到特定格式，直接找包含數字的關鍵行
                for line in body.split("\n"):
                    if "未完成" in line and any(c.isdigit() for c in line):
                        self.log(f"登入統計: {line.strip()}")
                        break
        except Exception:
            pass

    def _dismiss_popups(self):
        """自動關閉彈窗"""
        close_texts = ['了解，我清楚了', '我知道了', '確定', '關閉此視窗', '關閉']
        for text in close_texts:
            try:
                btns = self.driver.find_elements(By.XPATH, f"//*[text()='{text}']")
                for btn in btns:
                    if btn.is_displayed():
                        self.driver.execute_script("arguments[0].click()", btn)
                        self.log(f"已關閉彈窗（{text}）")
                        time.sleep(1)
            except Exception:
                pass
        try:
            for sel in [".fancybox-close", ".fancybox-close-small", "a.fancybox-item"]:
                for btn in self.driver.find_elements(By.CSS_SELECTOR, sel):
                    if btn.is_displayed():
                        self.driver.execute_script("arguments[0].click()", btn)
                        time.sleep(0.5)
        except Exception:
            pass

    # ── v1.8.0 Prefetch：登入後同步爬待考課程的題庫 ────────

    @staticmethod
    def _norm_title_key(t):
        """課名 → prefetch 字典 key（去空白、括號內容、講次）"""
        if not t:
            return ""
        s = re.sub(r'[\(（【].*?[\)）】]', '', t)
        s = re.sub(r'第\s*\d+\s*[講章節課集回單元]', '', s)
        s = re.sub(r'[\s　,，.。、；;：:！!？?\-—–\\/\[\]【】《》]+', '', s)
        return s.lower()

    def _collect_pending_course_titles(self, max_pages=5):
        """掃描 dashboard「未完成」分頁，回傳所有課程標題 list（去重）。
        會自動翻頁最多 max_pages 頁。掃完後不會回到原本位置 — caller 自己負責導頁。
        """
        titles = []
        seen = set()
        try:
            self.driver.get(DASHBOARD_URL)
            time.sleep(2.5)
            self._dismiss_popups()
            self._click_tab("未完成")
            time.sleep(1.5)
        except Exception as e:
            self.log(f"⚠ 無法掃描未完成課程標題：{e}")
            return titles

        for page in range(max_pages):
            try:
                # 抓所有 course-list-block 卡片
                cards = self.driver.find_elements(By.CSS_SELECTOR,
                    ".course-list-block")
                if not cards:
                    # 退而求其次：找含 /info/ 的連結
                    cards = self.driver.find_elements(By.CSS_SELECTOR,
                        "a[href*='/info/']")
                for card in cards:
                    if not card.is_displayed():
                        continue
                    title = ""
                    # 從卡片找標題
                    for ts in [".//div[contains(@class,'cb-info-name1')]",
                               ".//div[contains(@class,'course-list-block-info-name')]",
                               ".//h3", ".//h4",
                               ".//*[contains(@class,'title')]",
                               ".//strong"]:
                        try:
                            elt = card.find_element(By.XPATH, ts)
                            t = (elt.get_attribute("title") or elt.text or "").strip()
                            if t and len(t) > 3:
                                title = t
                                break
                        except Exception:
                            pass
                    if not title:
                        # 連結本身的 title 或 text
                        t = (card.get_attribute("title") or card.text or "").strip()
                        if t and len(t) > 3:
                            title = t.split("\n")[0].strip()
                    if not title:
                        continue
                    key = self._norm_title_key(title)
                    if key and key not in seen:
                        seen.add(key)
                        titles.append(title)
            except Exception:
                pass
            # 翻頁
            if not self._click_next_page():
                break
            time.sleep(1.8)

        return titles

    def _start_prefetch_pending(self, titles):
        """背景啟動 prefetch worker。non-blocking。"""
        if not _SCRAPER_AVAILABLE:
            self.log(f"⚠ qa_scraper 模組無法載入，跳過 prefetch（{_SCRAPER_IMPORT_ERR}）")
            return
        if not titles:
            self.log("📥 無待考課程，跳過 prefetch")
            return
        # 先把所有 title 標記為 queued 並建立 event
        with self._prefetch_lock:
            for t in titles:
                k = self._norm_title_key(t)
                if k and k not in self._prefetch_status:
                    self._prefetch_status[k] = "queued"
                    self._prefetch_events[k] = threading.Event()
        self.log(f"📥 啟動背景 prefetch（{len(titles)} 門課程）")
        self._prefetch_thread = threading.Thread(
            target=self._prefetch_worker, args=(titles,), daemon=True)
        self._prefetch_thread.start()

    def _prefetch_worker(self, titles):
        """背景執行：載入索引 → 並行查每課 → 寫入 qa_bank"""
        try:
            # 1) 載入索引（30 天 cache）
            try:
                self.log("📥 載入 roddayeye 課程索引...")
                idx = fetch_index(QA_INDEX_FILE)
                self._prefetch_index = idx
                self.log(f"📥 索引共 {len(idx)} 課（cache 30 天）")
            except Exception as e:
                self.log(f"⚠ 載入索引失敗：{e}")
                # 把所有 event 都 release，避免主流程一直等
                with self._prefetch_lock:
                    for k, ev in self._prefetch_events.items():
                        self._prefetch_status[k] = "err"
                        ev.set()
                return

            # 2) 並行抓答案
            with ThreadPoolExecutor(max_workers=4) as pool:
                futures = {pool.submit(self._prefetch_one, t, idx): t for t in titles}
                done_n = 0
                for fut in as_completed(futures):
                    done_n += 1
                    title = futures[fut]
                    try:
                        n_added = fut.result()
                    except Exception as e:
                        n_added = -1
                        self.log(f"⚠ Prefetch 失敗 {title}：{e}")
                    if n_added > 0:
                        self.log(f"📥 [{done_n}/{len(titles)}] ✓ {title}（+{n_added} 題）")
                    elif n_added == -3:
                        self.log(f"📥 [{done_n}/{len(titles)}] ✓ {title}（題庫已備齊）")
                    elif n_added == 0:
                        self.log(f"📥 [{done_n}/{len(titles)}] ⚠ {title}（roddayeye 無此課）")
                    elif n_added == -2:
                        self.log(f"📥 [{done_n}/{len(titles)}] ⚠ {title}（找不到匹配課名）")
                    elif n_added == -1:
                        self.log(f"📥 [{done_n}/{len(titles)}] ✕ {title}（fetch 錯誤）")

            # 3) 寫入 qa_bank
            try:
                self.qa_bank.save()
            except Exception:
                pass
            self.log(f"📥 Prefetch 完成，題庫共 {self.qa_bank.count()} 題")
        except Exception as e:
            self.log(f"⚠ Prefetch worker 異常：{e}")

    def _prefetch_one(self, title, idx):
        """單課 prefetch
        回傳碼：>0 新加題數；0 真的沒題；-2 找不到課；-3 已快取（題庫已備齊）；-1 錯誤"""
        k = self._norm_title_key(title)
        with self._prefetch_lock:
            self._prefetch_status[k] = "fetching"
        try:
            hits = fuzzy_lookup(title, idx, threshold=0.55, top_k=1)
            if not hits:
                with self._prefetch_lock:
                    self._prefetch_status[k] = "miss"
                    if k in self._prefetch_events:
                        self._prefetch_events[k].set()
                return -2
            score, name, url = hits[0]
            qs = fetch_and_parse(url, timeout=20)
            n_total = 0
            n_added = 0
            for q in qs:
                qtext = q.get("q") or ""
                ans   = q.get("a") or []
                qtype = q.get("type") or "SC"
                if not qtext or not ans:
                    continue
                n_total += 1
                # v1.8.7 bug #5：prefetch 用 add_if_absent（低信任，不覆蓋 harvester/手工答案）
                before = self.qa_bank.has_exact(qtext)
                self.qa_bank.add_if_absent(qtext, ans, qtype=qtype, course=name)
                if not before:
                    n_added += 1
            # v1.8.7：「題庫已備齊」也算 done，否則一直被當 miss
            has_answers = n_total > 0
            with self._prefetch_lock:
                self._prefetch_status[k] = "done" if has_answers else "miss"
                if k in self._prefetch_events:
                    self._prefetch_events[k].set()
            if n_added > 0:
                return n_added
            return -3 if has_answers else 0
        except Exception:
            with self._prefetch_lock:
                self._prefetch_status[k] = "err"
                if k in self._prefetch_events:
                    self._prefetch_events[k].set()
            return -1

    def _wait_for_prefetch(self, title, timeout=15):
        """阻塞最多 timeout 秒，等指定課程 prefetch 完成。回傳 status 字串。"""
        if not title:
            return "skip"
        k = self._norm_title_key(title)
        with self._prefetch_lock:
            ev = self._prefetch_events.get(k)
            status = self._prefetch_status.get(k, "unknown")
        if status in ("done", "miss", "err"):
            return status
        if ev is None:
            return "unknown"
        if ev.wait(timeout):
            with self._prefetch_lock:
                return self._prefetch_status.get(k, "unknown")
        return "timeout"

    # ── 自動上課核心 ──────────────────────────────────────

    def _on_start(self):
        if not self.driver:
            messagebox.showwarning("提示", "請先登入")
            return
        self.running = True
        self.cycle_count = 0
        self._set_btn_layout("running")
        self._set_status("上課中...")
        threading.Thread(target=self._auto_learn_main, daemon=True).start()

    def _on_stop(self):
        """v1.8.18：停止 = 收尾統計 + 存 log + 存題庫 + 關瀏覽器 + 關程式
           （仿 hiv_code「停止存檔退出」行為）"""
        self.running = False
        self._set_status("已停止 → 存檔中…")
        try:
            self._print_session_stats()
        except Exception:
            pass
        try:
            self.qa_bank.save()
        except Exception:
            pass
        try:
            self._save_missed_questions()
        except Exception:
            pass
        try:
            self._save_config()
        except Exception:
            pass
        # v1.8.18：自動存 log（無需使用者手動按）
        try:
            self._save_log()
        except Exception:
            pass
        # 走完整 _on_close 關瀏覽器 + 關程式
        try:
            self._on_close()
        except Exception:
            try: self.root.destroy()
            except Exception: pass

    def _auto_learn_main(self):
        # 重置「已嘗試課程」清單（每次按開始上課都從頭算）
        self._tried_hrefs = set()
        # 未完成階段連續找不到課程的次數，用來防止無限 retry
        miss_unfinished = 0
        try:
            while self.running:
                # v1.7.1：每輪先強制清理多餘視窗 + 跳回 dashboard
                try:
                    self._close_extra_windows()
                except Exception:
                    pass
                self._dismiss_popups()
                if not self._is_logged_in():
                    self.log("⚠ 偵測到登入狀態失效，請重新登入")
                    break

                # ── 第一階段：未完成(有時數)課程 → 讀+測驗+問卷 ──
                self.log("進入我的課程...")
                self.driver.get(DASHBOARD_URL)
                time.sleep(3)
                self._dismiss_popups()
                self._click_tab("未完成")
                time.sleep(2)

                # 在目前頁面找未嘗試課程；找不到就翻下一頁直到沒有為止
                entry = self._find_course_entry(exclude_tried=True)
                while entry is None:
                    if self._click_next_page():
                        self.log("本頁已無新課程，翻到下一頁...")
                        time.sleep(2)
                        entry = self._find_course_entry(exclude_tried=True)
                    else:
                        break  # 沒有下一頁了

                if entry:
                    miss_unfinished = 0
                    href = entry.get_attribute("href") or ""
                    if href:
                        self._tried_hrefs.add(href)
                    title, needs_log, exam_score, exam_pass, had_steps = self._extract_card_info(entry)
                    self._current_course_title = title or ""
                    # v1.8.24：had_steps=True 才信任 needs 的 False;否則保 None(未知)
                    if had_steps:
                        self._current_needs = {
                            "reading": "未閱讀" in needs_log,
                            "exam":    "未測驗" in needs_log,
                            "survey":  "未問卷" in needs_log,
                        }
                    else:
                        self._current_needs = {"reading": None, "exam": None, "survey": None}
                    self._current_exam_score  = exam_score
                    self._current_exam_pass   = exam_pass
                    self._current_already_min = None  # 進詳情頁後 _log_course_info 解析
                    extras = []
                    if exam_score is not None: extras.append(f"分數={exam_score:g}")
                    if exam_pass  is not None: extras.append(f"及格={exam_pass:g}")
                    self.log(f"── 進入課程: {title or '(課程)'}"
                             + (f" [{needs_log}]" if needs_log else "")
                             + ((" " + " ".join(extras)) if extras else ""))
                    self.driver.execute_script("arguments[0].click()", entry)
                    time.sleep(3)
                    self._process_current_course_page()
                    if self.running:
                        self.log("本門課程處理完畢，繼續下一門...")
                        time.sleep(3)
                    continue
                else:
                    # 找不到入口 — 但彈窗明明說還有未完成課程？
                    # 排除「已嘗試過」就完全沒結果，可能是真的全部嘗試過 → 進階段二
                    any_entry = self._find_course_entry(exclude_tried=False)
                    if any_entry is None and self.popup_pending_course > 0:
                        miss_unfinished += 1
                        self.log(f"⚠ 未完成分頁找不到任何課程入口，但登入彈窗顯示尚有 "
                                 f"{self.popup_pending_course} 門未完成（第 {miss_unfinished} 次）")
                        self._dump_unfinished_debug()
                        if miss_unfinished >= 3:
                            self.log("⚠ 已連續 3 次找不到未完成課程入口，請查看 DEBUG dump")
                            self.log("⚠ 不跳到「已完成」分頁（避免誤判），結束本次自動上課")
                            break
                        self.log("重新整理頁面後再試...")
                        time.sleep(2)
                        continue
                    # 有課程但全部已嘗試過 → 第一階段確實清空，進入階段二
                    if any_entry is not None:
                        self.log(f"未完成分頁的 {len(self._tried_hrefs)} 門課皆已嘗試過，"
                                 f"進入第二階段...")

                # ── 第二階段：已完成課程 → 補測驗 / 補問卷 ──
                # 只有在 popup 確認未完成 = 0 且仍有測驗/問卷待補時才進入
                need_exam   = (self.popup_pending_exam   > 0)
                need_survey = (self.popup_pending_survey > 0)
                if not (need_exam or need_survey):
                    # v1.8.15: popup 數字是登入時的快照，不會隨通關更新。
                    # 用本 session 實際統計取代誤導訊息。
                    s = self._stats or {}
                    self.log(f"所有課程已嘗試完畢（本 session 通過 {s.get('courses_passed',0)} 門 / "
                             f"未過 {s.get('courses_failed',0)} 門 / "
                             f"原始未完成 {self.popup_pending_course} 門）")
                    break

                self.log(f"未完成課程已清空，掃描待補測驗 {self.popup_pending_exam} 個 / "
                         f"問卷 {self.popup_pending_survey} 份...")
                self._click_tab("已完成")
                time.sleep(2)
                pend_entry, reason = self._find_pending_work_entry(
                    want_exam=need_exam, want_survey=need_survey)
                if pend_entry:
                    href = pend_entry.get_attribute("href") or ""
                    if href and href in self._tried_hrefs:
                        self.log(f"⚠ 此課程已嘗試過（{href[:60]}），結束")
                        break
                    if href:
                        self._tried_hrefs.add(href)
                    title, _needs_log, exam_score, exam_pass, _had = self._extract_card_info(pend_entry)
                    self._current_course_title = title or ""
                    # v1.8.23：補做場景 reason 已知；reading 視為已達標（不然不會出現在已完成）
                    self._current_needs = {
                        "reading": False,
                        "exam":    (reason == "exam"),
                        "survey":  (reason == "survey"),
                    }
                    self._current_exam_score  = exam_score
                    self._current_exam_pass   = exam_pass
                    self._current_already_min = None
                    label = {"exam": "補做測驗", "survey": "補做問卷"}.get(reason, "補做")
                    self.log(f"── {label}: {title or '(課程)'}")
                    self.driver.execute_script("arguments[0].click()", pend_entry)
                    time.sleep(3)
                    self._process_current_course_page()
                    if self.running:
                        time.sleep(3)
                    continue

                self.log("找不到待補測驗/問卷的課程，結束")
                break

        except Exception as e:
            self.log(f"自動上課發生錯誤: {e}")
        finally:
            self._set_status("已結束")
            self.running = False
            if self._is_logged_in():
                self._set_btn_layout("ready")
            else:
                self._set_btn_layout("pre_login")

    def _click_tab(self, keyword):
        """點擊包含 keyword 的分頁，回傳是否成功"""
        try:
            for el in self.driver.find_elements(By.XPATH,
                    f"//*[contains(text(),'{keyword}')]"):
                if el.is_displayed():
                    self.driver.execute_script("arguments[0].click()", el)
                    self.log(f"已切換到「{keyword}」分頁")
                    time.sleep(2)
                    return True
        except Exception as e:
            self.log(f"切換分頁失敗: {e}")
        return False

    def _find_course_entry(self, exclude_tried=True):
        """找「未完成(有時數)」分頁上可點擊的課程入口（優先標準 href，再 onclick/javascript:）"""
        exclude_text = {"退選", "登出", "搜尋", "排序", "常見問題", "下載",
                        "回首頁", "簡易操作", "加盟", "學習紀錄", "選課中心",
                        "學習目標", "了解", "確定", "關閉", "搜尋與排序"}

        # 方法0（最高優先）：course-list-block 內的課程 <a>（最精準）
        try:
            for el in self.driver.find_elements(By.CSS_SELECTOR,
                    ".course-list-block a[href*='/info/']"):
                if not el.is_displayed():
                    continue
                href = el.get_attribute("href") or ""
                if exclude_tried and href in self._tried_hrefs:
                    continue
                return el
        except Exception:
            pass

        # 方法0b：所有 /info/<id> 連結（fallback）
        try:
            for el in self.driver.find_elements(By.CSS_SELECTOR, "a[href*='/info/']"):
                if not el.is_displayed():
                    continue
                href = el.get_attribute("href") or ""
                if not re.search(r'/info/\d+', href):
                    continue
                if exclude_tried and href in self._tried_hrefs:
                    continue
                return el
        except Exception:
            pass

        # 方法0c：其他舊版 e等公務園 路徑
        course_selectors = [
            "a[href*='course_main']",
            "a[href*='course_id']",
            "a[href*='/open/']",
            "a[href*='mooc/course']",
            "a[href*='learn/course']",
            "a[href*='courseId']",
        ]
        skip_hrefs = {"dashboard", "logout", "login", "search", "sitemap"}
        for sel in course_selectors:
            try:
                for el in self.driver.find_elements(By.CSS_SELECTOR, sel):
                    if not el.is_displayed():
                        continue
                    href = el.get_attribute("href") or ""
                    if any(k in href for k in skip_hrefs):
                        continue
                    if exclude_tried and href in self._tried_hrefs:
                        continue
                    return el
            except Exception:
                pass

        # 方法1：有 onclick 的元素
        try:
            for el in self.driver.find_elements(By.XPATH, "//*[@onclick]"):
                if not el.is_displayed():
                    continue
                text = el.text.strip()
                onclick = el.get_attribute("onclick") or ""
                if any(k in text for k in exclude_text):
                    continue
                if any(k in onclick.lower() for k in
                       ["course", "gopage", "location", "open", "learn", "href"]):
                    return el
        except Exception:
            pass

        # 方法2：javascript: href 且在課程卡片內（過濾分享連結）
        share_kw = {"share", "wechat", "fb", "line"}
        try:
            for el in self.driver.find_elements(By.CSS_SELECTOR, "a[href^='javascript']"):
                if not el.is_displayed():
                    continue
                if any(k in el.text.strip() for k in exclude_text):
                    continue
                href = el.get_attribute("href") or ""
                if any(k in href.lower() for k in share_kw):
                    continue
                try:
                    el.find_element(By.XPATH,
                        "./ancestor::div[contains(@class,'course') or "
                        "contains(@class,'box') or contains(@class,'item') or "
                        "contains(@class,'card')][1]")
                    return el
                except Exception:
                    continue
        except Exception:
            pass

        return None

    def _find_pending_work_entry(self, want_exam=True, want_survey=True):
        """在已完成課程中找到還有待完成工作的課程入口
        回傳 (element, reason)：reason ∈ {'exam', 'survey', None}
        判斷規則（依 want 參數開關）：
          - 測驗分數：0 分 → exam
          - 問卷狀態：未填寫 → survey
        已嘗試過的課程（self._tried_hrefs）會跳過
        """
        course_selectors = [
            ".course-list-block a[href*='/info/']",
            "a[href*='/info/']",
            "a[href*='course_main']",
            "a[href*='course_id']",
            "a[href*='/open/']",
            "a[href*='mooc/course']",
            "a[href*='learn/course']",
            "a[href*='courseId']",
        ]
        skip_hrefs = {"dashboard", "logout", "login", "search", "sitemap"}

        for sel in course_selectors:
            try:
                for el in self.driver.find_elements(By.CSS_SELECTOR, sel):
                    if not el.is_displayed():
                        continue
                    href = el.get_attribute("href") or ""
                    if any(k in href for k in skip_hrefs):
                        continue
                    if href and href in self._tried_hrefs:
                        continue
                    # 找父卡片，檢查待完成項目（優先 course-list-block）
                    try:
                        try:
                            card = el.find_element(By.XPATH,
                                "./ancestor::div[contains(@class,'course-list-block')][1]")
                        except Exception:
                            card = el.find_element(By.XPATH,
                                "./ancestor::div[contains(@class,'course') or "
                                "contains(@class,'card') or contains(@class,'item') or "
                                "contains(@class,'box')][1]")
                        card_text = card.text
                        # 測驗分數：0 分 → 需補考
                        if want_exam and re.search(r'測驗分數[：:]\s*0\s*分', card_text):
                            return el, "exam"
                        # 問卷狀態：未填寫 → 需補問卷
                        if want_survey and re.search(r'問卷狀態[：:]\s*未填寫', card_text):
                            return el, "survey"
                    except Exception:
                        pass
            except Exception:
                pass
        return None, None

    def _dump_unfinished_debug(self):
        """未完成分頁找不到課程入口時，dump 頁面所有可見元素到 log，方便排查"""
        try:
            self.log("─── DEBUG dump 開始 ───")
            self.log(f"目前 URL: {self.driver.current_url}")
            self.log(f"頁面標題: {self.driver.title}")

            # dump 所有可見 <a> 連結
            anchors = self.driver.find_elements(By.TAG_NAME, "a")
            shown = 0
            for a in anchors:
                try:
                    if not a.is_displayed():
                        continue
                    href = (a.get_attribute("href") or "").strip()
                    text = (a.text or "").strip().replace("\n", " ")
                    if not href and not text:
                        continue
                    self.log(f"  [a] href={href[:80]!r}  text={text[:40]!r}")
                    shown += 1
                    if shown >= 30:
                        self.log(f"  ... 已顯示 30 筆 <a>，省略其餘")
                        break
                except Exception:
                    continue

            # dump 所有有 onclick 的可見元素
            shown = 0
            for el in self.driver.find_elements(By.XPATH, "//*[@onclick]"):
                try:
                    if not el.is_displayed():
                        continue
                    onclick = (el.get_attribute("onclick") or "").strip()
                    text = (el.text or "").strip().replace("\n", " ")
                    self.log(f"  [onclick] tag={el.tag_name} text={text[:30]!r} "
                             f"onclick={onclick[:80]!r}")
                    shown += 1
                    if shown >= 15:
                        self.log(f"  ... 已顯示 15 筆 onclick 元素，省略其餘")
                        break
                except Exception:
                    continue

            # 把整頁 HTML 存檔，方便事後分析
            try:
                log_dir = os.path.join(_BASE_DIR, "log")
                os.makedirs(log_dir, exist_ok=True)
                ts = datetime.now().strftime("%Y%m%d_%H%M%S")
                html_path = os.path.join(log_dir, f"debug_unfinished_{ts}.html")
                with open(html_path, "w", encoding="utf-8") as f:
                    f.write(self.driver.page_source)
                self.log(f"頁面 HTML 已存到: {html_path}")
            except Exception as e:
                self.log(f"存頁面 HTML 失敗: {e}")

            self.log("─── DEBUG dump 結束 ───")
        except Exception as e:
            self.log(f"DEBUG dump 失敗: {e}")

    def _dump_player_debug(self):
        """課程播放器找不到章節時，dump 主頁與所有 iframe 內 HTML"""
        try:
            self.log("─── 播放器 DEBUG dump 開始 ───")
            self.log(f"目前 URL: {self.driver.current_url}")
            self.log(f"頁面標題: {self.driver.title}")
            log_dir = os.path.join(_BASE_DIR, "log")
            os.makedirs(log_dir, exist_ok=True)
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")

            # 主頁 HTML
            try:
                main_path = os.path.join(log_dir, f"debug_player_main_{ts}.html")
                with open(main_path, "w", encoding="utf-8") as f:
                    f.write(self.driver.page_source)
                self.log(f"主頁 HTML 已存: {main_path}")
            except Exception as e:
                self.log(f"主頁 HTML 存檔失敗: {e}")

            # 主頁可見 <a>（前 40 筆）
            shown = 0
            for a in self.driver.find_elements(By.TAG_NAME, "a"):
                try:
                    if not a.is_displayed():
                        continue
                    href = (a.get_attribute("href") or "").strip()
                    onclick = (a.get_attribute("onclick") or "").strip()
                    text = (a.text or "").strip().replace("\n", " ")
                    if not (href or onclick or text):
                        continue
                    self.log(f"  [a] href={href[:60]!r}  onclick={onclick[:50]!r}  text={text[:30]!r}")
                    shown += 1
                    if shown >= 40:
                        self.log("  ... 已顯示 40 筆 <a>")
                        break
                except Exception:
                    continue

            # 主頁 input radio / li / label
            for sel in ["input[type='radio']", "input[type='checkbox']", "label",
                        "li[onclick]", "div[onclick]", "span[onclick]"]:
                try:
                    els = [e for e in self.driver.find_elements(By.CSS_SELECTOR, sel)
                           if e.is_displayed()]
                    self.log(f"  [{sel}] 可見 {len(els)} 個")
                    for e in els[:5]:
                        try:
                            text = (e.text or "").strip().replace("\n", " ")[:40]
                            cls = (e.get_attribute("class") or "")[:60]
                            on = (e.get_attribute("onclick") or "")[:60]
                            self.log(f"    └ class={cls!r} text={text!r} onclick={on!r}")
                        except Exception:
                            continue
                except Exception:
                    continue

            # 列出所有 frame/iframe 並 dump 內容
            iframes = self._all_frames()
            self.log(f"頁面有 {len(iframes)} 個 frame/iframe")
            for idx, iframe in enumerate(iframes):
                try:
                    src = iframe.get_attribute("src") or ""
                    name = iframe.get_attribute("name") or ""
                    self.log(f"  [iframe {idx}] name={name!r} src={src[:80]!r}")
                    try:
                        self.driver.switch_to.frame(iframe)
                        # iframe HTML
                        try:
                            ifr_path = os.path.join(log_dir, f"debug_player_iframe{idx}_{ts}.html")
                            with open(ifr_path, "w", encoding="utf-8") as f:
                                f.write(self.driver.page_source)
                            self.log(f"    iframe{idx} HTML 已存: {ifr_path}")
                        except Exception as e:
                            self.log(f"    iframe{idx} HTML 存檔失敗: {e}")
                        # iframe 內 <a> 前 30 筆
                        ishow = 0
                        for a in self.driver.find_elements(By.TAG_NAME, "a"):
                            try:
                                if not a.is_displayed():
                                    continue
                                href = (a.get_attribute("href") or "").strip()
                                onclick = (a.get_attribute("onclick") or "").strip()
                                text = (a.text or "").strip().replace("\n", " ")
                                if not (href or onclick or text):
                                    continue
                                self.log(f"    [iframe{idx} a] href={href[:50]!r}  "
                                         f"onclick={onclick[:50]!r}  text={text[:30]!r}")
                                ishow += 1
                                if ishow >= 30:
                                    self.log(f"    ... iframe{idx} 已顯示 30 筆 <a>")
                                    break
                            except Exception:
                                continue
                    finally:
                        self.driver.switch_to.default_content()
                except Exception as e:
                    self.log(f"  iframe {idx} dump 失敗: {e}")
                    self.driver.switch_to.default_content()

            self.log("─── 播放器 DEBUG dump 結束 ───")
        except Exception as e:
            self.log(f"播放器 DEBUG dump 失敗: {e}")
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass

    def _process_current_course_page(self):
        """處理目前所在的課程頁面（詳情頁 → 上課去 → 播放器 → 測驗 → 問卷）"""
        try:
            self._dismiss_page_popup()
            self._dismiss_popups()
            req_min = self._log_course_info()

            try:
                go_btn = WebDriverWait(self.driver, 8).until(EC.element_to_be_clickable(
                    (By.XPATH, "//*[normalize-space()='上課去' or "
                               "normalize-space()='繼續上課' or "
                               "normalize-space()='開始上課']")))
                go_btn.click()
                time.sleep(3)
                self.log("已點擊「上課去」")
                if len(self.driver.window_handles) > 1:
                    self._switch_to_course_window()
                self._dismiss_page_popup()
            except TimeoutException:
                self.log("找不到「上課去」按鈕，嘗試直接進行測驗/問卷...")
                # 試著直接做測驗（課程可能只剩測驗）
                self._auto_take_exam()
                self._auto_fill_player_survey()
                if not self.running:
                    return
                self.driver.get(DASHBOARD_URL)
                return

            # v1.8.23/24：badges(三態) + 分數 + 已上時數 主導 dispatch
            #   A. 時數短缺 → _learning_loop 累時數
            #   B. 測驗:已及格→跳;明確未過或 needs.exam=True→試;needs=None→保守試
            #   C. 問卷:needs.survey=True→試;明確 False 或 None→ 跳過
            needs   = self._current_needs
            score   = self._current_exam_score
            pass_   = self._current_exam_pass
            already = self._current_already_min
            nr      = needs.get("reading")
            ne      = needs.get("exam")
            ns      = needs.get("survey")
            score_passed = (score is not None and pass_ is not None and score >= pass_)
            score_failed = (score is not None and pass_ is not None and score <  pass_)

            # v1.8.24 P0-2 保險絲:時數短缺判斷三層退化
            if req_min and already is not None:
                time_short = (already < req_min)
            elif nr is True:
                time_short = True
            elif nr is False:
                time_short = False
            else:
                # 全無明確信號 — 有 req_min 就累兜底;否則跳過避免無謂上課
                time_short = bool(req_min)
                if time_short:
                    self.log("⚠ 已上時數+badges 信號全失效,但有 req_min → 退化為無條件累時數")
            self.log(f"📊 決策摘要 needs={needs} score={score} pass={pass_} "
                     f"already={already} req={req_min} 時數短缺={time_short} 已及格={score_passed}")

            # ── 階段 A：時數 ──
            if time_short:
                remaining = req_min - (already or 0)
                self.log(f"【A】時數短缺(已上 {(already or 0)*60:.0f} / 需 {req_min*60} 秒,剩 {remaining*60:.0f} 秒)→ 累積時數")
                self._learning_loop(required_minutes=req_min, already_minutes=(already or 0))
            else:
                self.log("【A】時數已達標(或無需閱讀),跳過上課階段")

            # ── 階段 B：測驗 ──
            if score_passed:
                self.log(f"【B】測驗已及格({score:g} ≥ {pass_:g}),跳過測驗")
            elif score_failed or ne is True or (ne is None and not score_passed):
                if score_failed:
                    self.log(f"【B】分數 {score:g} < 及格 {pass_:g} → 嘗試重測")
                elif ne is True:
                    self.log("【B】偵測到「未測驗」 → 嘗試測驗")
                else:
                    self.log("【B】無明確信號(needs/分數皆未知)→ 保守嘗試測驗")
                if self._try_jump_to_exam_sysbar():
                    self.log("⚡ 進入測驗模式")
                    self._auto_take_exam()
                else:
                    # v1.8.42:測驗被擋 → 補課重試(最多 3 精算+1×1800 兜底,永不放棄)
                    self.log("⚠ 測驗被擋 → 啟動補課重試(永不放棄本門)")
                    if self._recheck_and_supplement(req_min, self._try_jump_to_exam_sysbar, label="測驗"):
                        self.log("⚡ 進入測驗模式(補課後)")
                        self._auto_take_exam()
            else:
                self.log("【B】badges 明確不需測驗,跳過")

            # ── 階段 C：問卷 ──
            if ns is True:
                self.log("【C】偵測到「未問卷」 → 嘗試填寫")
                try:
                    if self._try_jump_to_survey_sysbar():
                        self.log("⚡ 進入問卷模式")
                        self._auto_fill_player_survey()
                    else:
                        # v1.8.42:問卷被擋(常因「請先閱讀達應閱讀時數」)→ 補課重試
                        self.log("⚠ 問卷被擋 → 啟動補課重試(永不放棄本門)")
                        if self._recheck_and_supplement(req_min, self._try_jump_to_survey_sysbar, label="問卷"):
                            self.log("⚡ 進入問卷模式(補課後)")
                            self._auto_fill_player_survey()
                except Exception as _e:
                    self.log(f"問卷處理錯誤: {_e}")
            elif ns is None:
                # 沒明確信號 — 保守試一次(原 v1.8.22 行為)
                self.log("【C】無明確 badges 信號 → 保守嘗試問卷")
                try:
                    if self._try_jump_to_survey_sysbar():
                        self.log("⚡ 進入問卷模式")
                        self._auto_fill_player_survey()
                    else:
                        self.log("⚠ 無法進入問卷頁,跳過")
                except Exception as _e:
                    self.log(f"問卷處理錯誤: {_e}")
            else:
                self.log("【C】badges 明確不需問卷,跳過")

            if len(self.driver.window_handles) > 1:
                self.driver.close()
                self.driver.switch_to.window(self.driver.window_handles[0])
        except Exception as e:
            self.log(f"處理課程頁面錯誤: {e}")
            try:
                if len(self.driver.window_handles) > 1:
                    self.driver.switch_to.window(self.driver.window_handles[0])
                self.driver.get(DASHBOARD_URL)
            except Exception:
                pass

    def _extract_card_info(self, el):
        """從連結元素向上找卡片容器，回傳 (title, needs_log, exam_score, exam_pass, had_steps)
        v1.8.23：加抓「測驗分數:X 分」與「及格分數:Y 分」(每課不同) 為權威信號之一
        v1.8.24：had_steps=True 才能信任 needs 的 False 為「明確不需要」(否則三個都 done 跟沒抓到難分)
        """
        title, needs_log = "", ""
        exam_score, exam_pass = None, None
        had_steps = False
        try:
            # 優先抓 e等公務園 的 course-list-block
            try:
                card = el.find_element(By.XPATH,
                    "./ancestor::div[contains(@class,'course-list-block')][1]")
            except Exception:
                card = el.find_element(By.XPATH,
                    "./ancestor::div[contains(@class,'course') or "
                    "contains(@class,'card') or contains(@class,'item') or "
                    "contains(@class,'box')][1]")
            # 標題：優先 cb-info-name1（含 title 屬性最準）→ 再 fallback 通用 selector
            for ts in [".//div[contains(@class,'cb-info-name1')]",
                       ".//div[contains(@class,'course-list-block-info-name')]",
                       ".//h3", ".//h4",
                       ".//p[contains(@class,'title')]",
                       ".//span[contains(@class,'title')]",
                       ".//div[contains(@class,'title')]",
                       ".//strong", ".//b"]:
                try:
                    elt = card.find_element(By.XPATH, ts)
                    t = (elt.get_attribute("title") or elt.text or "").strip()
                    if t and len(t) > 3 and t != "開放式課程":
                        title = t
                        break
                except Exception:
                    pass
            ct = card.text
            badges = []
            # 觀察各 step 是否完成（done class 表已完成）
            try:
                steps = card.find_elements(By.CSS_SELECTOR, ".course-steps-bar .step")
                if steps:
                    had_steps = True   # v1.8.24：抓到 step → needs 的 False 才可信
                for s in steps:
                    label = ""
                    try:
                        label = s.find_element(By.CSS_SELECTOR, ".label").text.strip()
                    except Exception:
                        label = s.text.strip()
                    cls = s.get_attribute("class") or ""
                    if label and "done" not in cls:
                        badges.append(f"未{label}")
            except Exception:
                pass
            if not badges and not had_steps:
                # v1.8.24：只在「真的沒抓到 step」時才用 fallback 字串(避免污染權威信號)
                if "閱讀時數" in ct:
                    badges.append("閱讀")
                if "測驗" in ct:
                    badges.append("測驗")
                if "問卷" in ct:
                    badges.append("問卷")
            needs_log = "/".join(badges)
            # v1.8.23/24：抓「測驗分數」與「及格分數」 — 取最後一筆(避免歷史紀錄誤導)
            try:
                ms = re.findall(r'測驗分數\s*[:：]\s*(\d+(?:\.\d+)?)\s*分', ct)
                if ms:
                    exam_score = float(ms[-1])
            except Exception:
                pass
            try:
                ms = re.findall(r'(?:及格分數|合格分數|通過分數|最低分數|及格門檻|合格門檻)'
                                r'\s*[:：]\s*(\d+(?:\.\d+)?)\s*分', ct)
                if ms:
                    exam_pass = float(ms[-1])
            except Exception:
                pass
        except Exception:
            pass
        return title, needs_log, exam_score, exam_pass, had_steps

    def _click_next_page(self):
        """點下一頁按鈕，回傳 True=成功翻頁 / False=已是最後頁"""
        try:
            candidates = self.driver.find_elements(By.XPATH,
                "//a[contains(@class,'next') and not(contains(@class,'disabled'))]"
                " | //li[contains(@class,'next') and not(contains(@class,'disabled'))]/a"
                " | //a[@title='下一頁']"
                " | //a[normalize-space()='>' or normalize-space()='›'"
                "    or normalize-space()='下一頁']")
            for el in candidates:
                if not el.is_displayed():
                    continue
                parent_cls = ""
                try:
                    parent_cls = el.find_element(By.XPATH, "..").get_attribute("class") or ""
                except Exception:
                    pass
                cls = (el.get_attribute("class") or "") + parent_cls
                if "disabled" in cls or "inactive" in cls:
                    continue
                self.driver.execute_script("arguments[0].click()", el)
                return True
        except Exception:
            pass
        return False

    def _log_course_info(self):
        """印出課程時數資訊與相關權威信號，回傳需要上課的分鐘數（50% 門檻），0 代表未知。
        v1.8.23：多行 dump 詳情頁所有時數/分數/及格相關行；嘗試解析「已上時數」存到
                 self._current_already_min；補抓 exam_score/exam_pass（卡片若沒抓到時）。
        """
        req = 0
        try:
            body = self.driver.find_element(By.TAG_NAME, "body").text
            # v1.8.40:visible body.text 不含 hidden tab(認證時數通常 hidden) →
            # 用 textContent 抓全部(含 hidden)讓 regex 找得到「通過條件」門檻字串
            try:
                body_full = self.driver.execute_script(
                    "return document.body && document.body.textContent || '';"
                ) or body
            except Exception:
                body_full = body

            # v1.8.23：多行 dump（給階段 2 收斂 selector 用）
            KEYS = ("分鐘", "小時", "時數", "分數", "及格", "合格", "通過",
                    "閱讀", "上課", "認證", "認定", "滿分", "門檻")
            seen = set()
            for raw in body.split("\n"):
                line = raw.strip()
                if not line or line in seen or len(line) > 80:
                    continue
                if any(k in line for k in KEYS):
                    self.log(f"📋 {line}")
                    seen.add(line)

            # v1.8.39/40:時數門檻優先抓「通過條件」中的「閱讀時數:HH:MM:SS(含)以上」(真實門檻)
            #          v1.8.40:用 body_full(textContent) 因為認證時數 tab 可能 hidden
            #          fallback 才用「總時數 50%」(以前的錯誤推估)
            req_from_pass = None
            m_pass = re.search(r'閱讀時數\s*[:：]?\s*(\d+):(\d+):(\d+)\s*[(（][^)）]*[)）]\s*以上', body_full)
            if m_pass:
                h, mi, s = int(m_pass.group(1)), int(m_pass.group(2)), int(m_pass.group(3))
                req_from_pass = int(h * 60 + mi + s / 60.0)
            if req_from_pass:
                req = req_from_pass
                self.log(f"時數門檻：通過條件規定至少 {req*60} 秒(權威來源)")
            else:
                # fallback 50% 推估
                m = re.search(r'(\d+(?:\.\d+)?)\s*小時', body_full)
                if m:
                    req = int(float(m.group(1)) * 60 * 0.5)
                else:
                    m2 = re.search(r'(\d+)\s*分鐘', body_full)
                    if m2:
                        req = int(int(m2.group(1)) * 0.5)
                if req:
                    self.log(f"時數門檻：需上課至少 {req*60} 秒（總時數 50%,推估值）")

            # v1.8.25/39:抓「已上時數」 — 排除「(含)以上」(那是門檻不是已上)
            already = None
            for m_hms in re.finditer(r'閱讀時數\s*[:：]\s*(\d+):(\d+):(\d+)([^\n]{0,15})', body_full):
                rest = m_hms.group(4) or ""
                if "以上" in rest:
                    continue   # 這是門檻字串,跳過
                h, mi, s = int(m_hms.group(1)), int(m_hms.group(2)), int(m_hms.group(3))
                already = h * 60 + mi + s / 60.0
                break
            if already is None:
                for pat in (
                    r'(?:已上|目前|累計|本次|現有)'
                    r'\s*(?:閱讀|上課|學習|課程)?\s*時數\s*[:：]?\s*(\d+(?:\.\d+)?)\s*分',
                    r'(?:已上|目前|累計|本次)\s*(\d+(?:\.\d+)?)\s*分',
                ):
                    m3 = re.search(pat, body_full)
                    if m3:
                        already = float(m3.group(1))
                        break
            if already is not None:
                self.log(f"✓ 已上時數：{already*60:.0f} 秒")
                self._current_already_min = already

            # v1.8.24：詳情頁補抓分數/及格門檻 — 用 findall 取最後一筆(避免歷史紀錄)
            if self._current_exam_score is None:
                ms = re.findall(r'測驗分數\s*[:：]\s*(\d+(?:\.\d+)?)\s*分', body_full)
                if ms:
                    self._current_exam_score = float(ms[-1])
            if self._current_exam_pass is None:
                ms = re.findall(r'(?:及格分數|合格分數|通過分數|最低分數|及格門檻|合格門檻|課程測驗)'
                                r'\s*[:：]?\s*(\d+(?:\.\d+)?)\s*分', body_full)
                if ms:
                    self._current_exam_pass = float(ms[-1])
        except Exception:
            pass
        return req

    def _check_course_complete(self):
        try:
            body = self.driver.find_element(By.TAG_NAME, "body").text
            if "已達上課時數" in body or "可以填寫問卷" in body:
                return True
            for sel in ["a[href*='survey']", "a[href*='evaluate']", ".survey_btn"]:
                try:
                    el = self.driver.find_element(By.CSS_SELECTOR, sel)
                    if el.is_displayed():
                        return True
                except NoSuchElementException:
                    pass
        except Exception:
            pass
        return False

    def _auto_fill_survey_form(self):
        try:
            time.sleep(2)
            radios = self.driver.find_elements(By.CSS_SELECTOR,
                "input[type='radio'][value='5'], input[type='radio'][value='4']")
            clicked = set()
            for r in radios:
                name = r.get_attribute("name")
                if name and name not in clicked:
                    self.driver.execute_script("arguments[0].click()", r)
                    clicked.add(name)
            time.sleep(1)
            for sel in ["button[type='submit']", "input[type='submit']", ".submit_btn"]:
                try:
                    btn = self.driver.find_element(By.CSS_SELECTOR, sel)
                    if btn.is_displayed():
                        btn.click()
                        time.sleep(3)
                        try:
                            self.driver.switch_to.alert.accept()
                        except Exception:
                            pass
                        return
                except NoSuchElementException:
                    pass
        except Exception:
            pass

    def _dismiss_player_popup(self):
        """關閉播放器內每30分鐘的驗證彈窗（未按確定會被登出）
           v1.8.17：跨 frame 偵測 + 橘色按鈕特徵 fallback
           v1.8.19：擴充元素 filter（含 div/span/li 帶 onclick/role），新增 JS-based 最終 fallback"""
        # 1. JS alert（最高優先）
        try:
            alert = self.driver.switch_to.alert
            self.log(f"關閉驗證彈窗(alert): {alert.text[:40]}")
            alert.accept()
            return True
        except Exception:
            pass

        long_phrases = ["繼續上課", "繼續學習", "仍在上課", "確認在線", "繼續觀看",
                        "我還在學習", "我還在", "繼續上課程"]
        exact_words  = ["繼續", "確認", "確定", "我在", "OK"]
        bad_words    = ["取消", "離開", "關閉", "回上一頁", "結束"]
        # v1.8.19：擴充 — 連 div/span/li/td 帶 onclick/role/class=btn 也算可點
        elem_filter = ("(self::button or self::a or self::input[@type='button'] "
                       "or self::input[@type='submit'] "
                       "or ((self::div or self::span or self::li or self::td or self::p) "
                       "and (@onclick or @role='button' or contains(@class,'btn') "
                       "or contains(@class,'button') or contains(@class,'click')))"
                       ")")

        def _try_click_in_current(xpath, label):
            try:
                btns = self.driver.find_elements(By.XPATH, xpath)
                for btn in btns:
                    try:
                        if not btn.is_displayed():
                            continue
                        text_norm = (btn.text or btn.get_attribute("value") or "").strip()
                        if any(bw in text_norm for bw in bad_words):
                            continue
                        self.driver.execute_script("arguments[0].click()", btn)
                        self.log(f"已回應驗證彈窗：{label} (按鈕文字：{text_norm[:20]})")
                        return True
                    except Exception:
                        continue
            except Exception:
                pass
            return False

        def _try_orange_button():
            """v1.8.17：抓橘色／黃色背景的可點按鈕（30 分鐘確認鈕通常是橘色）"""
            xp = ("//*[" + elem_filter + " and ("
                  "contains(@style,'orange') or contains(@style,'#F90') "
                  "or contains(@style,'#f90') or contains(@style,'#FF9') "
                  "or contains(@style,'#ff9') or contains(@style,'rgb(255') "
                  "or contains(@class,'orange') or contains(@class,'btn-warning') "
                  "or contains(@class,'btn_orange') or contains(@class,'btnContinue'))]")
            try:
                btns = self.driver.find_elements(By.XPATH, xp)
                for btn in btns:
                    try:
                        if not btn.is_displayed():
                            continue
                        text_norm = (btn.text or btn.get_attribute("value") or "").strip()
                        if any(bw in text_norm for bw in bad_words):
                            continue
                        # 額外驗證：橘色按鈕通常文字短且包含「繼續/確認/我」
                        if not text_norm or len(text_norm) > 30:
                            continue
                        if any(kw in text_norm for kw in ("繼續", "確認", "確定", "我", "OK", "I")):
                            self.driver.execute_script("arguments[0].click()", btn)
                            self.log(f"已回應驗證彈窗(橘色按鈕): {text_norm[:20]}")
                            return True
                    except Exception:
                        continue
            except Exception:
                pass
            return False

        def _scan_one_context():
            """在當前 frame context 中嘗試所有方法"""
            for text in long_phrases:
                if _try_click_in_current(
                    f"//*[contains(normalize-space(),'{text}') and {elem_filter}]", text):
                    return True
            for text in exact_words:
                if _try_click_in_current(
                    f"//*[normalize-space()='{text}' and {elem_filter}]", text):
                    return True
            if _try_orange_button():
                return True
            return False

        # 先在 default content 找
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        if _scan_one_context():
            return True

        # v1.8.20：優先掃 s_dialog 這種「對話框 iframe」（hrd.gov.tw e 學習用）
        priority_frame_names = ["s_dialog", "co_dialog", "dialog", "popup", "confirm"]
        try:
            self.driver.switch_to.default_content()
            all_iframes = (self.driver.find_elements(By.TAG_NAME, "iframe") +
                           self.driver.find_elements(By.TAG_NAME, "frame"))
            for fr in all_iframes:
                try:
                    name = (fr.get_attribute("name") or "").lower()
                    src  = (fr.get_attribute("src")  or "").lower()
                    if any(p in name or p in src for p in priority_frame_names):
                        self.driver.switch_to.default_content()
                        self.driver.switch_to.frame(fr)
                        # v1.8.25：找到 frame 不等於有彈窗,只在實際關彈窗時才 log
                        if _scan_one_context():
                            self.log(f"✓ 已關彈窗(對話框 frame: name={name})")
                            return True
                except Exception:
                    continue
            self.driver.switch_to.default_content()
        except Exception:
            try: self.driver.switch_to.default_content()
            except Exception: pass

        # v1.8.20：遞迴掃所有 frame（不限深度）
        def _recursive_scan(depth=0, max_depth=4):
            if depth > max_depth:
                return False
            if _scan_one_context():
                return True
            try:
                inners = self._all_frames()
            except Exception:
                return False
            for inner in inners:
                try:
                    self.driver.switch_to.frame(inner)
                except Exception:
                    continue
                try:
                    if _recursive_scan(depth + 1, max_depth):
                        return True
                finally:
                    try: self.driver.switch_to.parent_frame()
                    except Exception: pass
            return False

        try:
            self.driver.switch_to.default_content()
            if _recursive_scan():
                return True
        except Exception:
            pass

        # v1.8.19：最終 JS fallback — 暴力掃描所有 frame 內可見的「繼續/確認」文字節點
        # 從文字節點往上找最近的可點祖先（onclick/role/btn/a/button），點下去
        js_fallback = r"""
        (function() {
          var keywords = ['繼續上課', '繼續學習', '繼續上課程', '仍在上課',
                          '我還在學習', '確認在線', '繼續觀看', '繼續'];
          var bad = ['取消', '離開', '結束', '關閉', '回上一頁'];
          function isVisible(el) {
            if (!el || !el.getBoundingClientRect) return false;
            var r = el.getBoundingClientRect();
            if (r.width < 1 || r.height < 1) return false;
            var st = window.getComputedStyle(el);
            return st && st.visibility !== 'hidden' && st.display !== 'none' && st.opacity !== '0';
          }
          function findClickableAncestor(el) {
            var cur = el, depth = 0;
            while (cur && depth < 8) {
              var tag = (cur.tagName || '').toLowerCase();
              if (tag === 'button' || tag === 'a') return cur;
              if (cur.onclick || (cur.getAttribute && (cur.getAttribute('onclick') || cur.getAttribute('role') === 'button'))) return cur;
              var cls = (cur.className && cur.className.toString && cur.className.toString()) || '';
              if (/\b(btn|button|click)\b/i.test(cls)) return cur;
              cur = cur.parentElement; depth++;
            }
            return null;
          }
          var all = document.body ? document.body.querySelectorAll('*') : [];
          for (var i = 0; i < all.length; i++) {
            var el = all[i];
            if (el.children && el.children.length > 0) continue;  // 只看葉子節點
            var t = (el.innerText || el.textContent || '').replace(/\s+/g, '');
            if (!t || t.length > 30) continue;
            var matched = null;
            for (var k = 0; k < keywords.length; k++) {
              if (t.indexOf(keywords[k]) >= 0) { matched = keywords[k]; break; }
            }
            if (!matched) continue;
            if (bad.some(function(b) { return t.indexOf(b) >= 0; })) continue;
            if (!isVisible(el)) continue;
            var target = findClickableAncestor(el) || el;
            try {
              target.click();
              return matched + '|' + (target.tagName || '?') + '|' + (target.className || '');
            } catch(e) {}
          }
          return null;
        })();
        """
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        try:
            res = self.driver.execute_script(js_fallback)
            if res:
                self.log(f"已回應驗證彈窗(JS fallback): {res[:80]}")
                return True
            # 跨 frame JS 掃描
            for frame in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(frame)
                    res = self.driver.execute_script(js_fallback)
                    if res:
                        self.log(f"已回應驗證彈窗(JS fallback,frame): {res[:80]}")
                        return True
                    for inner in self._all_frames():
                        try:
                            self.driver.switch_to.frame(inner)
                            res = self.driver.execute_script(js_fallback)
                            if res:
                                self.log(f"已回應驗證彈窗(JS fallback,inner): {res[:80]}")
                                return True
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            continue
                except Exception:
                    continue
                finally:
                    try: self.driver.switch_to.default_content()
                    except Exception: pass
        except Exception:
            pass
        try: self.driver.switch_to.default_content()
        except Exception: pass
        return False

    def _idle_dialog_visible(self):
        """v1.8.22：偵測是否仍有「閱讀閒置提醒」對話框（已被 _dismiss_player_popup 嘗試後仍在）
        辨識特徵：頁面或任一 frame 內可見文字含關鍵字。
        """
        js = r"""
        (function() {
          var KEYS = ['閱讀閒置提醒', '閱讀閒置', '秒後自動登出', '請點選'];
          function bodyText(){
            try { return (document.body && document.body.innerText) || ''; } catch(e){ return ''; }
          }
          var t = bodyText();
          for(var i=0; i<KEYS.length; i++){
            if(t.indexOf(KEYS[i]) >= 0) return KEYS[i];
          }
          return null;
        })();
        """
        try:
            self.driver.switch_to.default_content()
        except Exception:
            return False
        try:
            if self.driver.execute_script(js):
                return True
            for frame in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(frame)
                    if self.driver.execute_script(js):
                        return True
                    for inner in self._all_frames():
                        try:
                            self.driver.switch_to.frame(inner)
                            if self.driver.execute_script(js):
                                return True
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            try: self.driver.switch_to.parent_frame()
                            except Exception: pass
                except Exception:
                    pass
        except Exception:
            pass
        finally:
            try: self.driver.switch_to.default_content()
            except Exception: pass
        return False

    def _try_jump_to_lesson_sysbar(self):
        """v1.8.16：點左側「開始上課」回到上課播放器（修「測驗/問卷後沒回上課」）"""
        return self._try_jump_to_sysbar_link(
            ["開始上課", "lesson", "play"], "開始上課")

    def _recheck_and_supplement(self, req_min, retry_jump_fn, label="測驗"):
        """v1.8.42:測驗/問卷被擋時補課重試,**永不放棄本門課**。

        最多 4 輪:前 3 輪精算補課秒數,第 4 輪 1800 秒兜底。
        每輪流程:切回上課頁 → 重抓站方時數 → 算補課秒數 → 跑 _learning_loop → 重試跳測驗/問卷。

        補課秒數三層判斷(由準到粗):
          1. 抓到站方 already → max(60, (req - already) × 60)
          2. 抓不到但有 _current_already_min + req_min → max(60, (req - 已知) × 60 + 60 安全)
          3. 完全無法判斷 / 第 4 輪兜底 → 1800 秒

        retry_jump_fn:傳 self._try_jump_to_exam_sysbar 或 self._try_jump_to_survey_sysbar
        回傳 True=最終跳成,False=4 輪皆失敗(本門記為跑失敗,但外層流程繼續)
        """
        MAX_RETRY = 4
        FALLBACK_SEC = 1800

        for attempt in range(MAX_RETRY):
            tag = f"第 {attempt+1}/{MAX_RETRY} 輪"
            # 切回上課頁
            try:
                if not self._try_jump_to_lesson_sysbar():
                    self.log(f"⚠ {tag} 切回上課頁失敗,跳過本輪")
                    continue
            except Exception as e:
                self.log(f"⚠ {tag} 切回上課頁錯誤: {e}")
                continue
            self._human_sleep(2.0, 0.5)

            # 計算補課秒數
            new_already = self._extract_already_from_current()
            sup_sec = None
            if new_already is not None:
                self._current_already_min = new_already
                if req_min and new_already >= req_min:
                    self.log(f"✓ {tag} 站方時數已達標({new_already*60:.0f}/{req_min*60:.0f} 秒) → 直接重試 {label}")
                    if retry_jump_fn():
                        self.log(f"⚡ {tag} {label} 跳成功(站方已達標)")
                        return True
                    self.log(f"⚠ {tag} 站方達標但 {label} 仍被擋(DOM 未同步?)→ 進下一輪")
                    continue
                if req_min:
                    sup_sec = max(60, int((req_min - new_already) * 60))
                    self.log(f"📋 {tag} 站方 {new_already*60:.0f}/{req_min*60:.0f} 秒,補 {sup_sec} 秒")
            if sup_sec is None and req_min and self._current_already_min is not None:
                sup_sec = max(60, int((req_min - self._current_already_min) * 60 + 60))
                self.log(f"⚠ {tag} 站方時數抓不到,以已知 {self._current_already_min*60:.0f} 秒+60 安全係數 → 補 {sup_sec} 秒")
            # 完全無法判斷 OR 已是最後一輪 → 1800 秒兜底
            if sup_sec is None or attempt == MAX_RETRY - 1:
                if sup_sec is None:
                    self.log(f"🛟 {tag} 完全無法判斷還要上多久 → 1800 秒兜底再試 {label}")
                else:
                    self.log(f"🛟 {tag} 已用完 3 次精算補課,改 1800 秒兜底再試 {label}")
                sup_sec = FALLBACK_SEC

            # 補課:呼 _learning_loop,fake required = current + sup_min
            sup_min = max(1, int(round(sup_sec / 60.0)))
            cur = self._current_already_min or 0
            fake_required = cur + sup_min
            self._learning_loop(required_minutes=fake_required, already_minutes=cur)

            # 補完試跳測驗/問卷
            if retry_jump_fn():
                self.log(f"⚡ {tag} 補課後 {label} 跳成功")
                return True
            self.log(f"⚠ {tag} 補課後 {label} 仍被擋")

        self.log(f"⚠ {label} 重試 {MAX_RETRY} 輪皆失敗,本門當作跑失敗(流程繼續下一門)")
        return False

    def _learning_loop(self, required_minutes=0, already_minutes=0):
        """v1.8.23：accept already_minutes 起點，目標 = max(0, required - already)。
        若 already 已達/超過 required，立即返回不再上課。
        """
        target_min = max(0, required_minutes - already_minutes)
        if required_minutes and target_min == 0:
            self.log(f"✓ 時數已達標(已上 {already_minutes*60:.0f} ≥ 需 {required_minutes*60:.0f} 秒)，跳過上課階段")
            return
        # v1.8.25/26/27:每門課第一次找到章節時 dump 標題,後續 cycle 不再 dump
        # v1.8.27:dump 邏輯移到 _find_chapters 內(在 frame context 抓 outerHTML 避免 stale)
        self._chapter_found_logged = False
        self._chapter_selectors_probed = False  # v1.8.28:每門課首次探測所有 selector(診斷用)
        self._pathtree_log_done = False         # v1.8.29:pathtree.nextStep 成功 log 只印一次
        # v1.8.16：進 loop 前先確保在上課頁面（不在的話 _find_chapters 會空轉）
        try:
            if self._try_jump_to_lesson_sysbar():
                self.log("✓ 已切回「開始上課」")
                self._human_sleep(2.0, 0.5)
        except Exception:
            pass
        self.log(f"開始上課！請專心聽講......(目標再上 {target_min*60:.0f} 秒)")
        check_every = 10   # 每 10 次循環做一次時數確認（內部固定值）
        local_cycle = 0
        no_chapter_count = 0
        start_time = time.time()
        # v1.8.30:頁面停留控制 — 偵測影片時長,沒影片 default 30 分鐘
        last_advance_at = None
        current_page_dur = 30.0   # v1.8.33:沒影片時 30 秒(快速推進文字頁;之前 30 分鐘卡死)
        self._video_duration_logged = False
        self._video_default_logged = False
        # v1.8.31:每 30 秒印一次精準狀態,取代每 cycle「第N次」噪訊
        last_status_at = 0.0
        # v1.8.22：「閱讀閒置提醒」對話框首次偵測時間戳
        idle_dlg_first_seen = None
        IDLE_DLG_TIMEOUT = 270  # 秒；站方倒數 297 秒，留 27 秒緩衝主動跳考避險
        # v1.8.36/37:站方時數權威 + _can_take_exam_now() 兜底
        # - 5 分鐘抓「閱讀時數」對比 req_min;抓到 → 信任站方
        # - 抓不到才 fallback:30 分鐘嘗試 _can_take_exam_now() 偵測測驗鈕(v1.8.20 原邏輯)
        last_already_check = time.time()
        last_exam_check = time.time()
        ALREADY_CHECK_INTERVAL = 5 * 60   # 秒
        EXAM_CHECK_INTERVAL = 30 * 60     # 秒
        already_ever_detected = False
        # v1.8.43:wall-time 達 target 時改成「強制驗證站方時數」,只有抓不到才用 60 秒緩衝兜底
        fallback_buffer_added = False

        while self.running:
            # ── 每次循環優先處理驗證彈窗（30分鐘一次，不處理會被登出）──
            self._dismiss_player_popup()

            # v1.8.22：URL 變化監控 — 站方可能因 idle 自動把頁面轉到測驗頁，
            # 偵測到後立即退出 learning_loop，外層會接 _auto_take_exam()
            try:
                cur_url = (self.driver.current_url or "")
            except Exception:
                cur_url = ""
            if "/learn/exam_" in cur_url or "/exam/" in cur_url:
                self.log(f"⚡ URL 已變到測驗頁（{cur_url[:60]}）→ 退出 learning_loop")
                return

            # v1.8.22：偵測「閱讀閒置提醒」對話框（_dismiss_player_popup 嘗試後仍在）
            if self._idle_dialog_visible():
                if idle_dlg_first_seen is None:
                    idle_dlg_first_seen = time.time()
                    self.log("⚠ 偵測到「閱讀閒置提醒」對話框，找不到「確定」按鈕；270 秒後將主動跳測驗頁")
                elapsed_idle = time.time() - idle_dlg_first_seen
                if elapsed_idle >= IDLE_DLG_TIMEOUT:
                    self.log(f"⏰ 閒置對話框已持續 {elapsed_idle:.0f}s 仍無法關閉 → 主動跳測驗頁避險")
                    if self._try_jump_to_exam_sysbar():
                        self.log("✓ 主動跳測驗頁成功 → 退出 learning_loop")
                        return
                    self.log("⚠ 主動跳測驗失敗，重置倒數再試一輪")
                    idle_dlg_first_seen = None
            else:
                idle_dlg_first_seen = None

            # v1.8.36:每 5 分鐘從當前頁面重抓「閱讀時數」對比 req_min(站方權威)
            if time.time() - last_already_check >= ALREADY_CHECK_INTERVAL:
                last_already_check = time.time()
                new_already = self._extract_already_from_current()
                if new_already is not None:
                    already_ever_detected = True
                    if new_already > already_minutes:
                        delta = new_already - already_minutes
                        self.log(f"📋 站方時數更新:{already_minutes*60:.0f} → {new_already*60:.0f} 秒(漲 {delta*60:.0f})")
                        already_minutes = new_already
                        target_min = max(0, required_minutes - already_minutes)
                        if target_min == 0:
                            self.log(f"✓ 站方時數已達標({already_minutes*60:.0f} ≥ {required_minutes*60:.0f} 秒),退出去測驗")
                            return

            # v1.8.37:fallback — 站方時數抓不到時,每 30 分鐘嘗試 _can_take_exam_now()
            if (not already_ever_detected and
                    time.time() - last_exam_check >= EXAM_CHECK_INTERVAL):
                last_exam_check = time.time()
                if self._can_take_exam_now():
                    elapsed_sec = time.time() - start_time
                    self.log(f"⚡ 上課 {elapsed_sec:.0f} 秒後偵測到「進行測驗」可點(站方時數抓不到時的 fallback)")
                    return

            # ── 時數門檻:wall time 達 target 時強制驗證站方時數(v1.8.43) ──
            # 站方達標→退出;站方仍短缺→缺額×1.5 加碼繼續上;抓不到→+60 秒緩衝兜底退
            if target_min > 0:
                elapsed_min = (time.time() - start_time) / 60
                if elapsed_min >= target_min:
                    verified = self._extract_already_from_current()
                    if verified is not None:
                        already_ever_detected = True
                        already_minutes = verified
                        if required_minutes and verified >= required_minutes:
                            self.log(f"✓ 本機 {elapsed_min*60:.0f} 秒達 target,站方確認 {verified*60:.0f}/{required_minutes*60:.0f} 秒,切換測驗/問卷")
                            return
                        # 站方仍短缺 → 缺額 × 1.5 加碼繼續上
                        new_remain_min = max(0.0, (required_minutes or 0) - verified)
                        extra_min = max(0.5, new_remain_min * 1.5)
                        target_min = elapsed_min + extra_min
                        self.log(f"⚠ 本機達 target 但站方僅 {verified*60:.0f}/{(required_minutes or 0)*60:.0f} 秒,缺 {new_remain_min*60:.0f} 秒 → 加碼上 {extra_min*60:.0f} 秒")
                    elif not fallback_buffer_added:
                        # 站方時數抓不到 → 加 60 秒緩衝後再退(僅一次,避免無窮迴圈)
                        target_min = elapsed_min + 1
                        fallback_buffer_added = True
                        self.log(f"⚠ 本機達 target 但站方時數抓不到,加 60 秒緩衝再退")
                    else:
                        self.log(f"已上 {elapsed_min*60:.0f} 秒,站方驗證持續失敗(緩衝已用),切換測驗/問卷")
                        return

            # v1.8.29/30:優先試 pathtree.nextStep(1),依當前頁面影片時長控制推進頻率
            #          (避免切換太快 — v1.8.29 每 cycle 推一次,11 章節 30 秒推完)
            now_t = time.time()
            should_advance = (last_advance_at is None) or \
                             ((now_t - last_advance_at) >= current_page_dur)
            if not should_advance:
                # 還沒到該頁停留時間 → 不推進,讓外層 cycle 繼續做彈窗/URL/idle/30分鐘測驗檢查
                pass
            elif self._try_pathtree_advance():
                last_advance_at = time.time()
                no_chapter_count = 0
                # 偵測新頁影片時長,沒有就用 30 分 default
                d = self._detect_video_duration()
                if d and d > 0:
                    current_page_dur = float(d)
                    if not self._video_duration_logged:
                        self._video_duration_logged = True
                        self.log(f"⏰ 偵測到影片時長 {d:.0f} 秒,此頁停留(後續沉默)")
                else:
                    current_page_dur = 30.0
                    if not self._video_default_logged:
                        self._video_default_logged = True
                        self.log("⚠ 偵測不到影片,此頁停留 30 秒(快速推進)— 後續沉默")
            else:
                # pathtree 不可用 → 退化點 SCO 章節元素(其他平台)
                chapters = self._find_chapters()
                if chapters:
                    # v1.8.27:章節 dump 已在 _find_chapters 內完成(frame context 還在,outerHTML 不會 stale)
                    no_chapter_count = 0
                    for ch in chapters:
                        if not self.running:
                            return
                        try:
                            self.driver.execute_script("arguments[0].click()", ch)
                            time.sleep(0.5)
                        except (StaleElementReferenceException, WebDriverException):
                            break
                    last_advance_at = time.time()
                    current_page_dur = 30.0
                else:
                    no_chapter_count += 1
                if no_chapter_count <= 3:
                    self.log("找不到課程章節，等待中...")
                    time.sleep(10)
                    continue
                elif no_chapter_count == 4:
                    # v1.8.22：章節耗盡 → dump 後立刻嘗試跳測驗（不必空轉等 idle dialog）
                    self.log("⚠ 連續 3 次找不到章節，dump player HTML...")
                    self._dump_player_debug()
                    self.log("章節耗盡，主動嘗試跳測驗頁...")
                    if self._try_jump_to_exam_sysbar():
                        self.log("⚡ 章節耗盡跳測驗成功 → 退出 learning_loop")
                        return
                    self.log("跳測驗失敗，停留在課程頁面（等待時數累積）...")
                    time.sleep(60)
                else:
                    self.log("停留在課程頁面（等待時數累積）...")
                    time.sleep(60)

            local_cycle += 1
            self.cycle_count += 1
            self._set_status(f"上課中... 第 {self.cycle_count} 次循環")

            # v1.8.31/33-38:每 30 秒印一次精準狀態,單位統一用「秒」(避免分/秒混用混淆)
            now_t2 = time.time()
            if (now_t2 - last_status_at) >= 30:
                last_status_at = now_t2
                elapsed_sec = now_t2 - start_time
                target_sec = target_min * 60
                target_remain_sec = max(0, target_sec - elapsed_sec)
                if last_advance_at:
                    page_remain_sec = max(0, current_page_dur - (now_t2 - last_advance_at))
                    if target_remain_sec <= page_remain_sec:
                        self.log(f"⏳ 已上 {elapsed_sec:.0f}/{target_sec:.0f} 秒,目標達標剩 {target_remain_sec:.0f} 秒")
                    else:
                        self.log(f"⏳ 已上 {elapsed_sec:.0f}/{target_sec:.0f} 秒,換頁剩 {page_remain_sec:.0f} 秒")
                else:
                    self.log(f"⏳ 已上 {elapsed_sec:.0f}/{target_sec:.0f} 秒,等待首次推進...")

            if local_cycle % check_every == 0:
                in_player = "elearn.hrd.gov.tw" in self.driver.current_url
                if not in_player:
                    try:
                        self.driver.refresh()
                        time.sleep(5)
                        self._dismiss_page_popup()
                    except Exception:
                        pass
                if self._check_course_complete():
                    self.log("該課已達上課時數")
                    return

            # v1.8.24：移除 50 cycle 硬限制(實測 50 cycle ≈ 2 分鐘,完全不夠 req_min);
            #          target_min 主導退出條件;90 分鐘超時兜底防無限循環
            if (time.time() - start_time) >= 90 * 60:
                elapsed_min = (time.time() - start_time) / 60
                self.log(f"⏰ _learning_loop 已跑 {elapsed_min:.0f} 分 ≥ 90 分硬上限,退出兜底")
                return

    def _all_frames(self):
        """回傳本頁所有 frame/iframe 元素（不遞迴；要遞迴自己再 switch）"""
        frames = []
        try:
            frames.extend(self.driver.find_elements(By.TAG_NAME, "frame"))
        except Exception:
            pass
        try:
            frames.extend(self.driver.find_elements(By.TAG_NAME, "iframe"))
        except Exception:
            pass
        return frames

    def _switch_to_course_window(self):
        """v1.8.32:切換到課程 domain 的 window,跳過 Edge 內建頁(edge://nurturing 等)。
        從新到舊試 handle,找到 elearn.hrd.gov.tw 就切過去;
        沒找到 → 嘗試關掉 edge:// / chrome:// 非課程視窗,留主視窗。
        """
        target_domain = "elearn.hrd.gov.tw"
        handles = list(self.driver.window_handles)
        for h in reversed(handles):
            try:
                self.driver.switch_to.window(h)
                cur_url = (self.driver.current_url or "").lower()
                if target_domain in cur_url:
                    self.log(f"切換到課程播放器視窗 (URL: {cur_url[:60]})")
                    return True
            except Exception:
                continue
        # 沒找到課程 domain — 關閉非課程內建頁 (Edge nurturing 等)
        for h in list(self.driver.window_handles):
            try:
                self.driver.switch_to.window(h)
                cur_url = (self.driver.current_url or "").lower()
                if (cur_url.startswith("edge://") or cur_url.startswith("chrome://") or
                        "nurturing" in cur_url):
                    self.log(f"⚠ 關閉非課程 Edge 內建視窗: {cur_url[:60]}")
                    self.driver.close()
            except Exception:
                pass
        # 切回剩下任一視窗
        try:
            remaining = self.driver.window_handles
            if remaining:
                self.driver.switch_to.window(remaining[-1])
                cur_url = (self.driver.current_url or "")[:60]
                self.log(f"⚠ 沒找到課程 domain,留在 {cur_url}")
        except Exception:
            pass
        return False

    def _detect_scorm_time(self):
        """v1.8.33:嘗試從 SCORM API 抓 session_time / total_time。
        SCORM 1.2 (window.API.LMSGetValue) / SCORM 2004 (API_1484_11.GetValue)。
        回傳 (mode, time_str) 或 None。
        """
        js = (
            "try {"
            "  var c1 = [window.API, window.parent && window.parent.API, window.top && window.top.API];"
            "  for (var i=0;i<c1.length;i++){"
            "    var a=c1[i];"
            "    if (a && typeof a.LMSGetValue==='function'){"
            "      var t=a.LMSGetValue('cmi.core.total_time') || a.LMSGetValue('cmi.core.session_time');"
            "      if (t) return ['scorm12', String(t)];"
            "    }"
            "  }"
            "  var c2 = [window.API_1484_11, window.parent && window.parent.API_1484_11, window.top && window.top.API_1484_11];"
            "  for (var i=0;i<c2.length;i++){"
            "    var a=c2[i];"
            "    if (a && typeof a.GetValue==='function'){"
            "      var t=a.GetValue('cmi.total_time') || a.GetValue('cmi.session_time');"
            "      if (t) return ['scorm2004', String(t)];"
            "    }"
            "  }"
            "  return null;"
            "} catch(e) { return null; }"
        )
        try:
            return self.driver.execute_script(js)
        except Exception:
            return None

    def _extract_already_from_current(self):
        """v1.8.36/39:從當前 driver context 任一 frame 找「閱讀時數:HH:MM:SS」(已上時數)。
        v1.8.39:排除「(含)以上」尾綴(那是通過條件門檻,不是已上時數)。
        用於 _learning_loop 中途檢查站方實際時數,取代 _can_take_exam_now() 按鈕 proxy。
        找不到回 None。
        """
        js = (
            "function f(d){"
            "  try {"
            "    var t=(d.body && d.body.innerText) || '';"
            "    var re=/閱讀時數\\s*[:：]\\s*(\\d+):(\\d+):(\\d+)([^\\n]{0,15})/g;"
            "    var m;"
            "    while ((m=re.exec(t))!==null) {"
            "      if ((m[4]||'').indexOf('以上')<0) {"
            "        return [parseInt(m[1]), parseInt(m[2]), parseInt(m[3])];"
            "      }"
            "    }"
            "  } catch(e) {}"
            "  return null;"
            "}"
            "var r=f(document); if (r) return r;"
            "var ifs=document.getElementsByTagName('iframe');"
            "for (var i=0;i<ifs.length;i++){"
            "  try { r=f(ifs[i].contentDocument); if (r) return r; } catch(e) {}"
            "}"
            "return null;"
        )
        try:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass
            result = self.driver.execute_script(js)
            if result and len(result) == 3:
                h, m, s = result
                return h * 60 + m + s / 60.0
        except Exception:
            pass
        return None

    def _detect_video_duration(self):
        """v1.8.30:偵測當前頁面 <video>.duration (秒)。跨 frame 找;找不到回 None。
        用於 _learning_loop 動態決定每頁停留時間,避免推進太快。
        """
        js = (
            "var v = document.querySelector('video');"
            "if (v && !isNaN(v.duration) && v.duration > 0) return v.duration;"
            "return null;"
        )
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        try:
            d = self.driver.execute_script(js)
            if d:
                return float(d)
        except Exception:
            pass
        try:
            for fr in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(fr)
                    d = self.driver.execute_script(js)
                    if d:
                        return float(d)
                    for inner in self._all_frames():
                        try:
                            self.driver.switch_to.frame(inner)
                            d = self.driver.execute_script(js)
                            if d:
                                return float(d)
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            try: self.driver.switch_to.parent_frame()
                            except Exception: pass
                except Exception:
                    pass
                finally:
                    try: self.driver.switch_to.default_content()
                    except Exception: pass
        except Exception:
            pass
        finally:
            try: self.driver.switch_to.default_content()
            except Exception: pass
        return None

    def _try_pathtree_advance(self):
        """v1.8.18：衛生福利e學園 章節由 JS pathtree 動態管理；
        靜態 selector 抓不到，改用 pathtree.nextStep(1) 推進一個節點。
        回 True 代表有成功呼叫"""
        try:
            for frame in self._all_frames():
                try:
                    name = frame.get_attribute("name") or ""
                    fid  = frame.get_attribute("id") or ""
                    if name not in ("s_catalog",) and fid not in ("s_catalog",):
                        continue
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(frame)
                    has = self.driver.execute_script(
                        "return typeof pathtree !== 'undefined' && typeof pathtree.nextStep === 'function';")
                    if not has:
                        continue
                    # 先展開全部章節
                    try:
                        self.driver.execute_script("pathtree.expandingAll && pathtree.expandingAll();")
                    except Exception:
                        pass
                    # 推進到下一節點
                    self.driver.execute_script("pathtree.nextStep(1);")
                    self.driver.switch_to.default_content()
                    # v1.8.29:每門課首次成功才 log,後續 cycle 沉默
                    if not getattr(self, '_pathtree_log_done', False):
                        self._pathtree_log_done = True
                        self.log("→ pathtree.nextStep(1) 推進章節中(後續 cycle 沉默)")
                    return True
                except Exception:
                    continue
        except Exception:
            pass
        finally:
            try: self.driver.switch_to.default_content()
            except Exception: pass
        return False

    def _probe_in_current(self, ctx_label, selectors):
        """v1.8.28:在當前 driver context(主頁或某 frame)探測所有 selector,印命中數+前 3 個標題"""
        for sel in selectors:
            try:
                els = [e for e in self.driver.find_elements(By.CSS_SELECTOR, sel)
                       if e.is_displayed()]
                if not els:
                    continue
                titles = []
                for e in els[:3]:
                    try:
                        t = (e.get_attribute("title") or e.text or "").strip()
                        t = t.replace("\n", " ")[:40]
                        if not t:
                            cls = (e.get_attribute("class") or "")[:20]
                            t = f"({e.tag_name}.{cls})"
                        titles.append(t)
                    except Exception:
                        titles.append("(read err)")
                more = f" +{len(els)-3}" if len(els) > 3 else ""
                self.log(f"  🔍[{ctx_label}] {sel} → {len(els)}: {' / '.join(titles)}{more}")
            except Exception:
                pass

    def _probe_all_selectors(self, selectors):
        """v1.8.28:診斷工具 — 遍歷主頁與各 frame,把所有 selector 命中 dump 出來
        每門課只跑一次(由 _chapter_selectors_probed 控制),用來找出真正章節的 selector
        """
        self.log("🔍 v1.8.28 selector 診斷開始(只跑一次)...")
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        self._probe_in_current("主頁面", selectors)
        try:
            for frame in self._all_frames():
                fid = frame.get_attribute("id") or ""
                fname = frame.get_attribute("name") or ""
                label = f"frame[{fid or fname or '?'}]"
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(frame)
                    self._probe_in_current(label, selectors)
                    for inner in self._all_frames():
                        iid = inner.get_attribute("id") or ""
                        iname = inner.get_attribute("name") or ""
                        ilabel = f"{label}>nested[{iid or iname or '?'}]"
                        try:
                            self.driver.switch_to.frame(inner)
                            self._probe_in_current(ilabel, selectors)
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            try: self.driver.switch_to.parent_frame()
                            except Exception: pass
                except Exception:
                    pass
                finally:
                    try: self.driver.switch_to.default_content()
                    except Exception: pass
        except Exception:
            pass
        finally:
            try: self.driver.switch_to.default_content()
            except Exception: pass
        self.log("🔍 v1.8.28 selector 診斷結束")

    def _dump_chapter_titles(self, els, where_label):
        """v1.8.27:在 frame context 內 dump 章節 — 避免後續切回 default_content 後 stale。
        每門課第一次找到時印一次,後續 cycle 不再 dump。
        """
        if getattr(self, '_chapter_found_logged', False):
            return
        self._chapter_found_logged = True
        self.log(f"📖 在 {where_label} 找到 {len(els)} 個章節:")
        for i, ch in enumerate(els[:20], 1):
            try:
                title_attr = (ch.get_attribute("title") or "").strip()
                text_val   = (ch.text or "").strip()
                display = title_attr or text_val
                if not display:
                    outer = ch.get_attribute("outerHTML") or ""
                    display = "[outerHTML] " + outer.replace("\n", " ").strip()[:120]
                else:
                    display = display.replace("\n", " ")[:80]
                tag = ch.tag_name
                self.log(f"   [{i}] tag={tag} {display}")
            except Exception as _e:
                self.log(f"   [{i}] (讀取錯誤: {str(_e)[:80]})")
        if len(els) > 20:
            self.log(f"   ...(其他 {len(els)-20} 個略)")

    def _find_chapters(self):
        """衛生福利e學園 用 <frame> 而非 <iframe>，章節在 s_catalog frame
        中華 e等公務園 等其他平台則直接在 main page 或 iframe 內
        """
        # v1.8.17 擴充 selectors（衛生福利e學園 + e等公務園 + 中華 e 等公務園 通吃）
        selectors = [
            "input[type='radio']",
            "a[onclick*='goPage']",
            "a[onclick*='play']",
            "a[onclick*='changeContent']",
            "a[onclick*='selectChapter']",
            "a[onclick*='openLesson']",
            "a[onclick*='SCO']",
            "[onclick*='lesson']",
            "[onclick*='unit']",
            "[onclick*='Chapter']",
            "[onclick*='Lesson']",
            "[onclick*='Unit']",
            "[onclick*='showSCO']",
            "[onclick*='openPDF']",
            "[onclick*='LoadCourse']",
            "[onclick*='loadContent']",
            "[onclick*='ChangeNode']",
            "span[onclick]",
            "li[onclick]",
            "div[onclick][role='button']",
            ".syllabus_node",
            ".course_tree li a",
            ".chapter_item",
            ".lesson_menu li",
            ".tree_node input",
            ".tree_node a",
            "#contentList li a",
            "ul.chapters li a",
            "ul.chapter_list li",
            ".sidebar a[onclick]",
            ".course_menu a",
            ".lesson_unit a",
            ".course_node",
            "[role='treeitem']",
            "[data-sco-id]",
            "[data-lesson-id]",
            "label[for*='lesson'], label[for*='unit']",
            # 兜底：任何 cursor:pointer + 看起來像章節文字的元素
            "li[style*='cursor']",
            "span[style*='cursor:pointer']",
        ]

        # v1.8.28:每門課第一次完整探測所有 selector(診斷用),不影響主邏輯
        if not getattr(self, '_chapter_selectors_probed', False):
            self._chapter_selectors_probed = True
            self._probe_all_selectors(selectors)

        # 主頁面找一次
        for sel in selectors:
            try:
                els = [e for e in self.driver.find_elements(By.CSS_SELECTOR, sel)
                       if e.is_displayed()]
                if len(els) >= 2:
                    self._dump_chapter_titles(els, f"主頁面 ({sel})")
                    return els
            except Exception:
                continue

        # 進入每個 frame/iframe 找；衛生福利e學園 章節在 s_catalog
        try:
            for frame in self._all_frames():
                fid = frame.get_attribute("id") or ""
                fname = frame.get_attribute("name") or ""
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(frame)
                    for sel in selectors:
                        try:
                            els = [e for e in self.driver.find_elements(
                                    By.CSS_SELECTOR, sel) if e.is_displayed()]
                            if len(els) >= 2:
                                # 注意：呼叫端會在 frame context 中操作這些元素
                                # 若有 stale，必須回到 default_content 重抓
                                self._dump_chapter_titles(els, f"frame[{fid or fname}] ({sel})")
                                return els
                        except Exception:
                            pass
                    # 第一層找不到 → 嘗試此 frame 內的子 frame（s_catalog 可能還有子 frame）
                    for inner in self._all_frames():
                        try:
                            self.driver.switch_to.frame(inner)
                            for sel in selectors:
                                try:
                                    els = [e for e in self.driver.find_elements(
                                            By.CSS_SELECTOR, sel) if e.is_displayed()]
                                    if len(els) >= 2:
                                        self._dump_chapter_titles(els, f"nested frame ({sel})")
                                        return els
                                except Exception:
                                    pass
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            try:
                                self.driver.switch_to.parent_frame()
                            except Exception:
                                self.driver.switch_to.default_content()
                                self.driver.switch_to.frame(frame)
                except Exception:
                    pass
                finally:
                    try:
                        self.driver.switch_to.default_content()
                    except Exception:
                        pass
        except Exception:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass
        return []

    def _can_take_exam_now(self):
        """檢查是否在任一 frame 中存在可點擊的「進行測驗」按鈕。
        v1.8.23 註：按鈕存在性 != 時數已達標(舊版誤把這個當代理信號);
                  時數判斷改由 _process_current_course_page 用 已上時數 vs req_min 主導。
        v1.6.2：用 normalize-space(.) 搜後代文字（避免按鈕含內層 div 抓不到）
        """
        # 多個 XPath candidate，優先匹配按鈕類 tag/class
        XPATHS = [
            "//a[contains(normalize-space(.),'進行測驗')]",
            "//button[contains(normalize-space(.),'進行測驗')]",
            "//input[(@type='button' or @type='submit') and contains(@value,'進行測驗')]",
            "//*[contains(@class,'btn') and contains(normalize-space(.),'進行測驗')]",
            "//*[@onclick and contains(normalize-space(.),'進行測驗')]",
        ]

        def _hit_in_current_frame():
            for xp in XPATHS:
                try:
                    for el in self.driver.find_elements(By.XPATH, xp):
                        try:
                            if el.is_displayed():
                                self._last_exam_btn_info = (
                                    f"tag={el.tag_name} "
                                    f"class={el.get_attribute('class') or ''}")
                                return True
                        except Exception:
                            pass
                except Exception:
                    pass
            return False

        # 主頁面
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        if _hit_in_current_frame():
            return True

        # 各 frame
        try:
            for frame in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(frame)
                    if _hit_in_current_frame():
                        return True
                    # 子 frame
                    for inner in self._all_frames():
                        try:
                            self.driver.switch_to.frame(inner)
                            if _hit_in_current_frame():
                                return True
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            try:
                                self.driver.switch_to.parent_frame()
                            except Exception:
                                pass
                except Exception:
                    pass
        finally:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass
        return False

    def _find_in_any_frame_xpath(self, xpath, clickable=False):
        """跨所有 frame/iframe 搜尋符合 xpath 的可見元素。
        如果找到，會把 driver 留在該 frame context（caller 完成後請 switch_to.default_content()）。
        回傳 list（找不到回傳 []）。
        """
        def _try_here():
            try:
                els = self.driver.find_elements(By.XPATH, xpath)
                ret = []
                for e in els:
                    try:
                        if not e.is_displayed():
                            continue
                        if clickable and not e.is_enabled():
                            continue
                        ret.append(e)
                    except Exception:
                        continue
                return ret
            except Exception:
                return []

        try:
            self.driver.switch_to.default_content()
        except Exception:
            return []

        hits = _try_here()
        if hits:
            return hits

        for frame in self._all_frames():
            try:
                self.driver.switch_to.frame(frame)
                hits = _try_here()
                if hits:
                    return hits
                # nested frame
                for inner in self._all_frames():
                    try:
                        self.driver.switch_to.frame(inner)
                        hits = _try_here()
                        if hits:
                            return hits
                        self.driver.switch_to.parent_frame()
                    except Exception:
                        try:
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            pass
                self.driver.switch_to.default_content()
            except Exception:
                try:
                    self.driver.switch_to.default_content()
                except Exception:
                    pass
        return []

    def _try_jump_to_sysbar_link(self, link_keywords, label):
        """共用：點 mooc_sysbar 內的某個導覽連結（測驗/問卷等）。
        link_keywords: 文字或 href 關鍵字 list
        回傳 True = 成功點擊，False = 找不到該連結
        """
        try:
            self.driver.switch_to.default_content()
        except Exception:
            return False

        sysbar_frame = None
        try:
            for fr in self._all_frames():
                name = fr.get_attribute("name") or ""
                fid = fr.get_attribute("id") or ""
                if "sysbar" in name.lower() or "sysbar" in fid.lower():
                    sysbar_frame = fr
                    break
        except Exception:
            pass
        if sysbar_frame is None:
            return False

        try:
            self.driver.switch_to.frame(sysbar_frame)
            target = None
            for kw in link_keywords:
                try:
                    # 文字匹配
                    for el in self.driver.find_elements(By.XPATH,
                            f"//a[contains(normalize-space(text()),'{kw}')]"):
                        if el.is_displayed():
                            target = el; break
                    if target: break
                    # href 匹配
                    for el in self.driver.find_elements(By.CSS_SELECTOR,
                            f"a[href*='{kw}']"):
                        if el.is_displayed():
                            target = el; break
                    if target: break
                except Exception:
                    pass
            if not target:
                self.log(f"sysbar 內找不到「{label}」連結")
                return False
            self.log(f"點擊「{label}」連結...")
            self.driver.execute_script("arguments[0].click()", target)
            return True
        except Exception as e:
            self.log(f"點「{label}」失敗：{e}")
            return False
        finally:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass

    def _exam_already_passed(self):
        """v1.8.20：偵測測驗已通過（避免重做）。
        v1.8.23 優先級:
          P1. 明確分數比對(每課及格門檻不同) → 直接判定
          P2. badges 主導(沒分數時) → needs[exam]=True→還沒過/False→已過
          P3. 都失效時走原字串 match 兜底
        """
        # P1. 明確比對(分數 + 該課及格門檻;避免硬編 60)
        score = getattr(self, "_current_exam_score", None)
        pass_ = getattr(self, "_current_exam_pass",  None)
        if score is not None and pass_ is not None:
            return score >= pass_

        # P2. badges
        needs = getattr(self, "_current_needs", {}) or {}
        ne = needs.get("exam")
        if ne is True:
            return False
        if ne is False:
            return True

        # P3. 字串 match 兜底
        PASS_KEYS = ("恭喜通過", "已通過", "通過測驗", "測驗已通過",
                     "測驗合格", "查看測驗結果", "查看成績")
        FAIL_KEYS = ("未通過", "不及格", "未達及格", "重新測驗",
                     "再次測驗", "尚未通過")

        def _check_in_current():
            # 先排除 fail keys（fail 頁面也常出現「通過」字樣 → 必須先擋）
            for fk in FAIL_KEYS:
                try:
                    els = self.driver.find_elements(
                        By.XPATH, f"//*[contains(normalize-space(.),'{fk}')]")
                    for el in els:
                        try:
                            if el.is_displayed():
                                return None  # 明確未通過 → 不算 pass
                        except Exception:
                            pass
                except Exception:
                    pass
            # 再找 pass keys
            for pk in PASS_KEYS:
                try:
                    els = self.driver.find_elements(
                        By.XPATH, f"//*[contains(normalize-space(.),'{pk}')]")
                    for el in els:
                        try:
                            if el.is_displayed():
                                return pk
                        except Exception:
                            pass
                except Exception:
                    pass
            return False

        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        r = _check_in_current()
        if r is None: return False
        if r: return True

        try:
            for fr in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(fr)
                    r = _check_in_current()
                    if r is None: return False
                    if r: return True
                    for inner in self._all_frames():
                        try:
                            self.driver.switch_to.frame(inner)
                            r = _check_in_current()
                            if r is None: return False
                            if r: return True
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            try: self.driver.switch_to.parent_frame()
                            except Exception: pass
                except Exception:
                    pass
        finally:
            try: self.driver.switch_to.default_content()
            except Exception: pass
        return False

    def _survey_already_done(self):
        """v1.8.7：快速偵測問卷已填寫（跨 frame 找「修改問卷／查看問卷／已填寫／已繳交」）
        看到任一 → 立刻 return True，主流程直接跳下一門課，不空等。
        v1.8.23/24：badges 明確「未問卷」(is True) 時短路;needs=None 走兜底字串 match
        """
        # v1.8.24：嚴格 `is True`(而非 truthy) — 避免 None 也誤觸短路
        needs = getattr(self, "_current_needs", {}) or {}
        if needs.get("survey") is True:
            return False

        DONE_KEYS = ("修改問卷", "查看問卷", "查看結果", "已填寫", "已繳交",
                     "已完成", "重新填寫")
        # XPath 一次抓所有「按鈕級別」的元素
        XP = (
            "//a[" + " or ".join([f"contains(normalize-space(.),'{k}')" for k in DONE_KEYS]) + "] | "
            "//button[" + " or ".join([f"contains(normalize-space(.),'{k}')" for k in DONE_KEYS]) + "] | "
            "//*[contains(@class,'btn') and (" +
            " or ".join([f"contains(normalize-space(.),'{k}')" for k in DONE_KEYS]) + ")] | "
            "//*[contains(@class,'process-btn') and (" +
            " or ".join([f"contains(normalize-space(.),'{k}')" for k in DONE_KEYS]) + ")]"
        )

        def _hit():
            try:
                els = self.driver.find_elements(By.XPATH, XP)
                for el in els:
                    try:
                        if not el.is_displayed():
                            continue
                        return True
                    except Exception:
                        pass
            except Exception:
                pass
            return False

        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        if _hit():
            return True
        try:
            for fr in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(fr)
                    if _hit():
                        return True
                    for inner in self._all_frames():
                        try:
                            self.driver.switch_to.frame(inner)
                            if _hit():
                                return True
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            try:
                                self.driver.switch_to.parent_frame()
                            except Exception:
                                pass
                except Exception:
                    pass
        finally:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass
        return False

    def _can_fill_survey_now(self):
        """檢查是否在任一 frame 中存在「未填寫」狀態的問卷按鈕。
        v1.8.1：排除「修改問卷／已填寫／已繳交／done/pass/finish/disabled」狀態。
        """
        # 收嚴：只認「填寫」「進行」「開始」三種動詞，排除「修改」（已填過）
        XPATHS = [
            "//a[contains(normalize-space(.),'填寫問卷')]",
            "//a[contains(normalize-space(.),'進行問卷')]",
            "//a[contains(normalize-space(.),'開始填寫')]",
            "//button[contains(normalize-space(.),'填寫問卷')]",
            "//button[contains(normalize-space(.),'進行問卷')]",
            "//*[contains(@class,'process-btn') and "
            "(contains(normalize-space(.),'填寫問卷') or "
            "contains(normalize-space(.),'進行問卷') or "
            "contains(normalize-space(.),'開始填寫'))]",
        ]
        DONE_CLS_TOKENS = ("done", "pass", "finished", "complete", "disabled", "inactive")
        DONE_TEXT_TOKENS = ("已填寫", "已繳交", "已完成", "修改問卷", "查看問卷",
                            "重新填寫")

        def _is_button_done(el):
            try:
                cls = (el.get_attribute("class") or "").lower()
                if any(tok in cls for tok in DONE_CLS_TOKENS):
                    return True
                txt = (el.text or "").strip()
                if any(tok in txt for tok in DONE_TEXT_TOKENS):
                    return True
                # 父層附近若標明「問卷狀態：已填寫」也視為已完成
                try:
                    parent = el.find_element(By.XPATH, "./ancestor::*[1]")
                    ptxt = (parent.text or "")
                    if "問卷狀態" in ptxt and ("已填寫" in ptxt or "已繳交" in ptxt):
                        return True
                except Exception:
                    pass
            except Exception:
                pass
            return False

        def _hit_in_current_frame():
            for xp in XPATHS:
                try:
                    for el in self.driver.find_elements(By.XPATH, xp):
                        try:
                            if not el.is_displayed():
                                continue
                            if _is_button_done(el):
                                continue
                            return True
                        except Exception:
                            pass
                except Exception:
                    pass
            return False

        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        if _hit_in_current_frame():
            return True
        try:
            for frame in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(frame)
                    if _hit_in_current_frame():
                        return True
                    for inner in self._all_frames():
                        try:
                            self.driver.switch_to.frame(inner)
                            if _hit_in_current_frame():
                                return True
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            try:
                                self.driver.switch_to.parent_frame()
                            except Exception:
                                pass
                except Exception:
                    pass
        finally:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass
        return False

    def _try_jump_to_survey_sysbar(self):
        """跳到「問卷/評價」頁，回傳是否實際出現可填問卷
        v1.6.2：輪詢 12 秒等 frame 載入
        v1.8.7：偵測到「修改問卷／查看問卷／已填寫」立刻 return False（已填過、不空等）
        """
        if not self._try_jump_to_sysbar_link(
                ["問卷/評價", "問卷", "questionnaire"], "問卷/評價"):
            return False
        for i in range(12):
            self._human_sleep(1.0, 0.2)
            # v1.8.7：問卷已填 → 立刻離開
            if self._survey_already_done():
                self.log(f"⏭ 問卷已填寫（第{i+1}秒偵測到「修改問卷／查看問卷」），跳過不空等")
                return False
            if self._can_fill_survey_now():
                self.log(f"✓ 偵測到可填問卷（第{i+1}秒）")
                return True
        # v1.8.23：失敗時印實際到達位置(判斷點驗證)
        try:
            cur_url   = (self.driver.current_url or "")[:80]
            cur_title = (self.driver.title or "")[:40]
        except Exception:
            cur_url, cur_title = "?", "?"
        self.log(f"⚠ 已點問卷連結，但 12 秒內未偵測到可填問卷按鈕 — URL={cur_url} title={cur_title}")
        return False

    def _try_jump_to_exam_sysbar(self):
        """跳到「測驗/考試」頁，回傳 True = 確實能進測驗
        v1.6.2：輪詢 12 秒等 frame 載入
        """
        if not self._try_jump_to_sysbar_link(
                ["測驗/考試", "測驗", "考試", "exam_list"], "測驗/考試"):
            return False
        for i in range(12):
            self._human_sleep(1.0, 0.2)
            if self._can_take_exam_now():
                info = getattr(self, "_last_exam_btn_info", "?")
                self.log(f"✓ 偵測到「進行測驗」按鈕（第{i+1}秒，{info}）")
                return True
        # v1.8.23：失敗時印實際到達位置(判斷點驗證)
        try:
            cur_url   = (self.driver.current_url or "")[:80]
            cur_title = (self.driver.title or "")[:40]
        except Exception:
            cur_url, cur_title = "?", "?"
        self.log(f"⚠ 已點測驗連結，但 12 秒內未偵測到「進行測驗」按鈕 — URL={cur_url} title={cur_title}")
        return False

    # ── 課程播放器：自動測驗 ─────────────────────────────────

    def _switch_to_new_window_if_any(self, prev_handles, label="新視窗"):
        """若 click 後新開視窗，自動切過去；回傳 True=有切"""
        try:
            self._human_sleep(1.0, 0.3)
            cur = self.driver.window_handles
            new_handles = [h for h in cur if h not in prev_handles]
            if new_handles:
                self.driver.switch_to.window(new_handles[-1])
                self.log(f"✓ 切換到{label} (URL: {self.driver.current_url[:80]})")
                self._human_sleep(1.5, 0.4)
                return True
        except Exception as e:
            self.log(f"切換新視窗失敗: {e}")
        return False

    def _check_exam_result(self):
        """讀結果頁判斷通過/未通過 + 抓分數(v1.8.45)。
        回傳：'pass' / 'fail' / 'unknown'
        分數另存到 self._last_exam_score(0~100,抓不到 None)。
        """
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        # 跨 frame 看頁面文字
        page_texts = []
        try:
            page_texts.append((self.driver.find_element(By.TAG_NAME, "body").text or "")[:2000])
        except Exception:
            pass
        try:
            for frame in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(frame)
                    page_texts.append((self.driver.find_element(By.TAG_NAME, "body").text or "")[:2000])
                except Exception:
                    pass
        finally:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass

        all_text = "\n".join(page_texts)
        # v1.8.46:抓分數 — 改順序避免 X/Y 誤抓題目內文(2024/12/01、1/3 機率)
        # 1) keyword「分數/得分/成績」最可靠 → 2) 鄰近 keyword 的「X 分」 → 3) X/Y 帶合理性檢查
        self._last_exam_score = None
        try:
            # 1) 「分數:65」「得分:65」「成績:65」「score:65」
            m = re.search(r'(?:分數|得分|成績|score)\s*[:：]?\s*(\d+(?:\.\d+)?)\s*分?',
                          all_text, re.IGNORECASE)
            if m:
                v = float(m.group(1))
                if 0 <= v <= 100:
                    self._last_exam_score = v
            # 2) 「本次/此次/您 ... X 分」鄰近 keyword
            if self._last_exam_score is None:
                m = re.search(r'(?:本次|此次|您|測驗|測試)[^。\n]{0,30}?(\d+(?:\.\d+)?)\s*分',
                              all_text)
                if m:
                    v = float(m.group(1))
                    if 0 <= v <= 100:
                        self._last_exam_score = v
            # 3) X/Y 比例 — 加合理性檢查(分母常見滿分,分子 0~分母)避免抓到日期/題目內文
            if self._last_exam_score is None:
                COMMON_DENS = {10, 20, 25, 50, 100, 200}
                for m in re.finditer(r'(\d+(?:\.\d+)?)\s*/\s*(\d+(?:\.\d+)?)', all_text):
                    try:
                        num = float(m.group(1)); den = float(m.group(2))
                        if den in COMMON_DENS and 0 <= num <= den:
                            self._last_exam_score = num * 100.0 / den
                            break
                    except Exception:
                        continue
        except Exception:
            self._last_exam_score = None
        # 注意 順序：先判 fail（不通過 也含 通過 字串）
        FAIL_KEYS = ["未通過", "不及格", "未達及格", "重新測驗", "再次測驗", "尚未通過"]
        PASS_KEYS = ["恭喜通過", "已通過", "及格", "合格", "通過測驗"]
        for k in FAIL_KEYS:
            if k in all_text:
                return "fail"
        for k in PASS_KEYS:
            if k in all_text:
                return "pass"
        return "unknown"

    def _try_click_show_answers(self):
        """嘗試點「查看作答」/「查看詳解」/「檢視答案」之類的按鈕，讓正解可見"""
        XPS = [
            "//a[contains(normalize-space(.),'查看作答')]",
            "//a[contains(normalize-space(.),'查看詳解')]",
            "//a[contains(normalize-space(.),'查看解答')]",
            "//a[contains(normalize-space(.),'檢視答案')]",
            "//a[contains(normalize-space(.),'觀看作答')]",
            "//button[contains(normalize-space(.),'查看作答')]",
            "//button[contains(normalize-space(.),'查看詳解')]",
            "//button[contains(normalize-space(.),'查看解答')]",
            "//button[contains(normalize-space(.),'檢視答案')]",
        ]
        for xp in XPS:
            try:
                btn = self._find_in_any_frame_xpath(xp, clickable=True)
                if btn:
                    try:
                        btn[0].click()
                    except Exception:
                        self.driver.execute_script("arguments[0].click()", btn[0])
                    self.log(f"📖 已點「{btn[0].text.strip()[:10]}」展示正解")
                    self._human_sleep(2.0, 0.5)
                    return True
            except Exception:
                pass
        return False

    def _harvest_from_result_page(self):
        """從測驗結果頁拔正解寫進 qa_bank。回傳 (新增題數, 結構化結果 list)。
        v1.8.7：每次失敗都呼叫，累積學習。"""
        course = getattr(self, "_current_course_title", "") or ""
        # 1) 試著點「查看作答」按鈕（有些頁面預設不展開）
        self._try_click_show_answers()

        # 2) 跨 frame 跑 JS 抓 (question, correct_options, type)
        contexts = [None]
        try:
            for fr in self._all_frames():
                contexts.append(fr)
        except Exception:
            pass

        all_results = []
        for ctx in contexts:
            try:
                self.driver.switch_to.default_content()
                if ctx is not None:
                    try:
                        self.driver.switch_to.frame(ctx)
                    except Exception:
                        continue
                # 嵌套 frame 也掃一層
                try:
                    chunk = self._extract_correct_in_current_frame()
                    all_results.extend(chunk)
                except Exception:
                    pass
                # nested
                try:
                    inner_frames = self._all_frames()
                except Exception:
                    inner_frames = []
                for inner in inner_frames:
                    try:
                        self.driver.switch_to.frame(inner)
                        chunk = self._extract_correct_in_current_frame()
                        all_results.extend(chunk)
                        self.driver.switch_to.parent_frame()
                    except Exception:
                        try:
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            pass
            except Exception:
                pass
            finally:
                try:
                    self.driver.switch_to.default_content()
                except Exception:
                    pass

        # 3) 寫入 qa_bank（不覆蓋既有，去重）
        n_added = 0
        seen_keys = set()
        for r in all_results:
            q = (r.get("q") or "").strip()
            answers = r.get("a") or []
            qtype = r.get("type") or "SC"
            if not q or not answers:
                continue
            key = QABank.normalize(q)
            if not key or key in seen_keys:
                continue
            seen_keys.add(key)
            # v1.8.7 bug #4: 用 has_exact（精確比對）而非 fuzzy find —
            #   避免「題庫有前綴/超集相似題」就跳過，結果不同題的真正正解永遠學不到
            if self.qa_bank.has_exact(q):
                continue   # 此題在題庫已有 exact key，不覆蓋
            # harvester 是高信任（真正結果頁），用 overwrite=True（預設）
            self.qa_bank.add(q, answers, qtype=qtype, course=course)
            n_added += 1
        if n_added > 0:
            try:
                self.qa_bank.save()
            except Exception:
                pass
        return n_added, all_results

    def _extract_correct_in_current_frame(self):
        """v1.8.7 在當前 frame 用 JS 抓「題目 + 正解選項」list。
        多策略偵測正解：class/text/icon/style。
        """
        try:
            return self.driver.execute_script(r"""
                // ── 工具：判斷某 element 是否被標為「正解」 ──
                function isMarkedCorrect(el) {
                    if (!el) return false;
                    var anc = el;
                    var depth = 0;
                    while (anc && depth < 5) {
                        depth++;
                        var cls = (anc.className || '').toString().toLowerCase();
                        if (/\b(correct|right(?!s)|success|pass(?!word)|win|tick|chosen-correct|answer-correct)\b/.test(cls)) {
                            return true;
                        }
                        var sty = (anc.getAttribute && anc.getAttribute('style') || '').toLowerCase();
                        // v1.8.7 bug #1: 原本 #0[a-f0-9]?…? 讓純黑 #000/#000000 也被當正解；
                        //   rgb(0, 1?\d{0,2}, 0) 也 match rgb(0,0,0)。結果題庫被黑字選項污染。
                        //   改用嚴格綠判定：hex G channel >=8 且 R/B <=4；rgb G >=120 且 R/B <=80
                        var hexMatch = sty.match(/color\s*:\s*#([0-9a-f]{3,6})\b/);
                        var rgbMatch = sty.match(/color\s*:\s*rgb\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)/);
                        var greenNamed = /color\s*:\s*(green|lime|limegreen|darkgreen|forestgreen|mediumseagreen|seagreen)\b/.test(sty);
                        var isGreenStyle = greenNamed;
                        if (!isGreenStyle && hexMatch) {
                            var hx = hexMatch[1];
                            var r,g,b;
                            if (hx.length === 3) { r=parseInt(hx[0]+hx[0],16); g=parseInt(hx[1]+hx[1],16); b=parseInt(hx[2]+hx[2],16); }
                            else if (hx.length === 6) { r=parseInt(hx.slice(0,2),16); g=parseInt(hx.slice(2,4),16); b=parseInt(hx.slice(4,6),16); }
                            else { r=g=b=0; }
                            isGreenStyle = (g >= 128 && r <= 80 && b <= 80);
                        }
                        if (!isGreenStyle && rgbMatch) {
                            var rr=parseInt(rgbMatch[1],10), gg=parseInt(rgbMatch[2],10), bb=parseInt(rgbMatch[3],10);
                            isGreenStyle = (gg >= 128 && rr <= 80 && bb <= 80);
                        }
                        if (isGreenStyle) {
                            return true;
                        }
                        anc = anc.parentElement;
                    }
                    // 文字標記
                    var t = (el.textContent || '').trim();
                    if (/(✓|✔|【正解】|【正確】|正解|正確答案|\(O\)|（O）)/.test(t)) {
                        return true;
                    }
                    // 兄弟 / 父層 兄弟出現「正解／正確」標
                    var p = el.parentElement;
                    if (p) {
                        var pt = (p.textContent || '').trim();
                        // 太貪心會誤判，加長度限制：父文字 < 80 字
                        if (pt.length < 80 && /(✓|✔|【正解】|正解|正確答案)/.test(pt)) {
                            return true;
                        }
                    }
                    return false;
                }
                // ── 取選項文字（label / sibling / parent label） ──
                function getOptionLabel(inp) {
                    if (inp.id) {
                        var L = document.querySelector('label[for="' + inp.id + '"]');
                        if (L) {
                            var t = (L.innerText || L.textContent || '').trim();
                            if (t) return t;
                        }
                    }
                    if (inp.parentElement && inp.parentElement.tagName === 'LABEL') {
                        var t = (inp.parentElement.innerText || inp.parentElement.textContent || '').trim();
                        if (t) return t;
                    }
                    var sib = inp.nextSibling;
                    while (sib && sib.nodeType === 3 && !sib.nodeValue.trim()) sib = sib.nextSibling;
                    if (sib) {
                        var t = (sib.textContent || sib.nodeValue || '').trim();
                        if (t) return t;
                    }
                    // 同層 element 兄弟
                    var es = inp.nextElementSibling;
                    if (es) {
                        var t = (es.innerText || es.textContent || '').trim();
                        if (t) return t;
                    }
                    return '';
                }
                // ── 取題目文字（與 _get_question_text 同邏輯） ──
                function getQuestionText(inp, target_name) {
                    var all_doc_inputs = document.querySelectorAll(
                        'input[type="radio"], input[type="checkbox"]');
                    var same_group = [];
                    for (var i = 0; i < all_doc_inputs.length; i++) {
                        if ((all_doc_inputs[i].name || '') === target_name) {
                            same_group.push(all_doc_inputs[i]);
                        }
                    }
                    if (same_group.length === 0) return '';
                    var anc = inp;
                    while (anc && anc.tagName !== 'BODY') {
                        var ca = true;
                        for (var i = 0; i < same_group.length; i++) {
                            if (!anc.contains(same_group[i])) { ca = false; break; }
                        }
                        if (ca) break;
                        anc = anc.parentElement;
                    }
                    if (!anc) return '';
                    var ai = anc.querySelectorAll('input[type="radio"], input[type="checkbox"]');
                    var has_other = false;
                    for (var i = 0; i < ai.length; i++) {
                        if ((ai[i].name||'') !== target_name) { has_other = true; break; }
                    }
                    if (!has_other) {
                        var t = (anc.innerText || anc.textContent || '').trim();
                        // 移除選項 label
                        for (var i = 0; i < same_group.length; i++) {
                            var lab = getOptionLabel(same_group[i]);
                            if (lab && t.indexOf(lab) >= 0) t = t.replace(lab, ' ');
                        }
                        return t;
                    }
                    var collected = [];
                    var sib = anc.previousElementSibling;
                    var hops = 0;
                    while (sib && hops < 12) {
                        hops++;
                        var si = sib.querySelectorAll('input[type="radio"], input[type="checkbox"]');
                        if (si.length > 0) break;
                        var t = (sib.innerText || sib.textContent || '').trim();
                        if (t) collected.unshift(t);
                        sib = sib.previousElementSibling;
                    }
                    return collected.join(' ');
                }
                // ── 主流程 ──
                var inputs = document.querySelectorAll(
                    'input[type="radio"], input[type="checkbox"]');
                var name_to_inputs = {};
                for (var i = 0; i < inputs.length; i++) {
                    var n = inputs[i].name || '';
                    if (!n) continue;
                    if (!name_to_inputs[n]) name_to_inputs[n] = [];
                    name_to_inputs[n].push(inputs[i]);
                }
                var results = [];
                for (var name in name_to_inputs) {
                    var grp = name_to_inputs[name];
                    if (grp.length < 2) continue;
                    var correct_opts = [];
                    for (var j = 0; j < grp.length; j++) {
                        if (isMarkedCorrect(grp[j])) {
                            var lab = getOptionLabel(grp[j]);
                            if (lab) correct_opts.push(lab);
                        }
                    }
                    if (correct_opts.length === 0) continue;
                    var qtext = getQuestionText(grp[0], name);
                    if (!qtext) continue;
                    // 清理 qtext 常見前綴
                    qtext = qtext.replace(/^[\s　]*\d+[\s\.、:：]+/, '');
                    qtext = qtext.replace(/\[\s*\d+(?:\.\d+)?\s*\]/g, '');
                    qtext = qtext.replace(/^(單選|多選|是非|複選)\s*配分[：:]\s*/g, '');
                    qtext = qtext.replace(/\s+/g, ' ').trim();
                    if (qtext.length < 5) continue;
                    var qtype = (grp[0].type === 'checkbox') ? 'MC'
                                : (grp.length === 2 ? 'TF' : 'SC');
                    results.push({
                        q: qtext.substring(0, 300),
                        a: correct_opts,
                        type: qtype
                    });
                }
                return results;
            """) or []
        except Exception:
            return []

    def _exam_attempts_exhausted(self):
        """偵測系統是否禁止繼續作答（次數已達上限／作答時間已過）"""
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        texts = []
        try:
            texts.append((self.driver.find_element(By.TAG_NAME, "body").text or "")[:1500])
        except Exception:
            pass
        try:
            for fr in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(fr)
                    texts.append((self.driver.find_element(By.TAG_NAME, "body").text or "")[:1500])
                except Exception:
                    pass
        finally:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass
        all_t = "\n".join(texts)
        STOP_KEYS = [
            "已達測驗次數上限", "已超過作答次數", "測驗次數已達上限", "作答次數已用完",
            "無法再次作答", "已截止", "已結束", "不再開放作答", "測驗已關閉",
            "考試時間已過", "已逾期",
        ]
        for k in STOP_KEYS:
            if k in all_t:
                return True, k
        return False, ""

    def _do_one_exam_attempt(self):
        """執行一次完整作答流程：點進行測驗 → 開始作答 → 答題 → 送出
        回傳 True=送出成功，False=失敗（找不到按鈕等）
        """
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass

        # v1.8.0：等待當前課程的 prefetch 完成（最多 15 秒）
        cur_title = getattr(self, "_current_course_title", "") or ""
        if cur_title:
            status = self._wait_for_prefetch(cur_title, timeout=15)
            if status == "done":
                self.log(f"📚 Prefetch 已備齊「{cur_title}」題庫")
            elif status == "timeout":
                self.log(f"⏳ Prefetch 仍在進行（超過 15 秒），先進測驗")
            elif status in ("miss", "err"):
                self.log(f"⚠ Prefetch 無「{cur_title}」題庫（{status}），靠押題")

        # 找「進行測驗」按鈕（跨 frame）
        btn = self._find_in_any_frame_xpath(
            "//a[contains(normalize-space(.),'進行測驗')] | "
            "//button[contains(normalize-space(.),'進行測驗')] | "
            "//*[contains(@class,'btn') and contains(normalize-space(.),'進行測驗')] | "
            "//*[@onclick and contains(normalize-space(.),'進行測驗')]",
            clickable=True)
        if not btn:
            self.log("⚠ 跨 frame 找不到「進行測驗」按鈕")
            return False

        prev_handles = list(self.driver.window_handles)
        self.log(f"點擊「進行測驗」（tag={btn[0].tag_name}, "
                 f"class={btn[0].get_attribute('class') or ''}）")
        try:
            btn[0].click()
        except Exception:
            self.driver.execute_script("arguments[0].click()", btn[0])
        self._switch_to_new_window_if_any(prev_handles, "測驗視窗")

        # 點「開始作答」
        self._human_sleep(1.5, 0.4)
        start_btn = None
        for _ in range(8):
            start_btn = self._find_in_any_frame_xpath(
                "//a[contains(normalize-space(.),'開始作答')] | "
                "//button[contains(normalize-space(.),'開始作答')] | "
                "//input[(@type='button' or @type='submit') and contains(@value,'開始作答')] | "
                "//*[contains(@class,'btn') and contains(normalize-space(.),'開始作答')]",
                clickable=True)
            if start_btn:
                break
            self._human_sleep(1.5, 0.3)
        if not start_btn:
            self.log("⚠ 找不到「開始作答」按鈕（12 秒內）")
            try:
                self.log(f"目前 URL: {self.driver.current_url}")
            except Exception:
                pass
            return False

        self.log(f"點擊「開始作答」")
        try:
            start_btn[0].click()
        except Exception:
            self.driver.execute_script("arguments[0].click()", start_btn[0])
        time.sleep(3)

        # 答題
        self._auto_answer_exam_questions()

        # 送出
        submit_btn = None
        for _ in range(5):
            submit_btn = self._find_in_any_frame_xpath(
                "//a[contains(normalize-space(.),'送出答案')] | "
                "//button[contains(normalize-space(.),'送出答案')] | "
                "//a[contains(normalize-space(.),'結束測驗')] | "
                "//button[contains(normalize-space(.),'結束測驗')] | "
                "//input[(@type='button' or @type='submit') and "
                "(contains(@value,'送出') or contains(@value,'結束測驗'))]",
                clickable=True)
            if submit_btn:
                break
            self._human_sleep(1.5, 0.3)
        if not submit_btn:
            self.log("⚠ 找不到「送出答案」按鈕")
            return False
        try:
            submit_btn[0].click()
        except Exception:
            self.driver.execute_script("arguments[0].click()", submit_btn[0])
        time.sleep(1)
        try:
            self.driver.switch_to.alert.accept()
            self.log("測驗已送出")
            time.sleep(3)
        except Exception:
            pass
        return True

    def _close_extra_windows(self):
        """關掉除主視窗外其他 window，並切回主視窗"""
        try:
            handles = self.driver.window_handles
            if len(handles) <= 1:
                return
            main_h = handles[0]
            for h in handles[1:]:
                try:
                    self.driver.switch_to.window(h)
                    self.driver.close()
                except Exception:
                    pass
            self.driver.switch_to.window(main_h)
        except Exception:
            pass

    # v1.8.7 bug #6: 敏感欄位 scrub + size cap + rolling delete
    _DUMP_MAX_BYTES = 2 * 1024 * 1024  # 每份 frame html 最多 2MB
    _DUMP_MAX_KEEP  = 5                 # 最多保留最近 5 組 debug_fail_* dump

    # v1.8.7 round-3 #6b：input 敏感欄位改「兩步 attr-parse」
    # 原本 regex 只 match type/name 先於 value 的順序；value-first 的 HTML（IIS / ASP.NET viewstate 常見）會漏洗
    _SENSITIVE_NAME_RE = re.compile(
        r'\b(?:password|passwd|pwd|csrf|token|session|auth|bearer|api[_-]?key|secret|'
        r'jsessionid|phpsessid|access[_-]?token|refresh[_-]?token)\b',
        re.IGNORECASE
    )
    _INPUT_TAG_RE = re.compile(r'<input\b([^>]*)>', re.IGNORECASE)
    _ATTR_RE = re.compile(r'(\w+(?:[-_]\w+)*)\s*=\s*(["\'])([^"\']*)\2', re.IGNORECASE)

    @classmethod
    def _scrub_input_tag(cls, match):
        """掃一個 <input ...> tag 的所有 attrs；若 type 是 hidden/password 且 name 含敏感字，
        把 value= 替換成 [REDACTED]。比 regex 鏈可靠，支援任意 attr 順序。"""
        attrs_raw = match.group(1)
        attrs = {m.group(1).lower(): (m.group(2), m.group(3))
                 for m in cls._ATTR_RE.finditer(attrs_raw)}
        type_val = attrs.get("type", ("", ""))[1].lower()
        name_val = attrs.get("name", ("", ""))[1]
        if type_val not in ("hidden", "password"):
            return match.group(0)
        if not cls._SENSITIVE_NAME_RE.search(name_val):
            return match.group(0)
        if "value" not in attrs:
            return match.group(0)
        # 只替換 value= 那段，保留其他 attr 順序
        q = attrs["value"][0]
        def _repl_value(m):
            if m.group(1).lower() == "value":
                return f'{m.group(1)}={q}[REDACTED]{q}'
            return m.group(0)
        new_attrs = cls._ATTR_RE.sub(_repl_value, attrs_raw)
        return f'<input{new_attrs}>'

    @classmethod
    def _scrub_sensitive_html(cls, html):
        """移除常見敏感欄位（session/token/csrf/password/身分證等）再寫檔。

        ⚠️ best-effort 清洗，非完整 PII scrub — dump 檔仍須當機敏資料處理。
          已知未覆蓋：
            - `type=text` 的 password input（少見但理論可能）
            - 純文字場景的身分證號（沒「身分證」前綴）
            - data-* custom attribute 的 token
            - 非 input 的 form token（如 textarea > viewstate）
        分享 dump 檔前請自行再 grep 敏感字眼。

        v1.8.7 round-2：word-boundary + 限 type=hidden/password，避免誤洗 session_timeout 題目選項
        v1.8.7 round-3 #6b：改兩步 attr-parse 支援 value-first order（IIS/ASP.NET）"""
        if not html:
            return html
        try:
            # (a) input tag — 兩步 parse 支援任意 attr 順序
            html = cls._INPUT_TAG_RE.sub(cls._scrub_input_tag, html)
            # (b) JS var assignment（嚴格 boundary）
            html = re.sub(
                r'(\b(?:token|csrf|sessionId|authorization|bearer|apiKey|secret|accessToken|refreshToken)\b\s*[:=]\s*)(["\'])[^"\']{8,}\2',
                r'\1\2[REDACTED]\2', html, flags=re.IGNORECASE)
            # (c) meta csrf
            html = re.sub(
                r'(<meta[^>]*\bname\s*=\s*["\'](?:csrf-token|x-csrf-token)["\'][^>]*\bcontent\s*=\s*)["\'][^"\']*["\']',
                r'\1"[REDACTED]"', html, flags=re.IGNORECASE)
            # (d) Cookie header in script / comments
            html = re.sub(r'(\bcookie\s*[:=]\s*)(["\'])[^"\']+\2',
                          r'\1\2[REDACTED]\2', html, flags=re.IGNORECASE)
            # (e) 身分證（僅「身分證 字號」語境）
            html = re.sub(
                r'(身分證\s*(?:字號)?\s*[：:]?\s*)([A-Z][12]\d{8})\b',
                r'\1[REDACTED]', html)
        except Exception as e:
            # scrub 失敗仍回原文，但記錄警告供 debug
            try:
                import sys
                print(f"[_scrub_sensitive_html] warning: {e}", file=sys.stderr)
            except Exception:
                pass
        return html

    def _rotate_debug_dumps(self):
        """保留最近 N 組 dump，較舊的刪掉"""
        try:
            files = [f for f in os.listdir(_DATA_DIR)
                     if f.startswith("debug_fail_")]
            # 以 mtime 倒排（新→舊）
            files.sort(key=lambda f: os.path.getmtime(os.path.join(_DATA_DIR, f)),
                       reverse=True)
            # 用「課名+時間戳」的前綴分組，保留最新 N 組
            seen_groups = set()
            to_delete = []
            for f in files:
                # 例：debug_fail_CRPD第2講_20260120_143022_a3_main.html
                m = re.match(r'(debug_fail_.+?_\d{8}_\d{6}_a\d+)', f)
                grp = m.group(1) if m else f
                if grp in seen_groups:
                    continue
                if len(seen_groups) >= self._DUMP_MAX_KEEP:
                    to_delete.append(f)
                    continue
                seen_groups.add(grp)
            # 保留的同組其他檔不刪；只刪超出組別的
            for grp in list(seen_groups)[self._DUMP_MAX_KEEP:]:
                for f in files:
                    if f.startswith(grp):
                        to_delete.append(f)
            for f in to_delete:
                try:
                    os.remove(os.path.join(_DATA_DIR, f))
                except Exception:
                    pass
        except Exception:
            pass

    def _dump_failed_page(self, attempt):
        """v1.8.7：失敗後 dump 整份頁面 source + 截圖，方便分析有沒有藏正解
        v1.8.7 bug #6: 洗敏感欄位 + 每份 ≤2MB + 最多保留最近 5 組"""
        try:
            ts = time.strftime("%Y%m%d_%H%M%S")
            course = (getattr(self, "_current_course_title", "") or "exam")
            safe_course = re.sub(r'[\\/:*?"<>|\s]+', "_", course)[:40]
            base = os.path.join(_DATA_DIR, f"debug_fail_{safe_course}_{ts}_a{attempt}")

            def _write_capped(path, html):
                if not html:
                    return
                scrubbed = self._scrub_sensitive_html(html)
                # v1.8.7 round-2 #6 修：原本切字元會讓 CJK（每字 3 bytes）檔案上限變 3 倍
                #   改成先 encode 成 bytes、截 bytes、再 decode（errors='ignore' 避免切到 UTF-8 多位元組中間）
                encoded = scrubbed.encode('utf-8', errors='ignore')
                if len(encoded) > self._DUMP_MAX_BYTES:
                    truncated_bytes = encoded[:self._DUMP_MAX_BYTES]
                    scrubbed = truncated_bytes.decode('utf-8', errors='ignore') + \
                               "\n\n[... TRUNCATED at 2MB for privacy ...]"
                with open(path, "w", encoding="utf-8") as f:
                    f.write(scrubbed)

            # 主 document
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass
            try:
                _write_capped(base + "_main.html", self.driver.page_source or "")
            except Exception:
                pass

            # 所有 frame 各 dump 一份
            try:
                for i, fr in enumerate(self._all_frames()):
                    try:
                        self.driver.switch_to.default_content()
                        self.driver.switch_to.frame(fr)
                        _write_capped(f"{base}_frame{i}.html",
                                      self.driver.page_source or "")
                    except Exception:
                        pass
            finally:
                try:
                    self.driver.switch_to.default_content()
                except Exception:
                    pass

            # 截圖
            try:
                self.driver.save_screenshot(base + ".png")
            except Exception:
                pass

            # 保留最近 N 組，刪舊
            self._rotate_debug_dumps()
            self.log(f"🔍 失敗頁已存（已洗敏感 / 每份≤2MB）：{os.path.basename(base)}_*.html / .png")
        except Exception as e:
            self.log(f"⚠ dump 失敗：{e}")

    def _auto_take_exam(self, max_retries=10):
        """v1.8.45 押題進化:
        - 抓分數記每次 (attempt, score, answers) → 爬山反推
        - 機率預測:第 3 次起評估,估計最終 < (pass-10) → 跳
        - AI 動態觸發:第 5 次起,預期 10 次內過不了 + 還有未命中題 → AI 補刀
        - 硬上限 10 次,第 11 次破例條件:當前分數 ≥ pass-5
        終止條件(任一觸發):
          1. 通過(pass)
          2. 系統作答上限
          3. 第 3 次起機率預測 < pass-10
          4. 第 10 次失敗且 < pass-5
          5. 第 11 次失敗(破例上限)
        """
        try:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass

            if not self._can_take_exam_now():
                self.log("目前頁面看不到「進行測驗」，先嘗試跳到測驗頁...")
                if not self._try_jump_to_exam_sysbar():
                    self.log("跳測驗頁失敗，放棄自動測驗")
                    return

            # v1.8.20:跳到測驗頁後先確認是否已通過
            if self._exam_already_passed():
                self.log("✓ 此課程測驗已通過，跳過不重做")
                self._stats["courses_passed"] += 1
                return

            self._stats["courses_attempted"] += 1
            self._exam_session_tried = {}
            prev_qa_count = self.qa_bank.count()
            # v1.8.45:爬山策略狀態
            self._attempt_history = []   # [{attempt, score, answers: {qsig: [labels]}, fallback_qsigs: set}]
            self._best_attempt = None
            self._ai_supplement_mode = False   # AI 補刀開關(機率太低觸發)
            # 取及格分(若已抓到,否則預設 75)
            pass_score = self._current_exam_pass if self._current_exam_pass else 75.0
            score_trail = []

            passed = False
            terminate_reason = "達上限"
            attempt = 0
            for attempt in range(1, max_retries + 2):   # 最多 11(破例)
                # ── 第 11 次破例條件:上一次分數必須 ≥ pass-5 ──
                if attempt == max_retries + 1:
                    last_s = score_trail[-1] if score_trail else 0.0
                    if last_s < pass_score - 5:
                        terminate_reason = f"達 {max_retries} 次,當前 {last_s:.0f} < pass-5({pass_score-5:.0f}),不破例"
                        attempt -= 1   # 沒真的跑第 11 次
                        break
                    self.log(f"⏩ 第 {max_retries} 次失敗但分數 {last_s:.0f} ≥ pass-5,破例試第 {attempt} 次")

                self.log(f"━━ 測驗第 {attempt}/{max_retries}{' (破例)' if attempt > max_retries else ''} 次嘗試 ━━")
                self._stats["exam_attempts"] += 1

                # 答題前重置 last_answers 容器(_auto_answer_exam_questions 會填)
                self._last_attempt_answers = {}
                self._last_attempt_fallback_qsigs = set()
                if self._ai_supplement_mode:
                    self.log("🤖 本次啟用 AI 補刀模式(對未命中題優先 AI)")

                ok = self._do_one_exam_attempt()
                if not ok:
                    self.log("此次未送出成功，跳出重考迴圈")
                    terminate_reason = "送出失敗"
                    break

                self._human_sleep(2.5, 0.6)
                result = self._check_exam_result()
                score = self._last_exam_score   # 由 _check_exam_result 設定
                score_show = f"{score:.0f}" if score is not None else "?"
                # 軌跡用 score 或上次值兜底(避免 None 中斷)
                score_trail.append(score if score is not None else (score_trail[-1] if score_trail else 0.0))

                # 紀錄本次 attempt 到 history(爬山用)
                snapshot = {
                    "attempt": attempt,
                    "score": score,
                    "answers": dict(self._last_attempt_answers),
                    "fallback_qsigs": set(self._last_attempt_fallback_qsigs),
                }
                self._attempt_history.append(snapshot)
                # 更新 best
                if score is not None:
                    if self._best_attempt is None or (self._best_attempt.get("score") or -1) < score:
                        self._best_attempt = snapshot
                        self.log(f"⭐ 更新最高分基線:第 {attempt} 次 {score:.0f} 分")

                # ── 通過 ──
                if result == "pass":
                    self.log(f"🎉 第 {attempt} 次:通過!分數 {score_show}")
                    self._stats["exams_passed"] += 1
                    self._stats["courses_passed"] += 1
                    # 過了 → 把每題答案寫進題庫(鎖定正解)
                    self._learn_from_passing_attempt(snapshot)
                    try:
                        n_h, _ = self._harvest_from_result_page()
                        if n_h > 0:
                            self.log(f"📥 過關後 harvester 收割 {n_h} 題進題庫")
                            self._stats["harvested_questions"] += n_h
                    except Exception as _eh:
                        self.log(f"⚠ harvester 例外: {_eh}")
                    passed = True
                    terminate_reason = "通過"
                    break

                if result == "fail":
                    self.log(f"❌ 第 {attempt} 次:未通過,分數 {score_show}")
                    # harvester
                    try:
                        n_h, _ = self._harvest_from_result_page()
                        if n_h > 0:
                            self.log(f"📥 失敗頁 harvester 拔到 {n_h} 題正解")
                            self._stats["harvested_questions"] += n_h
                    except Exception as _eh:
                        self.log(f"⚠ harvester 例外: {_eh}")

                    # 爬山反推:跟前一次分數比,若有上升把擾動題寫題庫
                    self._learn_from_perturbation()

                    # 系統作答上限
                    blocked, key = self._exam_attempts_exhausted()
                    if blocked:
                        self.log(f"🚫 系統限制:{key},停止重考")
                        self._stats["courses_failed"] += 1
                        terminate_reason = f"系統作答上限({key})"
                        break

                    # 機率預測:第 3 次起評估(v1.8.46 修:過濾 None + 用最近 3 次成長率)
                    if attempt >= 3 and score is not None:
                        valid_scores = [s for s in score_trail if s is not None]
                        avg_growth = None
                        if len(valid_scores) >= 3:
                            # 用最近 3 次:跨 2 步的平均成長,避免被第 1 次運氣拖累
                            recent = valid_scores[-3:]
                            avg_growth = (recent[-1] - recent[0]) / 2.0
                        elif len(valid_scores) >= 2:
                            avg_growth = (valid_scores[-1] - valid_scores[0]) / max(1, len(valid_scores) - 1)
                        if avg_growth is not None:
                            remaining = max_retries - attempt   # 還能跑幾次(不含破例)
                            predicted = score + remaining * avg_growth
                            self.log(f"📊 機率預測:當前 {score:.0f},近 3 次平均 +{avg_growth:.1f}/次,剩 {remaining} 次,估最終 {predicted:.0f} (pass {pass_score:.0f})")
                            if predicted < pass_score - 10:
                                self.log(f"📉 估最終 {predicted:.0f} < pass-10({pass_score-10:.0f}) → 跳本門")
                                self._stats["courses_failed"] += 1
                                terminate_reason = f"機率太低(估 {predicted:.0f} < {pass_score-10:.0f})"
                                break
                            # AI 補刀觸發:第 5 次起,估最終 < pass + 還有未命中題 + 有 Gemini key
                            if (attempt >= 5 and not self._ai_supplement_mode
                                    and self._gemini and predicted < pass_score
                                    and self._last_attempt_fallback_qsigs):
                                self.log(f"🤖 AI 補刀啟動:估最終 {predicted:.0f} < pass {pass_score:.0f},還有 {len(self._last_attempt_fallback_qsigs)} 題未命中")
                                self._ai_supplement_mode = True

                    # 第 10 次失敗且當前 < pass-5 → 不破例
                    if attempt == max_retries:
                        if score is None or score < pass_score - 5:
                            self.log(f"🛑 達 {max_retries} 次,當前 {score_show} < pass-5,放棄")
                            self._stats["courses_failed"] += 1
                            terminate_reason = f"達 {max_retries} 次,分數 {score_show} 距 pass 太遠"
                            break
                        # 否則進入下一個迴圈嘗試(第 11 次破例)

                    # 第 1 次失敗 dump
                    if attempt == 1:
                        try:
                            self._dump_failed_page(attempt)
                        except Exception:
                            pass

                    # 重新跳測驗頁
                    self._close_extra_windows()
                    self._human_sleep(2.0, 0.5)
                    if not self._try_jump_to_exam_sysbar():
                        self.log("無法重新跳測驗頁，停止重考")
                        self._stats["courses_failed"] += 1
                        terminate_reason = "無法重跳測驗頁"
                        break
                else:
                    self.log("無法判斷結果(unknown),保守視為完成")
                    terminate_reason = "結果頁無法判讀"
                    break

            # 收尾
            grown = self.qa_bank.count() - prev_qa_count
            total_tried = sum(len(v) for v in self._exam_session_tried.values())
            trail_str = "→".join(f"{s:.0f}" for s in score_trail) if score_trail else "—"
            self.log(f"📊 本門終止:[{terminate_reason}] 第 {attempt} 次,分數軌跡 {trail_str},題庫 +{grown},cycling 排除 {total_tried}")
            if not passed:
                self.log(f"💔 本門未過關")

            self._close_extra_windows()
        except Exception as e:
            self.log(f"自動測驗失敗: {e}")
            try:
                self._close_extra_windows()
            except Exception:
                pass

    # ── v1.8.45:爬山輔助 ────────────────────────────────────

    def _learn_from_passing_attempt(self, snapshot):
        """v1.8.45:通過時,把每題答案寫進題庫(鎖定正解)。
        snapshot.answers: {qsig: [picked_labels]} 但我們需要 qtext 作為 key。
        實作:題庫 add 走 qtext;這裡靠 _last_attempt_q_by_sig 對應(_auto_answer 紀錄)。
        """
        try:
            q_by_sig = getattr(self, "_last_attempt_q_by_sig", {}) or {}
            type_by_sig = getattr(self, "_last_attempt_type_by_sig", {}) or {}
            n = 0
            for qsig, labels in (snapshot.get("answers") or {}).items():
                qtext = q_by_sig.get(qsig, "")
                if not qtext or not labels:
                    continue
                qtype = type_by_sig.get(qsig, "SC")
                # add 預設 overwrite=True → 覆寫(高信任度)
                self.qa_bank.add(qtext, labels, qtype=qtype,
                                 course=getattr(self, "_current_course_title", ""))
                n += 1
            if n > 0:
                self.qa_bank.save()
                self.log(f"⭐ 通過解鎖:寫入 {n} 題正解到題庫")
        except Exception as e:
            self.log(f"⚠ _learn_from_passing_attempt 例外: {e}")

    def _learn_from_perturbation(self):
        """v1.8.45:失敗後,跟上一次比較分數差。
        - 分數↑ → 本次擾動的題答案可能對 → 候選地寫進題庫(low confidence,只寫 qsig 還沒有 a 的題)
        - 分數↓ → 上一次擾動的題答案可能對(已過保留邏輯,這裡不主動還原)
        - 分數=  → 不動
        為避免誤鎖,只在「比 best 還高」時才寫入。
        """
        try:
            hist = self._attempt_history
            if len(hist) < 2:
                return
            cur = hist[-1]
            best_before = max(
                (h for h in hist[:-1] if h.get("score") is not None),
                key=lambda h: h["score"],
                default=None,
            )
            if cur.get("score") is None or best_before is None:
                return
            cur_s = cur["score"]; prev_s = best_before["score"]
            delta = cur_s - prev_s
            if delta <= 0:
                return
            # 找本次相比 best_before 變化的 fallback 題(答案不同)
            q_by_sig = getattr(self, "_last_attempt_q_by_sig", {}) or {}
            type_by_sig = getattr(self, "_last_attempt_type_by_sig", {}) or {}
            cur_ans = cur.get("answers") or {}
            prev_ans = best_before.get("answers") or {}
            n_lock = 0
            for qsig in cur.get("fallback_qsigs") or set():
                cur_labs = cur_ans.get(qsig) or []
                prev_labs = prev_ans.get(qsig) or []
                if set(cur_labs) == set(prev_labs):
                    continue   # 沒改答案
                qtext = q_by_sig.get(qsig, "")
                if not qtext:
                    continue
                # 只寫 a 還空的 entry(不覆寫 harvester 拔到的高信任正解)
                existing = self.qa_bank.find(qtext)
                if existing and existing.get("a"):
                    continue
                qtype = type_by_sig.get(qsig, "SC")
                self.qa_bank.add(qtext, cur_labs, qtype=qtype,
                                 course=getattr(self, "_current_course_title", ""))
                n_lock += 1
            if n_lock > 0:
                self.qa_bank.save()
                self.log(f"📈 分數 {prev_s:.0f}→{cur_s:.0f} (+{delta:.0f}),爬山候選鎖定 {n_lock} 題答案")
        except Exception as e:
            self.log(f"⚠ _learn_from_perturbation 例外: {e}")

    # ── 答題：題庫優先，押題 fallback ─────────────────────

    def _get_option_label(self, input_el):
        """取 radio/checkbox 對應的選項文字"""
        # 1. 優先 <label for="id">
        try:
            iid = input_el.get_attribute("id")
            if iid:
                lab = self.driver.find_element(By.CSS_SELECTOR, f"label[for='{iid}']")
                t = (lab.text or "").strip()
                if t:
                    return t
        except Exception:
            pass
        # 2. 父層 <label>...<input>...文字</label>
        try:
            parent = input_el.find_element(By.XPATH, "./parent::*")
            if (parent.tag_name or "").lower() == "label":
                t = (parent.text or "").strip()
                if t:
                    return t
        except Exception:
            pass
        # 3. 緊鄰的下一個文字節點 / 兄弟元素
        try:
            sib = input_el.find_element(By.XPATH,
                "./following-sibling::*[1] | ./following::text()[1]/parent::*")
            t = (sib.text or "").strip()
            if t:
                return t
        except Exception:
            pass
        # 4. JS 取下一個 sibling text node
        try:
            t = self.driver.execute_script(
                "var n=arguments[0].nextSibling; "
                "while(n && n.nodeType===3 && !n.nodeValue.trim()) n=n.nextSibling; "
                "return n? (n.textContent||n.nodeValue||'').trim() : '';",
                input_el)
            if t:
                return t.strip()
        except Exception:
            pass
        return ""

    def _cleanup_qtext(self, text):
        """v1.8.7：移除題型 / 配分 / 題號 / whitespace（題庫 key 用）
        v1.8.12：強化前綴切除 — reverse DOM walk 常把考試頁 chrome（測驗資訊/題數/作答區/
        剩下時間）以及「上一題答案殘留」一起吃進來。改用：找出文字中最後出現的「N.」或「N、」
        題號（後面接空白），從該題號之後當作真題目。
        """
        if not text:
            return ""
        try:
            # 1) 切除考試頁 chrome 前綴
            for marker in ("作答區", "剩下時間", "頁數", "測驗資訊"):
                idx = text.rfind(marker)
                if idx >= 0:
                    # 取 marker 之後
                    text = text[idx + len(marker):]
            # 2) 找最後一個「N. 」或「N、」題號 — 切到題號之後
            #    匹配如 "1. 題目" / "10、題目" / " 6. 身心障礙..."
            #    限制 N <= 3 位數，避免吃到題目中的年份「2008.」
            matches = list(re.finditer(r'(?:^|\s)(\d{1,3})\s*[.\．、]\s+', text))
            if matches:
                last = matches[-1]
                text = text[last.end():]
            text = re.sub(r'(單選題?|多選題?|複選題?|是非題?)', '', text)
            text = re.sub(r'配分\s*[：:]?\s*\[?[\d\.]+\]?\s*分?', '', text)
            text = re.sub(r'\[\s*\d+(?:\.\d+)?\s*\]\s*分?', '', text)
            text = re.sub(r'^[\s　]*[（(\[【]?[\s　]*\d+[\s　]*[)）\]】．]?[、\.：:]?[\s　]*', '', text.strip())
            text = re.sub(r'[\s　\n\r]+', ' ', text).strip()
        except Exception:
            pass
        return text

    def _get_question_text(self, input_el):
        """v1.8.7：終極版 — 從 input 往前 DOM-walk 收集文字，遇到上一題 input 停
        痞客幫 / E等公務園 的試題結構通常是：
            <tr>題目1...</tr>
            <tr><input name=A1></tr>...
            <tr>題目2...</tr>
            <tr><input name=A2></tr>...
        共同 ancestor 是整張 table → 之前的 self mode 會誤抓全 table 文字。
        改用「reverse document order traversal」：從 input 往前走，
        收集所有 text node，遇到不同題的 input 就停。
        """
        target_name = input_el.get_attribute("name") or ""
        if not target_name:
            return ""

        # 策略 A：reverse DOM walk（主力）
        try:
            text = self.driver.execute_script(r"""
                var input = arguments[0];
                var target_name = arguments[1];
                var doc = input.ownerDocument || document;
                function prevNode(node) {
                    if (node.previousSibling) {
                        var n = node.previousSibling;
                        while (n.lastChild) n = n.lastChild;
                        return n;
                    }
                    return node.parentNode;
                }
                var collected = [];
                var node = input;
                var hops = 0;
                while (node && hops < 2000) {
                    hops++;
                    node = prevNode(node);
                    if (!node) break;
                    if (node === doc.body || node === doc.documentElement) break;
                    if (node.nodeType === 1) {
                        if (node.tagName === 'INPUT') {
                            var tt = (node.type || '').toLowerCase();
                            if ((tt === 'radio' || tt === 'checkbox') &&
                                (node.name || '') !== target_name) {
                                break;  // 邊界：上一題 input
                            }
                        } else if (node.tagName === 'BUTTON' || node.tagName === 'SELECT' ||
                                   node.tagName === 'TEXTAREA') {
                            // 表單控件不算題目文字
                        }
                    } else if (node.nodeType === 3) {
                        var txt = (node.nodeValue || '').trim();
                        if (txt.length >= 2) collected.unshift(txt);
                    }
                }
                return collected.join(' ').replace(/\s+/g, ' ').trim();
            """, input_el, target_name)
            if text and len(text) >= 5:
                cleaned = self._cleanup_qtext(text)
                if cleaned and len(cleaned) >= 5:
                    return cleaned
        except Exception as e:
            try:
                self.log(f"⚠ _get_question_text 策略A 例外: {type(e).__name__}: {str(e)[:120]}")
            except Exception:
                pass

        # 策略 B（fallback）：原 v1.8.1 ancestor + sibling
        try:
            result = self.driver.execute_script("""
                var input = arguments[0];
                var target_name = arguments[1];
                var all_doc_inputs = document.querySelectorAll(
                    'input[type="radio"], input[type="checkbox"]');
                var same_group = [];
                for (var i = 0; i < all_doc_inputs.length; i++) {
                    if ((all_doc_inputs[i].name || '') === target_name) {
                        same_group.push(all_doc_inputs[i]);
                    }
                }
                if (same_group.length === 0) return null;
                var anc = input;
                while (anc && anc.tagName !== 'BODY') {
                    var contains_all = true;
                    for (var i = 0; i < same_group.length; i++) {
                        if (!anc.contains(same_group[i])) {
                            contains_all = false;
                            break;
                        }
                    }
                    if (contains_all) break;
                    anc = anc.parentElement;
                }
                if (!anc) return null;
                var all_inputs = anc.querySelectorAll(
                    'input[type="radio"], input[type="checkbox"]');
                var has_other = false;
                for (var i = 0; i < all_inputs.length; i++) {
                    if ((all_inputs[i].name||'') !== target_name) {
                        has_other = true;
                        break;
                    }
                }
                if (!has_other) {
                    return {mode:'self', text: (anc.innerText||anc.textContent||'').trim()};
                }
                var collected = [];
                var sib = anc.previousElementSibling;
                var hops = 0;
                while (sib && hops < 12) {
                    hops++;
                    var sib_inputs = sib.querySelectorAll(
                        'input[type="radio"], input[type="checkbox"]');
                    if (sib_inputs.length > 0) break;
                    var t = (sib.innerText||sib.textContent||'').trim();
                    if (t) collected.unshift(t);
                    sib = sib.previousElementSibling;
                }
                if (collected.length === 0 && anc.parentElement) {
                    var psib = anc.parentElement.previousElementSibling;
                    var hops2 = 0;
                    while (psib && hops2 < 6) {
                        hops2++;
                        var sib_inputs = psib.querySelectorAll(
                            'input[type="radio"], input[type="checkbox"]');
                        if (sib_inputs.length > 0) break;
                        var t = (psib.innerText||psib.textContent||'').trim();
                        if (t) collected.unshift(t);
                        psib = psib.previousElementSibling;
                    }
                }
                return {mode:'sibling', text: collected.join(' ')};
            """, input_el, target_name)

            if not result or not result.get("text"):
                return ""
            text = result["text"]
            mode = result.get("mode", "sibling")

            if mode == "self":
                try:
                    safe_name = target_name.replace("'", "\\'")
                    for inp in self.driver.find_elements(
                            By.CSS_SELECTOR, f"input[name='{safe_name}']"):
                        lab = self._get_option_label(inp)
                        if lab and lab in text:
                            text = text.replace(lab, " ")
                except Exception:
                    pass
            return self._cleanup_qtext(text)
        except Exception:
            return ""

    @staticmethod
    def _texts_match(option_text, answer_text):
        """v1.8.14：選項文字 vs 答案文字 — 模糊比對（短字面 + 長相似度都過）
        策略：
          (1) normalize 後完全相等
          (2) TF 等價字 — 對↔是↔√、錯↔否↔×
          (3) 任一方為另一方 substring（短至 2 字也接受）
          (4) difflib ratio >= 0.7（中長文字寬容打字差異）
        """
        if not option_text or not answer_text:
            return False
        a = QABank.normalize(option_text)
        b = QABank.normalize(answer_text)
        if not a or not b:
            return False
        if a == b:
            return True
        # TF 等價組
        TF_TRUE = {"對", "是", "正確", "true", "T", "Y", "√", "v", "V", "○"}
        TF_FALSE = {"錯", "否", "錯誤", "不對", "false", "F", "N", "X", "×", "✗"}
        if (a in TF_TRUE and b in TF_TRUE) or (a in TF_FALSE and b in TF_FALSE):
            return True
        # substring（門檻降到 2 字）
        if len(b) >= 2 and b in a:
            return True
        if len(a) >= 2 and a in b:
            return True
        # difflib ratio
        try:
            import difflib
            if len(a) >= 4 and len(b) >= 4:
                if difflib.SequenceMatcher(None, a, b).ratio() >= 0.7:
                    return True
        except Exception:
            pass
        return False

    def _switch_to_question_frame(self):
        """v1.8.7：點完「開始作答」後，主動切到含 radio/checkbox 的 frame。
        在主 document 沒有 input 時，逐個 frame 搜尋。回傳是否有切過。"""
        try:
            self.driver.switch_to.default_content()
        except Exception:
            return False
        try:
            n_main = len(self.driver.find_elements(By.CSS_SELECTOR,
                "input[type='radio'], input[type='checkbox']"))
            if n_main >= 2:
                return False  # 主 document 已有，不需切
        except Exception:
            pass
        try:
            for fr in self._all_frames():
                try:
                    self.driver.switch_to.default_content()
                    self.driver.switch_to.frame(fr)
                    n_in = len(self.driver.find_elements(By.CSS_SELECTOR,
                        "input[type='radio'], input[type='checkbox']"))
                    if n_in >= 2:
                        return True
                    # 嵌套
                    for inner in self._all_frames():
                        try:
                            self.driver.switch_to.frame(inner)
                            n_in2 = len(self.driver.find_elements(By.CSS_SELECTOR,
                                "input[type='radio'], input[type='checkbox']"))
                            if n_in2 >= 2:
                                return True
                            self.driver.switch_to.parent_frame()
                        except Exception:
                            try:
                                self.driver.switch_to.parent_frame()
                            except Exception:
                                pass
                except Exception:
                    pass
        finally:
            pass
        # 全部沒找到 → 回 default
        try:
            self.driver.switch_to.default_content()
        except Exception:
            pass
        return False

    def _auto_answer_exam_questions(self):
        """v1.8.7：題庫 + 押題（含 cycling 不重複）
        - 主動切 frame
        - 等 input 載入後再抓
        - 抓不到題目文字時 dump 第一題 outerHTML 至 LOG（debug）
        """
        try:
            # v1.8.7：先切到含 input 的 frame
            switched = self._switch_to_question_frame()
            if switched:
                self.log("🔀 切換到含試題 input 的 frame")

            # 1) 等 input 載入 + 收集（最多重試 4 次）
            inputs = []
            for _try in range(4):
                inputs = self.driver.find_elements(By.CSS_SELECTOR,
                    "input[type='radio']:not([disabled]), "
                    "input[type='checkbox']:not([disabled])")
                if inputs:
                    break
                self._human_sleep(1.5, 0.4)
            groups = {}        # name -> [(input_el, label_text, type)]
            for inp in inputs:
                name = inp.get_attribute("name") or ""
                itype = (inp.get_attribute("type") or "").lower()
                if not name:
                    continue
                lab = self._get_option_label(inp)
                groups.setdefault(name, []).append((inp, lab, itype))

            n_total    = len(groups)
            n_db_hit   = 0
            n_opt_hit  = 0  # v1.8.9: 選項池直配命中
            n_ai_hit   = 0  # v1.8.8：Gemini AI 命中
            n_fallback = 0
            # v1.8.45:本次 attempt 答題紀錄(爬山用,_auto_take_exam 讀)
            self._last_attempt_q_by_sig = {}    # qsig -> qtext
            self._last_attempt_type_by_sig = {} # qsig -> "SC"/"MC"/"TF"
            # _last_attempt_answers / _last_attempt_fallback_qsigs 由 _auto_take_exam 預設 init
            if not hasattr(self, "_last_attempt_answers"):
                self._last_attempt_answers = {}
            if not hasattr(self, "_last_attempt_fallback_qsigs"):
                self._last_attempt_fallback_qsigs = set()
            _qsig_by_name = {}   # name -> qsig (sweep 用)
            # v1.8.45 AI 補刀:取上一輪 fallback qsigs(本次優先用 AI)
            _prev_fallback_qsigs = set()
            if (getattr(self, "_ai_supplement_mode", False)
                    and getattr(self, "_attempt_history", None)):
                _prev_fallback_qsigs = (self._attempt_history[-1].get("fallback_qsigs") or set())
                if _prev_fallback_qsigs:
                    self.log(f"🤖 AI 補刀:本次對 {len(_prev_fallback_qsigs)} 題(上輪 fallback) 優先 AI")

            # v1.8.9: 選項池直配 — 用該課程所有已知正解建 set
            # v1.8.11: 加診斷 log，pool 為空 / 課程名不匹配時也告知
            _course_hint = getattr(self, "_current_course_title", "")
            correct_pool = self.qa_bank.find_correct_options(course_hint=_course_hint)
            if correct_pool:
                self.log(f"🎯 選項池備妥：「{_course_hint[:30]}」共 {len(correct_pool)} 個已知正解選項")
            else:
                # 診斷：列出 qa_bank 既有 course 名，方便比對
                _all_pool = self.qa_bank.find_correct_options(course_hint="")
                _courses_in_bank = sorted({(v.get("course") or "")[:50]
                                           for v in self.qa_bank.data.values()
                                           if v.get("course")})
                self.log(f"⚠ 選項池空：course_hint=「{_course_hint[:40]}」 "
                         f"題庫總正解={len(_all_pool)}")
                if _courses_in_bank:
                    self.log(f"   題庫含 {len(_courses_in_bank)} 門課："
                             f"{' | '.join(_courses_in_bank[:3])}{'...' if len(_courses_in_bank)>3 else ''}")

            # v1.8.7：debug dump — 第一次出現 empty qtext 時記錄 input HTML
            _dumped = False
            def _debug_dump_input(inp_el):
                nonlocal _dumped
                if _dumped:
                    return
                _dumped = True
                try:
                    html = self.driver.execute_script(
                        "var e=arguments[0]; var p=e; var ps=[]; "
                        "for(var i=0;i<4;i++){if(!p||p.tagName==='BODY')break; "
                        "ps.push((p.outerHTML||'').substring(0,300)); p=p.parentElement;} "
                        "return ps.join('\\n----\\n');", inp_el)
                    self.log(f"🔍 DEBUG（首題 outerHTML 4 層）：\n{html[:1200]}")
                except Exception as e:
                    self.log(f"🔍 DEBUG dump 失敗: {e}")

            for name, opts in groups.items():
                if not opts:
                    continue

                # 2) 取題目文字（用第一個 input 往上找）
                qtext = self._get_question_text(opts[0][0])
                # v1.8.45:算 qsig + 推測 qtype 給 sweep 用
                qsig = self._options_signature(opts, qtext=qtext or "")
                qtype_inferred = ("MC" if (opts and opts[0][2] == "checkbox")
                                  else ("TF" if len(opts) == 2 else "SC"))
                if qsig:
                    _qsig_by_name[name] = qsig
                    self._last_attempt_q_by_sig[qsig] = qtext or ""
                    self._last_attempt_type_by_sig[qsig] = qtype_inferred
                # v1.8.45 AI 補刀:若該題上輪是 fallback 題且補刀模式已啟用,跳過題庫命中強制走 AI
                _use_ai_first = (qsig and qsig in _prev_fallback_qsigs and self._gemini)
                hit = None if _use_ai_first else (self.qa_bank.find(qtext) if qtext else None)

                if hit:
                    n_db_hit += 1
                    # 3) 從題庫答案文字匹配選項
                    ans_list = hit.get("a") or []
                    qtype = hit.get("type", "SC")
                    clicked_any = False
                    for inp, lab, itype in opts:
                        for ans in ans_list:
                            if self._texts_match(lab, ans):
                                try:
                                    self.driver.execute_script(
                                        "arguments[0].click()", inp)
                                    clicked_any = True
                                    if itype == "radio":
                                        break
                                except Exception:
                                    pass
                        if clicked_any and itype == "radio":
                            break
                    qshow = qtext[:60] + ("..." if len(qtext) > 60 else "")
                    if not clicked_any:
                        # 答案文字配不到任何選項 → 退回押題
                        self._fallback_answer_group(opts, qtext=qtext)
                        self.log(f"📚→❓ 題庫有但選項配不到：{qshow}")
                    else:
                        self.log(f"📚 題庫命中：{qshow}")
                else:
                    # v1.8.11: 診斷 — 為什麼 AI 沒被呼叫
                    if not qtext:
                        self.log(f"⚠ AI 跳過：抓不到題目文字（name={name}）→ 走 pool/押題")
                    elif not self._gemini:
                        self.log(f"⚠ AI 跳過：Gemini 未啟用或已停用 → 走 pool/押題")
                    # v1.8.8：題庫 miss → 嘗試 Gemini AI 答題
                    if qtext and self._gemini:
                        ai_matched = self._ask_ai(qtext, opts)
                        if ai_matched:
                            itype0 = opts[0][2]
                            clicked_any = False
                            if itype0 == "radio":
                                try:
                                    self.driver.execute_script(
                                        "arguments[0].click()", ai_matched[0][0])
                                    clicked_any = True
                                except Exception:
                                    pass
                            else:
                                for i2, _l2, _t2 in opts:
                                    try:
                                        if i2.is_selected():
                                            self.driver.execute_script(
                                                "arguments[0].click()", i2)
                                    except Exception:
                                        pass
                                for inp_m, _l, _t in ai_matched:
                                    try:
                                        self.driver.execute_script(
                                            "arguments[0].click()", inp_m)
                                        clicked_any = True
                                    except Exception:
                                        pass
                            if clicked_any:
                                n_ai_hit += 1
                                mlabs = " | ".join(
                                    [(l[:25] + "..." if len(l) > 25 else l)
                                     for _i, l, _t in ai_matched])
                                qshow2 = qtext[:50] + ("..." if len(qtext) > 50 else "")
                                self.log(f"🤖 AI答題：{qshow2} → {mlabs}")
                                try:
                                    qtype_ai = ("MC" if opts[0][2] == "checkbox"
                                                else ("TF" if len(opts) == 2 else "SC"))
                                    self.qa_bank.add(
                                        qtext,
                                        [l for _i, l, _t in ai_matched],
                                        qtype=qtype_ai,
                                        course=getattr(self, "_current_course_title", ""))
                                    self.qa_bank.save()
                                except Exception:
                                    pass
                                continue   # 跳過 fallback

                    # v1.8.9: 選項池直配（題庫 miss + AI miss 後）
                    if correct_pool:
                        pool_matched = []
                        for inp, lab, itype in opts:
                            lab_norm = QABank.normalize(lab)
                            if not lab_norm:
                                continue
                            # 三層比對：(1) 完全相等 (2) 互為子字串≥6字 (3) difflib≥0.85
                            matched = False
                            if lab_norm in correct_pool:
                                matched = True
                            elif len(lab_norm) >= 6:
                                for p in correct_pool:
                                    if len(p) >= 6 and (lab_norm in p or p in lab_norm):
                                        matched = True
                                        break
                            if not matched:
                                try:
                                    import difflib
                                    for p in correct_pool:
                                        if len(p) >= 6 and len(lab_norm) >= 6:
                                            if difflib.SequenceMatcher(
                                                    None, lab_norm, p).ratio() >= 0.85:
                                                matched = True
                                                break
                                except Exception:
                                    pass
                            if matched:
                                pool_matched.append((inp, lab, itype))

                        # v1.8.11: pool 有但全選項都沒中 → 印選項與 pool 樣本診斷
                        if not pool_matched and qtext:
                            _opt_show = " | ".join(
                                [(l[:18] + "..." if len(l) > 18 else l)
                                 for _i, l, _t in opts if l][:4])
                            _pool_sample = list(correct_pool)[:3]
                            _pool_show = " | ".join(
                                [(p[:18] + "..." if len(p) > 18 else p)
                                 for p in _pool_sample])
                            self.log(f"🔎 pool 未中：選項=[{_opt_show}] "
                                     f"vs pool 樣本=[{_pool_show}]")

                        if pool_matched:
                            itype0 = opts[0][2] if opts else "radio"
                            clicked_pool = False
                            if itype0 == "radio":
                                try:
                                    self.driver.execute_script(
                                        "arguments[0].click()", pool_matched[0][0])
                                    clicked_pool = True
                                except Exception:
                                    pass
                            else:
                                # MC: 取消所有已勾 → 勾所有命中
                                for i2, _l2, _t2 in opts:
                                    try:
                                        if i2.is_selected():
                                            self.driver.execute_script(
                                                "arguments[0].click()", i2)
                                    except Exception:
                                        pass
                                for inp_m, _lm, _tm in pool_matched:
                                    try:
                                        self.driver.execute_script(
                                            "arguments[0].click()", inp_m)
                                        clicked_pool = True
                                    except Exception:
                                        pass
                            if clicked_pool:
                                n_opt_hit += 1
                                mlabs = " | ".join(
                                    [(l[:25] + "..." if len(l) > 25 else l)
                                     for _i, l, _t in pool_matched])
                                qshow_p = qtext[:50] + ("..." if len(qtext) > 50 else "")
                                self.log(f"🎯 選項池命中：{qshow_p} → {mlabs}")
                                continue  # 跳過 fallback

                    n_fallback += 1
                    # v1.8.45:標記為 fallback 題(爬山追蹤用)
                    if qsig:
                        self._last_attempt_fallback_qsigs.add(qsig)
                    self._fallback_answer_group(opts, qtext=qtext)
                    qshow = qtext[:60] + ("..." if len(qtext) > 60 else "")
                    if qtext:
                        self.log(f"❓ 題庫無：{qshow}")
                        # 記錄到 missed 字典：題目 → {options, course}
                        try:
                            opt_labels = [lab for _i, lab, _t in opts if lab]
                            key = QABank.normalize(qtext)
                            if key and key not in self._missed_questions:
                                self._missed_questions[key] = {
                                    "q": qtext[:300],
                                    "options": opt_labels,
                                    "course": getattr(self, "_current_course_title", ""),
                                    "type": ("MC" if (opts and opts[0][2] == "checkbox")
                                             else ("TF" if len(opts) == 2 else "SC")),
                                    "a": [],   # 待人工填
                                }
                        except Exception:
                            pass
                    else:
                        self.log(f"❓ 抓不到題目文字（name={name}）")

            # v1.8.45:答題完成 sweep — 抓每題目前 selected 的 labels(爬山反推用)
            try:
                for name, opts in groups.items():
                    qsig = _qsig_by_name.get(name) or ""
                    if not qsig or not opts:
                        continue
                    picked = []
                    for inp, lab, _t in opts:
                        try:
                            if inp.is_selected() and lab:
                                picked.append(lab)
                        except Exception:
                            pass
                    self._last_attempt_answers[qsig] = picked
            except Exception:
                pass

            self.log(f"答題完成（{n_total} 題：題庫 {n_db_hit} / 選項池 {n_opt_hit} / AI {n_ai_hit} / 押題 {n_fallback}）")
            try:
                self._stats["questions_total"] += n_total
                self._stats["db_hits"]         += n_db_hit
                self._stats["option_hits"]     += n_opt_hit
                self._stats["ai_hits"]         += n_ai_hit
                self._stats["fallbacks"]       += n_fallback
            except Exception:
                pass
        except Exception as e:
            self.log(f"自動答題失敗: {e}")

    @staticmethod
    def _options_signature(opts, qtext=""):
        """v1.8.7：用選項標籤組合做 key（跨 attempt 穩定，題目順序、id 都會變）
        v1.8.7 bug #3：加入 qtext。原本只 hash labels → TF 題全部共用「對/錯」signature，
        一題試過「對」後所有 TF 題的 tried set 都卡死，cycling 等於沒用。
        v1.8.7 round-2 補：當 qtext normalize 為空（只含標點或抓漏時），
        用 input name 當 salt，避免退化回 labels-only 讓 TF 題又共撞。"""
        labs = sorted([(QABank.normalize(lab) or "")
                       for _i, lab, _t in opts if lab])
        if not labs:
            return ""
        q_norm = QABank.normalize(qtext or "")
        if not q_norm:
            # v1.8.7 round-3 #3：三層 fallback salt，避免 name 也空時退化回 labels-only 全題共撞
            # 1) input name → 2) input id → 3) 前 3 個 option 的 value attr tuple
            salt = ""
            try:
                first_inp = opts[0][0] if opts else None
                if first_inp:
                    salt = (first_inp.get_attribute("name") or "").strip()
                    if not salt:
                        salt = (first_inp.get_attribute("id") or "").strip()
                    if not salt and opts:
                        # 最後一道：用前 3 個 option value 當 salt（通常 value=A/B/C 或答案內容）
                        vals = []
                        for o in opts[:3]:
                            try:
                                vals.append(o[0].get_attribute("value") or "")
                            except Exception:
                                vals.append("")
                        salt = "|".join(vals)
            except Exception:
                salt = ""
            q_norm = "NO_QTEXT_" + salt
        try:
            import hashlib
            combined = (q_norm + "\u0001" + "\u0001".join(labs)).encode("utf-8")
            h = hashlib.md5(combined).hexdigest()[:16]
            return h
        except Exception:
            return (q_norm[:40] + "|" + "|".join(labs))[:160]

    # 「以上皆是」/「以上皆非」常見變體
    _ALL_ABOVE_KEYS  = ("以上皆是", "以上皆對", "以上皆正確", "全部皆是",
                        "上述皆是", "上述皆對", "以上都是", "以上都對",
                        "上述都對", "前述皆是", "all of the above")
    _NONE_ABOVE_KEYS = ("以上皆非", "以上皆錯", "以上皆無", "上述皆非",
                        "以上都不是", "上述都不對", "前述皆非",
                        "none of the above")
    # 絕對化字眼 — 出現在選項裡通常是錯的；出現在 TF 題目通常答否
    # v1.8.7 bug #7：中文類用子字串比對、英文類需 \b word boundary 避免誤觸
    # 例：`every` 子字串會命中 `everyone / everywhere`；`must` 命中 `must-have`；`all` 命中 `allergy/install`
    _ABSOLUTE_KEYS_CJK = ("一定", "絕對", "必定", "必然", "永遠", "從不",
                          "絕不", "完全", "100%", "百分之百", "毫無例外",
                          "所有的", "任何")
    _ABSOLUTE_KEYS_EN  = ("every", "always", "never",
                          "absolutely", "definitely", "must")

    @classmethod
    def _is_all_above(cls, label):
        if not label:
            return False
        s = (label or "").lower().replace(" ", "")
        return any(k.lower().replace(" ", "") in s for k in cls._ALL_ABOVE_KEYS)

    @classmethod
    def _is_none_above(cls, label):
        if not label:
            return False
        s = (label or "").lower().replace(" ", "")
        return any(k.lower().replace(" ", "") in s for k in cls._NONE_ABOVE_KEYS)

    @classmethod
    def _has_absolute_word(cls, text):
        """含「一定 / 絕對 / 必定 / 永遠」等絕對化字眼 → 通常是出題者埋的坑
        v1.8.7 bug #7：中文子字串 OK、英文需 word boundary 避免誤觸 everyone/must-have"""
        if not text:
            return False
        s_lower = text.lower()
        s_no_space = s_lower.replace(" ", "")
        # 中文：子字串比對
        for k in cls._ABSOLUTE_KEYS_CJK:
            if k.lower().replace(" ", "") in s_no_space:
                return True
        # 英文：word boundary
        for k in cls._ABSOLUTE_KEYS_EN:
            if re.search(r'\b' + re.escape(k) + r'\b', s_lower):
                return True
        return False

    @staticmethod
    def _question_polarity(qtext):
        """v1.8.7：題目語意極性
            'neg' = 找錯的（下列何者錯誤 / 為非 / 不正確 / 何者錯）
            'pos' = 找對的（下列何者正確 / 為是 / 何者對 / 為真）
            ''    = 不確定（含抓不到題目文字）
        當 polarity = 'neg'：含絕對化字眼的選項 = 答案
        當 polarity = 'pos'：含絕對化字眼的選項 = 排除
        """
        if not qtext:
            return ""
        s = qtext.replace(" ", "").replace("　", "")
        NEG = ("錯誤", "為非", "何者非", "不正確", "不對", "何者錯",
               "不是", "何者誤", "錯的", "不可", "不能", "下列哪一項不",
               "何者不屬", "何者非屬", "incorrect", "wrong", "false",
               "not true", "not correct")
        POS = ("正確", "為是", "為真", "何者對", "何者是", "正確的",
               "屬於", "下列何者屬", "下列哪一項是", "true", "correct")
        # NEG 詞彙較強烈，先比對
        for k in NEG:
            if k in s:
                return "neg"
        for k in POS:
            if k in s:
                return "pos"
        return ""

    def _fallback_answer_group(self, opts, qtext=""):
        """v1.8.7 押題策略（即使抓不到題目文字也能跑）：
        1. 「以上皆是」優先（單選＆多選都適用）
        2. 題目極性 + 絕對化字眼：
           - 找錯題型 + 含「一定/絕對」 → 那個就是答案
           - 找對題型 + 含「一定/絕對」 → 排除
        3. cycling：跳過已試過的錯選項（依 options_signature 跨 attempt 穩定）
        4. 是非題：題目含絕對化字眼 → 偏好「錯／否」；否則偏好「對／是」
        5. 單選預設：剩餘最長 label
        """
        if not opts:
            return
        itype = opts[0][2]
        # v1.8.7 bug #3: 傳入 qtext，每題獨立 tried set，避免 TF 共用「對/錯」signature
        sig = self._options_signature(opts, qtext=qtext or "")
        tried = self._exam_session_tried.setdefault(sig, set())
        # v1.8.45:把題庫 known wrong 預載入 tried(持久化的 cycling),跨 session 不重蹈覆轍
        if qtext:
            tried |= self.qa_bank.get_wrong(qtext)
        polarity = self._question_polarity(qtext or "")

        def _norm_lab(lab):
            return QABank.normalize(lab or "")

        def _click(inp):
            try:
                self.driver.execute_script("arguments[0].click()", inp)
                return True
            except Exception:
                return False

        def _record_wrong(lab):
            """v1.8.45:cycling 試完後失敗 → 寫進題庫 wrong(持久化)"""
            nl = _norm_lab(lab)
            tried.add(nl)
            if qtext and lab:
                try:
                    self.qa_bank.add_wrong(qtext, lab)
                except Exception:
                    pass

        try:
            # ── 多選題 (checkbox) ──
            if itype == "checkbox":
                # 1. 「以上皆是」優先且未試 → 只勾它
                for inp, lab, _t in opts:
                    if self._is_all_above(lab) and _norm_lab(lab) not in tried:
                        for i2, _l2, _t2 in opts:
                            try:
                                if i2.is_selected():
                                    self.driver.execute_script("arguments[0].click()", i2)
                            except Exception:
                                pass
                        if _click(inp):
                            _record_wrong(lab)
                            return
                # 2. 全勾，但跳過「以上皆非」與絕對化詞（找對題型才避絕對化）
                clicked_any = False
                for inp, lab, _t in opts:
                    if self._is_none_above(lab):
                        continue
                    if polarity == "pos" and self._has_absolute_word(lab):
                        continue
                    try:
                        if not inp.is_selected():
                            if _click(inp):
                                clicked_any = True
                                _record_wrong(lab)
                    except Exception:
                        pass
                if clicked_any:
                    return
                _click(opts[0][0])
                return

            # ── 是非題 (2 選項) ──
            if len(opts) == 2:
                YES_KEYS = ("○", "對", "是", "true", "正確", "correct", "yes", "t")
                NO_KEYS  = ("✕", "×", "錯", "否", "false", "錯誤", "wrong", "no", "f")
                # 題目含「一定 / 絕對」→ 通常答否
                if self._has_absolute_word(qtext):
                    for inp, lab, _t in opts:
                        sl = (lab or "").strip().lower()
                        if any(k.lower() in sl for k in NO_KEYS) and _norm_lab(lab) not in tried:
                            if _click(inp):
                                _record_wrong(lab)
                                return
                # 預設偏好「對／是」
                for inp, lab, _t in opts:
                    sl = (lab or "").strip().lower()
                    if any(k.lower() in sl for k in YES_KEYS) and _norm_lab(lab) not in tried:
                        if _click(inp):
                            _record_wrong(lab)
                            return
                # cycling：找未試過的
                for inp, lab, _t in opts:
                    if _norm_lab(lab) not in tried:
                        if _click(inp):
                            _record_wrong(lab)
                            return
                _click(opts[0][0])
                return

            # ── 單選題 (3+ 選項) ──
            # 1. 「以上皆是」優先（除非題目語意是 neg「找錯的」就跳過 — 那個情況下「以上皆是」自己就錯）
            if polarity != "neg":
                for inp, lab, _t in opts:
                    if self._is_all_above(lab) and _norm_lab(lab) not in tried:
                        if _click(inp):
                            _record_wrong(lab)
                            return
            # 2. polarity = neg：含絕對化字眼的選項 = 正解
            if polarity == "neg":
                abs_opts = [(inp, lab) for (inp, lab, _t) in opts
                            if self._has_absolute_word(lab) and _norm_lab(lab) not in tried]
                if abs_opts:
                    # 最長 absolute 通常更可疑 → 越是錯的越愛寫的滿
                    abs_opts.sort(key=lambda x: len(x[1] or ""), reverse=True)
                    inp, lab = abs_opts[0]
                    if _click(inp):
                        _record_wrong(lab)
                        return
            # 3. cycling：選未試過、非「以上皆非」的最長 label
            #    polarity = pos → 排除絕對化字眼
            def _ok(lab):
                if self._is_none_above(lab):
                    return False
                if polarity == "pos" and self._has_absolute_word(lab):
                    return False
                return True
            untried = [(inp, lab) for (inp, lab, _t) in opts
                       if _norm_lab(lab) not in tried and _ok(lab)]
            if untried:
                untried.sort(key=lambda x: len(x[1] or ""), reverse=True)
                inp, lab = untried[0]
                if _click(inp):
                    _record_wrong(lab)
                    return
            # 4. 退到原本被排除的（含絕對化／以上皆非）
            untried2 = [(inp, lab) for (inp, lab, _t) in opts
                        if _norm_lab(lab) not in tried]
            if untried2:
                untried2.sort(key=lambda x: len(x[1] or ""), reverse=True)
                inp, lab = untried2[0]
                if _click(inp):
                    _record_wrong(lab)
                    return
            # 5. 全試過 → 隨機
            try:
                inp, lab, _t = random.choice(opts)
                _click(inp)
            except Exception:
                _click(opts[-1][0])
        except Exception:
            try:
                self.driver.execute_script("arguments[0].click()", opts[-1][0])
            except Exception:
                pass

    # ── 課程播放器：自動填問卷 ───────────────────────────────

    def _auto_fill_player_survey(self):
        """在播放器內自動填問卷/評價（v1.6.2：跨 frame + 新視窗）
        v1.8.7：開頭快速偵測「修改問卷」狀態 → 立刻離開（不空等、不重複送）
        """
        try:
            try:
                self.driver.switch_to.default_content()
            except Exception:
                pass

            # v1.8.7：第一道關卡 — 已填過就直接走
            if self._survey_already_done():
                self.log("⏭ 問卷已填寫（修改問卷／查看問卷），直接進下一門")
                return

            # 若目前頁面已有可填問卷按鈕（已被 _try_jump_to_survey_sysbar 帶到），就不重點連結
            if not self._can_fill_survey_now():
                self.log("目前頁面看不到問卷按鈕，先嘗試跳到問卷頁...")
                if not self._try_jump_to_survey_sysbar():
                    self.log("跳問卷頁失敗或問卷已填，放棄自動填問卷")
                    return

            # v1.8.7：第二道關卡 — 跳到問卷頁後再確認一次
            if self._survey_already_done():
                self.log("⏭ 問卷頁顯示已填寫，跳過")
                return

            # 跨 frame 找「填寫問卷」/「進行問卷」/「開始填寫」按鈕
            # v1.8.1：拿掉「修改問卷」（已填過），點下去會重複送問卷
            btns = self._find_in_any_frame_xpath(
                "//a[contains(normalize-space(.),'填寫問卷')] | "
                "//a[contains(normalize-space(.),'進行問卷')] | "
                "//a[contains(normalize-space(.),'開始填寫')] | "
                "//button[contains(normalize-space(.),'填寫問卷')] | "
                "//button[contains(normalize-space(.),'進行問卷')] | "
                "//*[contains(@class,'process-btn') and "
                "(contains(normalize-space(.),'填寫問卷') or "
                "contains(normalize-space(.),'進行問卷') or "
                "contains(normalize-space(.),'開始填寫'))]",
                clickable=True)
            # v1.8.1：再次過濾 done/pass/finish/disabled 狀態
            DONE_CLS = ("done", "pass", "finished", "complete", "disabled", "inactive")
            DONE_TXT = ("已填寫", "已繳交", "已完成", "修改問卷", "查看問卷", "重新填寫")
            if btns:
                btn_el = btns[0]
                cls_l = (btn_el.get_attribute("class") or "").lower()
                txt_v = (btn_el.text or "").strip()
                if any(t in cls_l for t in DONE_CLS) or any(t in txt_v for t in DONE_TXT):
                    self.log(f"⏭ 問卷已填寫（class={cls_l[:40]}, text={txt_v[:20]}），跳過")
                    return
            if not btns:
                self.log("⏭ 找不到「填寫問卷」按鈕（可能已填寫），跳過")
                return

            prev_handles = list(self.driver.window_handles)
            self.log(f"點擊「填寫問卷」（tag={btns[0].tag_name}）")
            try:
                btns[0].click()
            except Exception:
                self.driver.execute_script("arguments[0].click()", btns[0])

            # 處理可能新視窗
            self._switch_to_new_window_if_any(prev_handles, "問卷視窗")
            self._human_sleep(2.5, 0.6)

            # Checkbox 多選：每組勾選第一個
            cbs = self.driver.find_elements(By.CSS_SELECTOR, "input[type='checkbox']")
            cb_groups = {}
            for cb in cbs:
                name = (cb.get_attribute("name") or "").rsplit("[", 1)[0]
                if name not in cb_groups:
                    cb_groups[name] = []
                cb_groups[name].append(cb)
            for name, group in cb_groups.items():
                if group:
                    try:
                        if not group[0].is_selected():
                            self.driver.execute_script("arguments[0].click()", group[0])
                    except Exception:
                        pass

            # Radio 單選：每組選第一個（非常滿意/非常同意）
            radios = self.driver.find_elements(By.CSS_SELECTOR, "input[type='radio']")
            r_groups = {}
            for r in radios:
                name = r.get_attribute("name") or ""
                if name not in r_groups:
                    r_groups[name] = []
                r_groups[name].append(r)
            for name, opts in r_groups.items():
                if opts:
                    try:
                        self.driver.execute_script("arguments[0].click()", opts[0])
                    except Exception:
                        pass

            # 點「確定繳交」（跨 frame）
            submit = None
            for _ in range(5):
                submit = self._find_in_any_frame_xpath(
                    "//a[contains(normalize-space(.),'確定繳交')] | "
                    "//button[contains(normalize-space(.),'確定繳交')] | "
                    "//a[contains(normalize-space(.),'確定送出')] | "
                    "//button[contains(normalize-space(.),'確定送出')] | "
                    "//input[(@type='button' or @type='submit') and "
                    "(contains(@value,'繳交') or contains(@value,'送出'))]",
                    clickable=True)
                if submit:
                    break
                self._human_sleep(1.5, 0.3)
            if not submit:
                self.log("⚠ 找不到問卷繳交按鈕")
                return
            try:
                submit[0].click()
            except Exception:
                self.driver.execute_script("arguments[0].click()", submit[0])
            time.sleep(1)
            try:
                self.driver.switch_to.alert.accept()
            except Exception:
                pass
            self.log("✓ 問卷已繳交")
            time.sleep(2)

            # 收尾：關掉所有額外視窗（避免 session 跑到怪 window）
            self._close_extra_windows()
        except Exception as e:
            self.log(f"自動填問卷失敗: {e}")
            try:
                self._close_extra_windows()
            except Exception:
                pass

    # ── 關閉 ──────────────────────────────────────────────

    def _save_missed_questions(self):
        """把本次執行所有未命中的題目寫到 qa_missed.json，方便人工填答案"""
        if not self._missed_questions:
            return
        try:
            existing = {}
            if os.path.exists(QA_MISS_FILE):
                with open(QA_MISS_FILE, "r", encoding="utf-8") as f:
                    existing = json.load(f)
            existing.update(self._missed_questions)
            with open(QA_MISS_FILE, "w", encoding="utf-8") as f:
                json.dump(existing, f, ensure_ascii=False, indent=2)
            self.log(f"📝 未命中題目已存：{QA_MISS_FILE}（共 {len(existing)} 題）")
        except Exception as e:
            self.log(f"存 qa_missed.json 失敗：{e}")

    def _print_session_stats(self):
        """v1.8.7：印出本次執行累積統計"""
        try:
            s = self._stats or {}
            self.log("══ 本次執行統計 ══")
            self.log(f"  起始：{s.get('started_at','')}")
            self.log(f"  課程：嘗試 {s.get('courses_attempted',0)}、過 {s.get('courses_passed',0)}、未過 {s.get('courses_failed',0)}")
            self.log(f"  測驗：總 attempt {s.get('exam_attempts',0)}、通過 {s.get('exams_passed',0)}")
            self.log(f"  答題：總 {s.get('questions_total',0)} 題（題庫 {s.get('db_hits',0)} / 選項池 {s.get('option_hits',0)} / AI {s.get('ai_hits',0)} / 押題 {s.get('fallbacks',0)}）")
            self.log(f"  學習：harvester 收割 {s.get('harvested_questions',0)} 題")
            self.log(f"  目前題庫總量：{self.qa_bank.count()} 題")
            self.log(f"  未命中（待人工）：{len(self._missed_questions)} 題")
            self.log("══════════════════")
        except Exception as e:
            try:
                self.log(f"⚠ 統計輸出失敗：{e}")
            except Exception:
                pass

    def _on_close(self):
        """v1.8.18：關閉視窗時也自動存 log（仿 hiv_code）"""
        self.running = False
        try:
            self._print_session_stats()
        except Exception:
            pass
        try:
            self._save_config()
        except Exception:
            pass
        try:
            self.qa_bank.save()
        except Exception:
            pass
        try:
            self._save_missed_questions()
        except Exception:
            pass
        # v1.8.18：自動存 log
        try:
            self._save_log()
        except Exception:
            pass
        self.root.destroy()
        # 背景關閉瀏覽器，不讓 UI 卡住
        if self.driver:
            def _quit():
                try:
                    self.driver.quit()
                except Exception:
                    pass
            threading.Thread(target=_quit, daemon=True).start()

    def run(self):
        self.log(f"E等公務園 自動上課工具 v{VERSION}")
        self.log("自動管理瀏覽器驅動版本 - 不需要手動更換 msedgedriver")
        self.log(f"📚 題庫已載入：{self.qa_bank.count()} 題（{QA_BANK_FILE}）")
        if not self.config.get("accounts"):
            self.log("尚無帳號，請按「＋新增」加入帳號")
        else:
            self.log("請選擇帳號後按「登入」")
        self.root.mainloop()


# ══════════════════════════════════════════════════════════
#  帳號新增/編輯對話框
# ══════════════════════════════════════════════════════════

class AccountDialog(tk.Toplevel):
    def __init__(self, parent, title="帳號", data=None):
        super().__init__(parent)
        self.title(title)
        self.resizable(False, False)
        self.grab_set()
        self.result = None

        data = data or {}
        ttk.Label(self, text="顯示名稱：").grid(row=0, column=0, padx=10, pady=6, sticky="w")
        self.label_var = tk.StringVar(value=data.get("label", ""))
        ttk.Entry(self, textvariable=self.label_var, width=24).grid(row=0, column=1, padx=10, pady=6)

        ttk.Label(self, text="帳號：").grid(row=1, column=0, padx=10, pady=6, sticky="w")
        self.account_var = tk.StringVar(value=data.get("account", ""))
        ttk.Entry(self, textvariable=self.account_var, width=24).grid(row=1, column=1, padx=10, pady=6)

        ttk.Label(self, text="密碼：").grid(row=2, column=0, padx=10, pady=6, sticky="w")
        self.password_var = tk.StringVar(value=data.get("password", ""))
        pw_frame = ttk.Frame(self)
        pw_frame.grid(row=2, column=1, padx=10, pady=6, sticky="w")
        self._pw_entry = ttk.Entry(pw_frame, textvariable=self.password_var,
                                   show="*", width=20)
        self._pw_entry.pack(side=tk.LEFT)
        self._pw_visible = False
        self._pw_btn = ttk.Button(pw_frame, text="👁", width=3,
                                  command=self._toggle_password)
        self._pw_btn.pack(side=tk.LEFT, padx=(4, 0))

        self.login_type = tk.StringVar(value="elearn")

        bf = ttk.Frame(self)
        bf.grid(row=3, column=0, columnspan=2, pady=10)
        ttk.Button(bf, text="確定", command=self._ok).pack(side=tk.LEFT, padx=6)
        ttk.Button(bf, text="取消", command=self.destroy).pack(side=tk.LEFT)

        self.wait_window()

    def _toggle_password(self):
        self._pw_visible = not self._pw_visible
        self._pw_entry.config(show="" if self._pw_visible else "*")
        self._pw_btn.config(text="🙈" if self._pw_visible else "👁")

    def _ok(self):
        acc = self.account_var.get().strip()
        if not acc:
            messagebox.showwarning("提示", "帳號不能為空", parent=self)
            return
        self.result = {
            "label":      self.label_var.get().strip() or acc,
            "account":    acc,
            "password":   self.password_var.get(),
            "login_type": self.login_type.get(),
        }
        self.destroy()


# ══════════════════════════════════════════════════════════
#  Gemini API Key 新增/編輯對話框 (v1.8.47)
# ══════════════════════════════════════════════════════════

class ApiKeyDialog(tk.Toplevel):
    def __init__(self, parent, title="API Key", data=None):
        super().__init__(parent)
        self.title(title)
        self.resizable(False, False)
        self.grab_set()
        self.result = None

        data = data or {}
        ttk.Label(self, text="顯示名稱：").grid(row=0, column=0, padx=10, pady=6, sticky="w")
        self.label_var = tk.StringVar(value=data.get("label", ""))
        ttk.Entry(self, textvariable=self.label_var, width=30).grid(row=0, column=1, padx=10, pady=6)

        ttk.Label(self, text="API Key：").grid(row=1, column=0, padx=10, pady=6, sticky="w")
        self.key_var = tk.StringVar(value=data.get("key", ""))
        kf = ttk.Frame(self)
        kf.grid(row=1, column=1, padx=10, pady=6, sticky="w")
        self._key_entry = ttk.Entry(kf, textvariable=self.key_var, show="*", width=26)
        self._key_entry.pack(side=tk.LEFT)
        self._key_visible = False
        self._key_btn = ttk.Button(kf, text="👁", width=3, command=self._toggle_key)
        self._key_btn.pack(side=tk.LEFT, padx=(4, 0))

        ttk.Label(self, text="(取得 Gemini API Key:aistudio.google.com/apikey)",
                  foreground="gray", font=("Microsoft JhengHei", 8)).grid(
            row=2, column=0, columnspan=2, padx=10, pady=(0, 4), sticky="w")

        bf = ttk.Frame(self)
        bf.grid(row=3, column=0, columnspan=2, pady=10)
        ttk.Button(bf, text="確定", command=self._ok).pack(side=tk.LEFT, padx=6)
        ttk.Button(bf, text="取消", command=self.destroy).pack(side=tk.LEFT)

        self.wait_window()

    def _toggle_key(self):
        self._key_visible = not self._key_visible
        self._key_entry.config(show="" if self._key_visible else "*")
        self._key_btn.config(text="🙈" if self._key_visible else "👁")

    def _ok(self):
        k = self.key_var.get().strip()
        if not k:
            messagebox.showwarning("提示", "API Key 不能為空", parent=self)
            return
        if len(k) < 20:
            messagebox.showwarning("提示", "API Key 長度看起來不對 (應 ≥ 20 字元)", parent=self)
            return
        self.result = {
            "label": self.label_var.get().strip() or "key",
            "key":   k,
        }
        self.destroy()


# ══════════════════════════════════════════════════════════
if __name__ == "__main__":
    try:
        app = EClassApp()
        app.run()
    except Exception as e:
        import traceback
        traceback.print_exc()
        input("\n按 Enter 關閉...")
