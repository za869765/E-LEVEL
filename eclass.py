"""
E等公務園 自動上課輔助工具 v1.1.0
- 自動管理瀏覽器驅動版本（永遠不會版本不符）
- 支援 E等公務人員（我的e政府）/ 人事服務網eCPA 登入
- 多組帳號記憶與快速切換
- 自動掃描未完成課程 → 循環上課 → 自動關彈窗
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, simpledialog
import threading
import time
import json
import os
import re
import sys
from datetime import datetime

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

VERSION = "1.5.1"
# 打包成 exe 時用 sys.executable 定位，避免存到暫存目錄
if getattr(sys, 'frozen', False):
    _BASE_DIR = os.path.dirname(sys.executable)
else:
    _BASE_DIR = os.path.dirname(os.path.abspath(__file__))
_DATA_DIR   = os.path.join(_BASE_DIR, "data")
os.makedirs(_DATA_DIR, exist_ok=True)
CONFIG_FILE = os.path.join(_DATA_DIR, "eclass_config.json")

ELEARN_HOME   = "https://elearn.hrd.gov.tw/mooc/index.php"
ECPA_LOGIN    = "https://ecpa.dgpa.gov.tw/uIAM/clogin.asp?destid=CrossHRD"
DASHBOARD_URL = "https://elearn.hrd.gov.tw/mooc/user/learn_dashboard.php"


# ══════════════════════════════════════════════════════════
class EClassApp:
    def __init__(self):
        self.driver   = None
        self.running  = False
        self.cycle_count = 0
        self._tried_hrefs = set()   # 本次執行已嘗試過的課程 href，避免無限迴圈
        self.config   = self._load_config()

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
        cfg = {
            "accounts":     self.config.get("accounts", []),
            "last_account": self.account_var.get(),
            "browser":      self.browser_type.get(),
        }
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)

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
        self.stop_btn  = ttk.Button(self._btn_frame, text="停止",
                                    style="Big.TButton", command=self._on_stop)
        self._set_btn_layout("pre_login")  # 初始狀態

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
        """偵測瀏覽器是否已登入 E等公務園"""
        if not self.driver:
            return False
        try:
            url = self.driver.current_url
            if "elearn.hrd.gov.tw" not in url:
                return False
            if "login" in url.lower() or "co_login" in url.lower():
                return False
            els = self.driver.find_elements(By.CSS_SELECTOR,
                "a[href*='logout'], .logout_btn, a[href*='learn_dashboard'],"
                " a[href*='mycourse'], .user_name, .username")
            return len(els) > 0
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

    # ── 日誌 ──────────────────────────────────────────────

    def log(self, msg):
        ts = datetime.now().strftime("%H:%M:%S")
        self.log_area.insert(tk.END, f"[{ts}] {msg}\n")
        self.log_area.see(tk.END)

    def _set_status(self, text):
        self.status_var.set(text)

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
        if browser == "chrome":
            self.log("⏳ 首次使用 Chrome 需下載 ChromeDriver，可能等 1~2 分鐘，請勿關閉...")
            opts = ChromeOptions()
            opts.add_argument("--start-maximized")
            opts.add_argument("--disable-notifications")
            opts.add_experimental_option("excludeSwitches", ["enable-logging"])
            self.driver = webdriver.Chrome(options=opts)
        else:
            opts = EdgeOptions()
            opts.add_argument("--start-maximized")
            opts.add_argument("--disable-notifications")
            opts.add_experimental_option("excludeSwitches", ["enable-logging"])
            self.driver = webdriver.Edge(options=opts)
        self.log("瀏覽器啟動成功！")

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
                self.log("登入成功！自動開始上課...")
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
        self.running = False
        self._set_status("已停止")
        # 判斷目前是否已登入，決定回到哪個狀態
        if self._is_logged_in():
            self._set_btn_layout("ready")
        else:
            self._set_btn_layout("pre_login")

    def _auto_learn_main(self):
        # 重置「已嘗試課程」清單（每次按開始上課都從頭算）
        self._tried_hrefs = set()
        try:
            while self.running:
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

                entry = self._find_course_entry()
                if entry:
                    href = entry.get_attribute("href") or ""
                    if href and href in self._tried_hrefs:
                        self.log(f"⚠ 此課程已嘗試過（{href[:60]}），跳過第一階段")
                    else:
                        if href:
                            self._tried_hrefs.add(href)
                        title, needs_log = self._extract_card_info(entry)
                        self.log(f"── 進入課程: {title or '(課程)'}"
                                 + (f" [{needs_log}]" if needs_log else ""))
                        self.driver.execute_script("arguments[0].click()", entry)
                        time.sleep(3)
                        self._process_current_course_page()
                        if self.running:
                            self.log("本門課程處理完畢，繼續下一門...")
                            time.sleep(3)
                        continue

                # ── 第二階段：已完成課程 → 補測驗 / 補問卷 ──
                self.log("未完成課程已清空，掃描待補測驗/問卷...")
                self._click_tab("已完成")
                time.sleep(2)
                pend_entry, reason = self._find_pending_work_entry()
                if pend_entry:
                    href = pend_entry.get_attribute("href") or ""
                    if href and href in self._tried_hrefs:
                        self.log(f"⚠ 此課程已嘗試過（{href[:60]}），結束")
                        break
                    if href:
                        self._tried_hrefs.add(href)
                    title, _ = self._extract_card_info(pend_entry)
                    label = {"exam": "補做測驗", "survey": "補做問卷"}.get(reason, "補做")
                    self.log(f"── {label}: {title or '(課程)'}")
                    self.driver.execute_script("arguments[0].click()", pend_entry)
                    time.sleep(3)
                    self._process_current_course_page()
                    if self.running:
                        time.sleep(3)
                    continue

                self.log("所有課程已完成！")
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

    def _find_course_entry(self):
        """找「未完成(有時數)」分頁上可點擊的課程入口（優先標準 href，再 onclick/javascript:）"""
        exclude_text = {"退選", "登出", "搜尋", "排序", "常見問題", "下載",
                        "回首頁", "簡易操作", "加盟", "學習紀錄", "選課中心",
                        "學習目標", "了解", "確定", "關閉", "搜尋與排序"}

        # 方法0（最高優先）：標準課程 href 連結
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

    def _find_pending_work_entry(self):
        """在已完成課程中找到還有待完成工作的課程入口
        回傳 (element, reason)：reason ∈ {'exam', 'survey', None}
        判斷規則：
          - 測驗分數：0 分 → exam
          - 問卷狀態：未填寫 → survey
        已嘗試過的課程（self._tried_hrefs）會跳過
        """
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
                    if href and href in self._tried_hrefs:
                        continue
                    # 找父卡片，檢查待完成項目
                    try:
                        card = el.find_element(By.XPATH,
                            "./ancestor::div[contains(@class,'course') or "
                            "contains(@class,'card') or contains(@class,'item') or "
                            "contains(@class,'box')][1]")
                        card_text = card.text
                        # 測驗分數：0 分 → 需補考
                        if re.search(r'測驗分數[：:]\s*0\s*分', card_text):
                            return el, "exam"
                        # 問卷狀態：未填寫 → 需補問卷
                        if re.search(r'問卷狀態[：:]\s*未填寫', card_text):
                            return el, "survey"
                    except Exception:
                        pass
            except Exception:
                pass
        return None, None

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
                    self.driver.switch_to.window(self.driver.window_handles[-1])
                    self.log("切換到課程播放器視窗")
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

            self._learning_loop(required_minutes=req_min)
            self.log("嘗試自動測驗...")
            self._auto_take_exam()
            self.log("嘗試自動填問卷...")
            self._auto_fill_player_survey()

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
        """從連結元素向上找卡片容器，回傳 (title, needs_log)"""
        title, needs_log = "", ""
        try:
            card = el.find_element(By.XPATH,
                "./ancestor::div[contains(@class,'course') or "
                "contains(@class,'card') or contains(@class,'item') or "
                "contains(@class,'box')][1]")
            for ts in [".//h3", ".//h4", ".//p[contains(@class,'title')]",
                       ".//span[contains(@class,'title')]",
                       ".//div[contains(@class,'title')]",
                       ".//strong", ".//b"]:
                try:
                    t = card.find_element(By.XPATH, ts).text.strip()
                    if t and len(t) > 3:
                        title = t
                        break
                except Exception:
                    pass
            ct = card.text
            badges = []
            if "閱讀時數" in ct:
                badges.append("閱讀")
            if "測驗" in ct:
                badges.append("測驗")
            if "問卷" in ct:
                badges.append("問卷")
            needs_log = "/".join(badges)
        except Exception:
            pass
        return title, needs_log

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
        """印出課程時數資訊，回傳需要上課的分鐘數（50% 門檻），0 代表未知"""
        try:
            body = self.driver.find_element(By.TAG_NAME, "body").text
            for line in body.split("\n"):
                if ("分鐘" in line or "小時" in line) and \
                        ("認證" in line or "時數" in line or "上課" in line or "認定" in line):
                    self.log(line.strip())
                    break
            # 解析小時數 → 50% 門檻（分鐘）
            m = re.search(r'(\d+(?:\.\d+)?)\s*小時', body)
            if m:
                total_min = float(m.group(1)) * 60
                req = int(total_min * 0.5)
                self.log(f"時數門檻：需上課至少 {req} 分鐘（總時數 50%）")
                return req
            # 只有分鐘表示
            m2 = re.search(r'(\d+)\s*分鐘', body)
            if m2:
                req = int(int(m2.group(1)) * 0.5)
                self.log(f"時數門檻：需上課至少 {req} 分鐘（總時數 50%）")
                return req
        except Exception:
            pass
        return 0

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
        """關閉播放器內每30分鐘的驗證彈窗（未按確定會被登出）"""
        # 1. JS alert（最高優先）
        try:
            alert = self.driver.switch_to.alert
            self.log(f"關閉驗證彈窗(alert): {alert.text[:40]}")
            alert.accept()
            return True
        except Exception:
            pass
        # 2. 頁面內驗證彈窗（按確定/繼續/繼續上課）
        confirm_texts = ["繼續上課", "繼續學習", "繼續", "確認", "我在",
                         "確定", "仍在上課", "確認在線", "繼續觀看", "OK"]
        for text in confirm_texts:
            try:
                btns = self.driver.find_elements(By.XPATH,
                    f"//*[contains(normalize-space(),'{text}') and "
                    f"(self::button or self::a or self::input[@type='button'] "
                    f"or self::input[@type='submit'])]")
                for btn in btns:
                    if btn.is_displayed():
                        self.driver.execute_script("arguments[0].click()", btn)
                        self.log(f"已回應驗證彈窗：{text}")
                        return True
            except Exception:
                pass
        return False

    def _learning_loop(self, required_minutes=0):
        self.log("開始上課！請專心聽講......")
        check_every = 10   # 每 10 次循環做一次時數確認（內部固定值）
        local_cycle = 0
        no_chapter_count = 0
        start_time = time.time()

        while self.running:
            # ── 每次循環優先處理驗證彈窗（30分鐘一次，不處理會被登出）──
            self._dismiss_player_popup()

            # ── 時數門檻：已達 50% 即退出，進行測驗/問卷 ──
            if required_minutes > 0:
                elapsed_min = (time.time() - start_time) / 60
                if elapsed_min >= required_minutes:
                    self.log(f"已上課 {elapsed_min:.0f} 分鐘，達到時數門檻（{required_minutes}分），切換測驗/問卷")
                    return

            chapters = self._find_chapters()
            if chapters:
                no_chapter_count = 0
                for ch in chapters:
                    if not self.running:
                        return
                    try:
                        self.driver.execute_script("arguments[0].click()", ch)
                        time.sleep(0.5)
                    except (StaleElementReferenceException, WebDriverException):
                        break
            else:
                no_chapter_count += 1
                if no_chapter_count <= 3:
                    self.log("找不到課程章節，等待中...")
                    time.sleep(10)
                    continue
                else:
                    # 找不到章節 → 停留在課程頁面等時數累積
                    self.log("停留在課程頁面（等待時數累積）...")
                    time.sleep(60)

            local_cycle += 1
            self.cycle_count += 1
            self.log(f"第{self.cycle_count}次，我正在努力上課中....運行")
            self._set_status(f"上課中... 第 {self.cycle_count} 次循環")

            if local_cycle % check_every == 0:
                self.log("檢查上課時數...")
                in_player = "mohw.elearn.hrd.gov.tw" in self.driver.current_url
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

            # 播放器內最多 50 次循環後返回，繼續做測驗/問卷
            if "mohw.elearn.hrd.gov.tw" in self.driver.current_url and local_cycle >= 50:
                self.log("播放器上課循環已達上限，準備進行測驗和問卷")
                return

    def _find_chapters(self):
        # 課程播放器（mohw.elearn.hrd.gov.tw）左側章節為 radio button
        selectors = [
            "input[type='radio']",         # 最高優先：播放器左側章節 radio
            ".syllabus_node",
            ".course_tree li a",
            ".chapter_item",
            ".lesson_menu li",
            ".tree_node input",
            "#contentList li a",
            "ul.chapters li a",
            ".sidebar a[onclick]",
            ".course_menu a",
            "label[for*='lesson'], label[for*='unit']",
        ]
        for sel in selectors:
            try:
                els = [e for e in self.driver.find_elements(By.CSS_SELECTOR, sel)
                       if e.is_displayed()]
                if len(els) >= 2:
                    return els
            except Exception:
                continue

        # iframe fallback
        try:
            for iframe in self.driver.find_elements(By.TAG_NAME, "iframe"):
                try:
                    self.driver.switch_to.frame(iframe)
                    for sel in selectors[:6]:
                        try:
                            els = [e for e in self.driver.find_elements(By.CSS_SELECTOR, sel)
                                   if e.is_displayed()]
                            if len(els) >= 2:
                                return els
                        except Exception:
                            pass
                    self.driver.switch_to.default_content()
                except Exception:
                    self.driver.switch_to.default_content()
        except Exception:
            self.driver.switch_to.default_content()
        return []

    # ── 課程播放器：自動測驗 ─────────────────────────────────

    def _auto_take_exam(self):
        """在播放器內自動完成測驗"""
        try:
            # 點左側「測驗/考試」
            links = self.driver.find_elements(By.XPATH,
                "//a[contains(text(),'測驗') or contains(text(),'考試')]")
            link = next((e for e in links if e.is_displayed()), None)
            if not link:
                return
            self.driver.execute_script("arguments[0].click()", link)
            time.sleep(2)

            # 點「進行測驗」
            try:
                btn = WebDriverWait(self.driver, 6).until(EC.element_to_be_clickable(
                    (By.XPATH, "//*[contains(text(),'進行測驗')]")))
                btn.click()
                time.sleep(2)
            except TimeoutException:
                return

            # 點「開始作答」
            try:
                btn = WebDriverWait(self.driver, 6).until(EC.element_to_be_clickable(
                    (By.XPATH, "//*[contains(text(),'開始作答')]")))
                btn.click()
                time.sleep(3)
            except TimeoutException:
                return

            # 自動答題
            self._auto_answer_exam_questions()

            # 點「送出答案，結束測驗」
            try:
                submit = WebDriverWait(self.driver, 8).until(EC.element_to_be_clickable(
                    (By.XPATH, "//*[contains(text(),'送出答案') or contains(text(),'結束測驗')]")))
                self.driver.execute_script("arguments[0].click()", submit)
                time.sleep(1)
                try:
                    self.driver.switch_to.alert.accept()
                    self.log("測驗已送出")
                    time.sleep(3)
                except Exception:
                    pass
                # 若結果頁是新視窗，關閉
                if len(self.driver.window_handles) > 1:
                    self.driver.switch_to.window(self.driver.window_handles[-1])
                    self.driver.close()
                    self.driver.switch_to.window(self.driver.window_handles[0])
            except TimeoutException:
                self.log("找不到「送出答案」按鈕")
        except Exception as e:
            self.log(f"自動測驗失敗: {e}")

    def _auto_answer_exam_questions(self):
        """是非題選○（第一個），單選選最後（以上皆是），多選全選"""
        try:
            radios = self.driver.find_elements(By.CSS_SELECTOR,
                "input[type='radio']:not([disabled])")
            groups = {}
            for r in radios:
                name = r.get_attribute("name") or ""
                if name not in groups:
                    groups[name] = []
                groups[name].append(r)

            for name, opts in groups.items():
                if not name or not opts:
                    continue
                try:
                    if len(opts) == 2:
                        # 是非題：選○（第一個）
                        self.driver.execute_script("arguments[0].click()", opts[0])
                    else:
                        # 單選題：選最後一個（通常是「以上皆是」）
                        self.driver.execute_script("arguments[0].click()", opts[-1])
                except Exception:
                    pass

            # 多選題 checkbox：全部勾選
            cbs = self.driver.find_elements(By.CSS_SELECTOR,
                "input[type='checkbox']:not([disabled])")
            for cb in cbs:
                try:
                    if not cb.is_selected():
                        self.driver.execute_script("arguments[0].click()", cb)
                except Exception:
                    pass

            self.log(f"已自動答題（{len(groups)} 組）")
        except Exception as e:
            self.log(f"自動答題失敗: {e}")

    # ── 課程播放器：自動填問卷 ───────────────────────────────

    def _auto_fill_player_survey(self):
        """在播放器內自動填問卷/評價"""
        try:
            # 點左側「問卷/評價」
            links = self.driver.find_elements(By.XPATH,
                "//a[contains(text(),'問卷') or contains(text(),'評價')]")
            link = next((e for e in links if e.is_displayed()), None)
            if not link:
                return
            self.driver.execute_script("arguments[0].click()", link)
            time.sleep(2)

            # 點「填寫問卷」或「修改問卷」
            try:
                btn = WebDriverWait(self.driver, 6).until(EC.element_to_be_clickable(
                    (By.XPATH, "//*[contains(text(),'填寫問卷') or contains(text(),'修改問卷')]")))
                btn.click()
                time.sleep(3)
            except TimeoutException:
                return

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

            # 點「確定繳交」
            try:
                submit = WebDriverWait(self.driver, 6).until(EC.element_to_be_clickable(
                    (By.XPATH, "//*[contains(text(),'確定繳交') or contains(text(),'確定送出')]")))
                self.driver.execute_script("arguments[0].click()", submit)
                time.sleep(1)
                try:
                    self.driver.switch_to.alert.accept()
                except Exception:
                    pass
                self.log("問卷已繳交")
                time.sleep(2)
            except TimeoutException:
                self.log("找不到問卷繳交按鈕")
        except Exception as e:
            self.log(f"自動填問卷失敗: {e}")

    # ── 關閉 ──────────────────────────────────────────────

    def _on_close(self):
        self.running = False
        try:
            self._save_config()
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
        ttk.Entry(self, textvariable=self.password_var, show="*", width=24).grid(row=2, column=1, padx=10, pady=6)

        self.login_type = tk.StringVar(value="elearn")

        bf = ttk.Frame(self)
        bf.grid(row=3, column=0, columnspan=2, pady=10)
        ttk.Button(bf, text="確定", command=self._ok).pack(side=tk.LEFT, padx=6)
        ttk.Button(bf, text="取消", command=self.destroy).pack(side=tk.LEFT)

        self.wait_window()

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
if __name__ == "__main__":
    try:
        app = EClassApp()
        app.run()
    except Exception as e:
        import traceback
        traceback.print_exc()
        input("\n按 Enter 關閉...")
