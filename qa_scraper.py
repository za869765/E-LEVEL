"""
qa_scraper.py — roddayeye 痞客幫題庫爬蟲（v1.8.0）

主要功能：
1. fetch_index()              — 抓 https://roddayeye.pixnet.net/blog/posts/15325785090
                                 解析所有「課名 → 答案頁 URL」mapping，cache 30 天
2. fuzzy_lookup(title, idx)   — 用 difflib 找最相近的課名
3. fetch_and_parse(url)       — 抓答案頁 HTML，解析 [{q, type, a, options_all}]

注意：
- 痞客幫頁面 meta 宣告 UTF-8，但實際中文內容是 Big5。要做混合解碼。
- 答案頁結構：<table> 中每題 Q row + 4~5 選項 row；正解 row 第一格含 <span>v</span>
"""

import os
import re
import json
import time
import difflib
import urllib.request
import urllib.error
from html import unescape
from html.parser import HTMLParser

INDEX_URL = "https://roddayeye.pixnet.net/blog/posts/15325785090"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
      "AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/120.0.0.0 Safari/537.36")
HEADERS = {
    "User-Agent": UA,
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "zh-TW,zh;q=0.9,en-US;q=0.8,en;q=0.7",
    "Accept-Encoding": "identity",
}

INDEX_CACHE_TTL = 30 * 86400   # 30 天


# ── 編碼工具 ────────────────────────────────────────────
def _cjk_hit_ratio(s):
    """回傳字串中 CJK 中文字符占非空白字元的比例（0~1）。
    用來判定 decode 結果是否「讀得出中文」，比 try/except 可靠。"""
    if not s:
        return 0.0
    non_ws = [c for c in s if not c.isspace()]
    if not non_ws:
        return 0.0
    cjk = sum(1 for c in non_ws if "\u4e00" <= c <= "\u9fff")
    return cjk / len(non_ws)


def smart_decode(raw_bytes):
    """痞客幫頁面：頭部宣告 UTF-8 但中文 body 是 Big5。
    bug #39: 原本「先試 UTF-8 strict 成功就回傳」邏輯反了。
      - Big5 bytes 有時能通過 UTF-8 strict（罕見但會發生），結果亂碼仍回傳
      - 反過來，若 Big5 decode 出更多可讀中文 → 那才是對的編碼
    新策略：兩種都試（以 replace 模式），比較 CJK 中文字元命中率高者。
    """
    candidates = []
    for enc in ("utf-8", "big5"):
        try:
            decoded = raw_bytes.decode(enc, "replace")
        except Exception:
            continue
        candidates.append((_cjk_hit_ratio(decoded), enc, decoded))
    if not candidates:
        return raw_bytes.decode("utf-8", "replace")
    candidates.sort(key=lambda x: x[0], reverse=True)
    return candidates[0][2]


def http_get(url, timeout=15):
    req = urllib.request.Request(url, headers=HEADERS)
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


# ── 索引 ────────────────────────────────────────────────
_LINK_RE = re.compile(
    r'<a\s+[^>]*?href="(https?://roddayeye\.pixnet\.net/blog/post/(\d+))"[^>]*>'
    r'(.*?)</a>',
    re.I | re.S)


def _strip_html_to_text(html_fragment):
    """簡易把 HTML tags 拔光成純文字"""
    s = re.sub(r'<[^>]+>', '', html_fragment)
    s = unescape(s)
    return re.sub(r'\s+', ' ', s).strip()


def fetch_index(cache_path):
    """抓索引並回傳 dict {課名: URL}。會 cache 到 cache_path。
    cache 過期或不存在才重抓。
    """
    # cache 命中
    if cache_path and os.path.exists(cache_path):
        try:
            mtime = os.path.getmtime(cache_path)
            if time.time() - mtime < INDEX_CACHE_TTL:
                with open(cache_path, "r", encoding="utf-8") as f:
                    return json.load(f)
        except Exception:
            pass

    raw = http_get(INDEX_URL, timeout=20)
    html = smart_decode(raw)

    idx = {}
    for m in _LINK_RE.finditer(html):
        url = m.group(1)
        title_html = m.group(3)
        title = _strip_html_to_text(title_html)
        # 索引內鏈如「天花《解答》」「身心障礙者權利保障」
        # 把「《解答》」「(解答)」「【解答】」之類去掉
        title = re.sub(r'[《\(（【]\s*解答\s*[】）\)》]', '', title).strip()
        if not title or len(title) < 2:
            continue
        # 過濾分類/Tag 連結
        if "分類" in title or "tag" in url.lower():
            continue
        # 同名取最新（後者覆蓋）
        idx[title] = url

    # 寫 cache
    if cache_path:
        try:
            os.makedirs(os.path.dirname(cache_path), exist_ok=True)
            with open(cache_path, "w", encoding="utf-8") as f:
                json.dump(idx, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    return idx


# ── Fuzzy 課名比對 ────────────────────────────────────────
def _normalize_title(t):
    """正規化課名以便比對：去括號內容、講次、標點、空白"""
    if not t:
        return ""
    s = t
    # 移除（...）/【...】/(...)
    s = re.sub(r'[\(（【].*?[\)）】]', '', s)
    # 移除「第N講」「第N章」「第N單元」
    s = re.sub(r'第\s*\d+\s*[講章節課集回單元]', '', s)
    # 移除冒號後綴
    s = re.sub(r'[：:].*$', '', s)
    # 移除空白標點
    s = re.sub(r'[\s　,，.。、；;！!？?\-—–\\/]+', '', s)
    return s


def fuzzy_lookup(my_title, index_dict, threshold=0.45, top_k=3):
    """用 difflib 找最像的課名。回傳 [(score, idx_title, url), ...]，按分數降序"""
    if not my_title or not index_dict:
        return []
    me_norm = _normalize_title(my_title)
    if not me_norm:
        return []

    scored = []
    for idx_title, url in index_dict.items():
        them_norm = _normalize_title(idx_title)
        if not them_norm:
            continue
        # 完全相等加分
        if me_norm == them_norm:
            scored.append((1.0, idx_title, url))
            continue
        # 子字串匹配（短的在長的裡）
        sub_bonus = 0.0
        if len(me_norm) >= 3 and me_norm in them_norm:
            sub_bonus = 0.3
        elif len(them_norm) >= 3 and them_norm in me_norm:
            sub_bonus = 0.3
        ratio = difflib.SequenceMatcher(None, me_norm, them_norm).ratio()
        scored.append((min(1.0, ratio + sub_bonus), idx_title, url))

    scored.sort(key=lambda x: x[0], reverse=True)
    # 去掉低於門檻
    return [s for s in scored[:top_k] if s[0] >= threshold]


# ── 解析答案頁 ────────────────────────────────────────────
# 答案頁結構（roddayeye 痞客幫）：
#  <tr>  ← 題目 row
#    <td><span>Q</span></td>
#    <td><span style="color:white">r</span></td>   ← 隱藏題型代號
#    <td><span>4. 題目文字</span></td>
#  </tr>
#  <tr>  ← 選項 row（錯）
#    <td><span></span></td>
#    <td>(white)o</td>
#    <td><span>A 選項文字</span></td>
#  </tr>
#  <tr>  ← 選項 row（對）
#    <td><span>v</span></td>            ← 第一格含 v = 正解
#    <td>(white)d</td>
#    <td><span>C 選項文字</span></td>
#  </tr>

class _AnswerPageParser(HTMLParser):
    """解析痞客幫答案頁，產出 list of {q, type, a, options_all}"""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.in_tr = False
        self.in_td = False
        self.cur_td_html = []     # 當前 td 內 raw text
        self.cur_td_has_v = False  # 第一格 td 是否含「v」標記
        self.cur_tds = []         # 當前 tr 累積的 td 文字 list
        self.cur_tds_v = []       # 對應每個 td 是否含 v
        self.questions = []       # output
        self._cur_q = None        # 當前正在累積的題目 dict

    # 把所有非 ASCII / 純白色 span 視為「真實文字」累積到 cur_td_html
    def handle_starttag(self, tag, attrs):
        if tag == "tr":
            self.in_tr = True
            self.cur_tds = []
            self.cur_tds_v = []
        elif tag == "td":
            self.in_td = True
            self.cur_td_html = []
            self.cur_td_has_v = False
            self._td_white_buffer = []
            self._in_white_span = False
        elif tag == "span":
            if self.in_td:
                # 偵測「白字」span（color:white 或 color:rgb(255,255,255)）
                style = ""
                for k, v in attrs:
                    if k.lower() == "style":
                        style = (v or "").lower()
                if "rgb(255, 255, 255)" in style or "color:white" in style \
                        or "color: white" in style or "#ffffff" in style \
                        or "#fff;" in style:
                    self._in_white_span = True
                else:
                    self._in_white_span = False

    def handle_endtag(self, tag):
        if tag == "span" and self.in_td:
            self._in_white_span = False
        elif tag == "td" and self.in_td:
            text = "".join(self.cur_td_html).strip()
            self.cur_tds.append(text)
            self.cur_tds_v.append(self.cur_td_has_v)
            self.in_td = False
        elif tag == "tr" and self.in_tr:
            self._handle_row()
            self.in_tr = False

    def handle_data(self, data):
        if not self.in_td:
            return
        # 「v」標記專偵：第一個 td 的可見文字若是 v
        if self._in_white_span:
            # 白字內容 = 隱藏的代號（題型 r/y/m, 選項 A/B/C/D）
            return
        # 偵測 v 標記
        d = data.strip()
        if d == "v" or d.lower() == "v":
            self.cur_td_has_v = True
        self.cur_td_html.append(data)

    def _handle_row(self):
        """每個 tr 結束 → 判斷是題目 row 還是選項 row"""
        if not self.cur_tds:
            return
        # 題目 row 通常 3 td：[Q] [代號] [4. 題目文字]
        # 選項 row 通常 3 td：[v或空] [代號] [選項文字]
        # 或 [空] [v_marked代號?] [選項文字]
        # 我們判斷：第 3 個 td 文字長 >= 2 且
        #   - 開頭含 Q 或第 1 個 td = "Q" → 題目
        #   - 否則 → 選項
        if len(self.cur_tds) < 3:
            return

        first_td = (self.cur_tds[0] or "").strip()
        third_td = (self.cur_tds[2] or "").strip()

        # 題目 row 判定：第 1 td = Q
        if first_td == "Q" or first_td.upper().startswith("Q"):
            # 收尾上一題
            self._flush_q()
            # 開新題
            qtext = re.sub(r'^\s*\d+[\s\.、:：]+', '', third_td).strip()
            self._cur_q = {
                "q": qtext,
                "type": "SC",   # 後面用 v 數量推斷
                "a": [],
                "options_all": [],
            }
            return

        # 選項 row 判定
        if self._cur_q is None:
            return
        if not third_td:
            return
        # 去掉前綴 "A " "B "
        opt = re.sub(r'^[A-Da-dＡ-ＤＡＢＣＤ]\s*[\.、:：\s]?\s*', '', third_td).strip()
        if not opt:
            return
        # 是否正解：第 1 格含 v
        is_correct = any(self.cur_tds_v[:1]) or any(
            (t or "").strip().lower() == "v" for t in self.cur_tds[:1])
        self._cur_q["options_all"].append({"text": opt, "correct": is_correct})
        if is_correct:
            self._cur_q["a"].append(opt)

    def _flush_q(self):
        if self._cur_q and self._cur_q.get("q"):
            opts = self._cur_q["options_all"]
            n_correct = sum(1 for o in opts if o["correct"])
            if len(opts) == 2:
                self._cur_q["type"] = "TF"
            elif n_correct >= 2:
                self._cur_q["type"] = "MC"
            else:
                self._cur_q["type"] = "SC"
            if self._cur_q["a"]:   # 至少有一個正解才收
                self.questions.append(self._cur_q)
        self._cur_q = None

    def close(self):
        self._flush_q()
        super().close()


def fetch_and_parse(url, timeout=15):
    """抓答案頁 → 回傳 list[{q, type, a, options_all}]"""
    raw = http_get(url, timeout=timeout)
    html = smart_decode(raw)
    p = _AnswerPageParser()
    try:
        p.feed(html)
        p.close()
    except Exception:
        pass
    return p.questions


# ── stand-alone 測試 ─────────────────────────────────────
if __name__ == "__main__":
    import sys
    cache = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                         "data", "course_index.json")
    print("[+] 抓索引...")
    idx = fetch_index(cache)
    print(f"[+] 索引共 {len(idx)} 課")

    test_titles = [
        "身心障礙者權利公約(CRPD)第2講：不歧視",
        "公民與政治權(含轉型正義)",
        "人權與國際公約",
    ]
    for t in test_titles:
        print(f"\n=== 找：{t} ===")
        hits = fuzzy_lookup(t, idx, threshold=0.4, top_k=5)
        for score, name, url in hits:
            print(f"  {score:.2f}  {name}  →  {url}")
        if hits:
            top_url = hits[0][2]
            print(f"\n[+] 抓 top {top_url}")
            qs = fetch_and_parse(top_url)
            print(f"[+] 解析到 {len(qs)} 題")
            for i, q in enumerate(qs[:2], 1):
                print(f"  Q{i} ({q['type']}): {q['q'][:80]}")
                for o in q["options_all"]:
                    mark = "✓" if o["correct"] else " "
                    print(f"     [{mark}] {o['text'][:70]}")
