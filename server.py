#!/usr/bin/env python3
# Portfolio Pi v2 — JTBD redesign (stdlib only)
import json, os, re, time, html, glob, urllib.request, urllib.parse, xml.etree.ElementTree as ET
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta

BASE = os.path.dirname(os.path.abspath(__file__))
SEED = json.load(open(os.path.join(BASE, "seed.json"), encoding="utf-8"))
try:
    MANIFEST = json.load(open(os.path.join(BASE, "garp-manifest.json"), encoding="utf-8"))
except Exception:
    MANIFEST = {}
ITEMS = SEED["items"]; OPTIONS = SEED.get("options", [])
POS = [i for i in ITEMS if i["kind"] == "position"]
WATCH = [i for i in ITEMS if i["kind"] == "watch"]
IDX = [i for i in ITEMS if i["kind"] == "index"]
STRIP_SYMS = ["^VIX", "SOXX", "^NDX", "^GSPC"]  # indices strip: only these four (Oren, 8/11/2026)
KNOWN_SYMS = [i["symbol"] for i in POS + WATCH]
MONTHS = ["","ינו׳","פבר׳","מרץ","אפר׳","מאי","יוני","יולי","אוג׳","ספט׳","אוק׳","נוב׳","דצמ׳"]
FLEX_DIR = os.path.expanduser("~/ibflex/reports")
PLANIT_LOANS_ILS = 758400; PLANIT_LOANS_N = 6; PLANIT_RATE = 4.25; PLANIT_MONTHLY_ILS = 2737; PLANIT_ASOF = "31/08/2026"
# Tesla Model 3 — מימון ישיר: קרן מקורית ₪174,882; ₪10,324 קרן הוחזרה עד 17/10/2026 → יתרה ₪164,558.
# החזר חודשי ≈₪1,657 (אחרון שנצפה 10/10/2026, עולה בהדרגה; מקור: RiseUp — "מימון ישיר מקבוצת י(י)").
# תנאים (אורן, 8/11): הלוואה 0% צמודה למדד — והכסף שהיה אמור לקנות את הרכב במזומן הוזרם לתיק
# במקום זאת, כך שהלוואת טסלה נחשבת מימון של התיק (לא הוצאה נפרדת).
TESLA_LOAN_ORIG_ILS = 174882; TESLA_LOAN_BAL_ILS = 164558; TESLA_MONTHLY_ILS = 1657; TESLA_ASOF = "17/10/2026"; TESLA_LAST_PAY = "10/10/2026"
# Norton (ASRE) — הלוואת Norton, נפרדת מתיק ההון (אורן, 17/10/2026; אומת מחדש 8/11/2026):
# התחייבות $150,000 ל-ASRE NORTON; הועברו ₪475,000 ב-25/01/2026 (אסמכתת מזרחי + RiseUp),
# התקבלו $150,961.39, עודף $961.39 הוחזר 06/2026 (מייל אלטשולר 23/06/2026).
# מודל החישוב (אורן, 8/11): הלוואת Norton = ₪475,000 — רשומה כמידע בלבד, לא משמשת בחישובים.
# מסך כל הלוואות Planit (₪758,400) מורידים את Norton (₪475,000) והיתרה (₪283,400) נכנסת לתיק,
# בנוסף להלוואת טסלה (₪164,558). כלומר הלוואות התיק = ₪447,958.
# (הערה: במסמכים רק ₪356,000 מתוייגים לשתי הלוואות ינואר — חשבונות 1347269 + 1355799;
# ההפרש ₪119,000 יוחזר בנפרד. במודל של אורן מלוא ₪475,000 מנוכה מסך Planit.)
# ריבית בלבד, הקרן מוחזרת בסוף התקופה. החזר חודשי ₪1,714 (מוגדל יחסית מ-₪1,285 של Planit על ₪356,000).
NORTON_COMMIT_USD = 150000; NORTON_WIRED_ILS = 475000; NORTON_WIRE_DATE = "25/01/2026"
NORTON_RECEIVED_USD = 150961.39; NORTON_REFUND_USD = 961.39
NORTON_LOAN_ILS = 475000; NORTON_MONTHLY_ILS = 1714; NORTON_ASOF = "31/08/2026"
# Meta RSU — from Oren's "Meta RSU Calculator - Shareable" (Summary tab), as of 10/11/2026 (Oren, 10/11/2026):
# vested 1,864 + unvested 471 = 2,335 shares; price $641.37; USDILS 3.16 in the sheet.
# Net after tax available to sell as of the 15/11/2026 vesting: $779,074.18 (Income 102 + non-102 + Profit 102).
RSU_VESTED = 1864; RSU_UNVESTED = 471; RSU_PRICE_USD = 641.37
RSU_PCT_DEFAULT = 50  # default % of RSUs to realize (Oren, 10/11/2026)
RSU_VEST_DATE = "15/11/2026"; RSU_ASOF = "10/11/2026"
# RSU net after tax as a function of META price — mirrors the sheet's Grants formulas exactly:
# per grant: income = MIN(price, grant_price)*shares*0.5;
# profit = MAX(price-grant_price, 0)*shares*(0.72 if 102-passed else 0.5).
# Grouped by (grant price, shares, 102 rate); grants vested by 15/11/2026 only.
# Verified: rsu_net_usd(641.37) == 779074.18 (sheet Summary G45).
RSU_GRANTS = [(332.63, 663, 0.72), (208.03, 23, 0.72), (181.11, 891, 0.72),
              (484.27, 258, 0.72), (662.71, 98, 0.5), (693.37, 40, 0.5)]


def _rsu_net(price, grants):
    return sum(sh * (0.5 * min(price, gp) + rt * max(price - gp, 0.0))
               for gp, sh, rt in grants)
def rsu_net_usd(price):
    return _rsu_net(price, RSU_GRANTS)
# Shares vesting 15/11/2026 (Grants tab: 59x$181.11, 23x$484.27, 14x$662.71, 13x$693.37)
# — already inside rsu_net_usd (the headline net is as of the 15/11 vesting).
RSU_VEST_1511 = [(181.11, 59, 0.72), (484.27, 23, 0.72), (662.71, 14, 0.5), (693.37, 13, 0.5)]
def vest1511_net_usd(price):
    return _rsu_net(price, RSU_VEST_1511)
# Current home (Ra'anana) — value ₪4.1M and mortgage ₪1.2M, both given by Oren 10/11/2026.
HOME_VALUE_ILS = 4100000; MORTGAGE_ILS = 1200000
# Ramat Hasharon (Yirmiyahu 19) — future sale proceeds; OUR SHARE is 1/6 of the
# property (full asking price ₪8,000,000; the exclusivity doc writes ₪80,000,000,
# almost certainly a typo). Default ₪1,000,000 (Oren, 18/11/2026), EXCLUDED from
# the total until he checks the box.
RAMAT_HASHARON_ILS = 1000000
# Purchase costs (Oren, 10/11/2026): brokerage 2%+VAT, lawyer 0.5%+VAT, VAT 18% (since 1/1/2025).
BROKER_PCT = 0.02; LAWYER_PCT = 0.005; VAT_RATE = 0.18
# Purchase tax 2026, single apartment - frozen brackets until 15/1/2028 (Tax Authority instruction 1/2025).
TAX_BRACKETS = [(1978745, 0.0), (2347040, 0.035), (6055070, 0.05), (20183565, 0.08), (None, 0.10)]
# Mortgage tracks, 20y - BOI monthly averages Sep 2026; prime 4.75% (BOI 3.25% since 3/9/2026).
PRIME_RATE = 4.75; PRIME_SPREAD = -0.75
FIXED_RATE = 4.62  # fixed non-CPI, 15-20y average
VAR_RATE = 4.56    # variable non-CPI, resets every 2-5y
MORT_YEARS = 20
PURCHASE_PRICE_DEFAULT = 7000000
# Renovation as part of the purchase cost (Oren, 18/11/2026); included by default.
RENOVATION_ILS = 300000
NORTON_COMMIT_USD = 150000; NORTON_WIRED_ILS = 475000; NORTON_WIRE_DATE = "25/01/2026"
NORTON_RECEIVED_USD = 150961.39; NORTON_REFUND_USD = 961.39
NORTON_LOAN_ILS = 475000; NORTON_MONTHLY_ILS = 1714; NORTON_ASOF = "31/08/2026"

def norm(sym): return (sym or "").replace(" ", "-").strip()
def fnum(v):
    try: return float(v)
    except Exception: return None

# ---------- quotes / history ----------
_cache = {}; _lock = __import__("threading").Lock()
def fetch_chart(sym, rng="1y"):
    url = "https://query1.finance.yahoo.com/v8/finance/chart/" + urllib.parse.quote(sym, safe="") + ("?range=%s&interval=1d" % rng)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (X11; Linux) AppleWebKit/537.36"})
    with urllib.request.urlopen(req, timeout=15) as r:
        d = json.loads(r.read().decode())
    res = d["chart"]["result"][0]; meta = res.get("meta", {})
    ts = res.get("timestamp", []) or []
    raw = res["indicators"]["quote"][0]
    closes, highs, lows, dates = [], [], [], []
    for j, c in enumerate(raw.get("close", [])):
        if c is None: continue
        closes.append(c); highs.append(raw.get("high", [None]*len(raw.get("close", [])))[j]); lows.append(raw.get("low", [None]*len(raw.get("close", [])))[j])
        dates.append(datetime.fromtimestamp(ts[j]).date() if j < len(ts) else None)
    if not closes: raise ValueError("no closes")
    price = meta.get("regularMarketPrice") or closes[-1]
    if len(closes) > 1 and abs(price - closes[-1]) > closes[-1] * 0.0002: prev_day = closes[-1]
    elif len(closes) > 1: prev_day = closes[-2]
    else: prev_day = price
    def ma(n): return sum(closes[-n:]) / n if len(closes) >= n else None
    def ma_at(e, n):
        seg = closes[e - n + 1:e + 1]
        return sum(seg) / n if len(seg) == n else None
    cross = None
    if len(closes) > 201:
        a1, b1 = ma_at(len(closes)-1, 150), ma_at(len(closes)-1, 200)
        a0, b0 = ma_at(len(closes)-2, 150), ma_at(len(closes)-2, 200)
        if None not in (a1, b1, a0, b0):
            if a0 <= b0 and a1 > b1: cross = "golden"
            elif a0 >= b0 and a1 < b1: cross = "death"
    # close ~30 days ago (for month view)
    mclose = None
    if dates and dates[-1]:
        target = dates[-1] - timedelta(days=30)
        for dt, c in zip(dates, closes):
            if dt and dt <= target: mclose = c
    return {"price": price, "dayPct": (price/prev_day - 1)*100 if prev_day else 0.0, "prevClose": prev_day,
            "ma150": ma(150), "ma200": ma(200), "high52": max([h for h in highs if h], default=None),
            "low52": min([l for l in lows if l], default=None), "cross": cross, "asof": time.time(), "stale": False,
            "mktTime": meta.get("regularMarketTime"),
            "monthClose": mclose, "hist": list(zip([str(d) for d in dates], closes)) if rng == "2y" else None}

def get_quote(sym, rng="1y"):
    key = sym + "|" + rng
    now = time.time()
    with _lock: c = _cache.get(key)
    if c and now - c[0] < 600: return c[1]
    try:
        q = fetch_chart(sym, rng)
    except Exception:
        if c:
            q = dict(c[1]); q["stale"] = True; return q
        return None
    with _lock: _cache[key] = (now, q)
    return q

def get_quotes(symbols):
    with ThreadPoolExecutor(max_workers=10) as ex:
        return dict(zip(symbols, ex.map(get_quote, symbols)))

# ---------- IB Flex parsing ----------
_flex_cache = {"mtime": 0, "data": None}
def _parse_daily(path):
    root = ET.parse(path).getroot()
    rows = root.findall(".//EquitySummaryByReportDateInBase")
    if not rows: return None
    last = max(rows, key=lambda e: e.get("reportDate", ""))
    f = lambda k: fnum(last.get(k)) or 0.0
    pos = []
    for e in root.findall(".//OpenPosition"):
        pos.append({"symbol": e.get("symbol", ""), "cat": e.get("assetCategory", ""),
                    "qty": fnum(e.get("position")), "mark": fnum(e.get("markPrice")),
                    "value": fnum(e.get("positionValue")), "costPrice": fnum(e.get("costBasisPrice")),
                    "costMoney": fnum(e.get("costBasisMoney")), "unreal": fnum(e.get("fifoPnlUnrealized")),
                    "pctNav": fnum(e.get("percentOfNAV")), "underlying": e.get("underlyingSymbol", "")})
    return {"date": last.get("reportDate", ""), "total": f("total"), "cash": f("cash"),
            "stock": f("stock"), "options": f("options"), "file": os.path.basename(path), "positions": pos}

def _parse_ytd(path):
    root = ET.parse(path).getroot()
    series = {}
    for e in root.findall(".//EquitySummaryByReportDateInBase"):
        d = e.get("reportDate", "")
        if len(d) == 8: series[d] = fnum(e.get("total")) or 0.0
    flows = {}
    flow_rows = []; _txns = set()
    for e in root.findall(".//CashTransaction"):
        if e.get("type") == "Deposits/Withdrawals":
            d = (e.get("reportDate") or "")[:8]; a = fnum(e.get("amount"))
            fxr = fnum(e.get("fxRateToBase")) or 1.0  # amounts may be in ILS — convert to base (USD)
            if len(d) == 8 and a:
                flows[d] = flows.get(d, 0.0) + a * fxr
                txn = e.get("transactionID") or ""
                if txn not in _txns:
                    _txns.add(txn)
                    flow_rows.append({"date": d, "ils": a, "usd": a * fxr, "fx": fxr, "txn": txn})
    cin = root.find(".//ChangeInNAV")
    cin = dict(cin.attrib) if cin is not None else {}
    fifo = {}; fifo_stk = {}
    for e in root.findall(".//FIFOPerformanceSummaryUnderlying"):
        u = norm(e.get("underlyingSymbol") or e.get("symbol") or "")
        if not u: continue
        g = fifo.setdefault(u, {"realized": 0.0, "unrealized": 0.0, "total": 0.0, "cats": set()})
        g["realized"] += fnum(e.get("totalRealizedPnl")) or 0.0
        g["unrealized"] += fnum(e.get("totalUnrealizedPnl")) or 0.0
        g["total"] += fnum(e.get("totalFifoPnl")) or 0.0
        g["cats"].add(e.get("assetCategory", ""))
        if e.get("assetCategory") == "STK":
            gs = fifo_stk.setdefault(u, {"realized": 0.0, "unrealized": 0.0, "total": 0.0})
            gs["realized"] += fnum(e.get("totalRealizedPnl")) or 0.0
            gs["unrealized"] += fnum(e.get("totalUnrealizedPnl")) or 0.0
            gs["total"] += fnum(e.get("totalFifoPnl")) or 0.0
    first_buy = {}; last_trade = {}; closed_cost = {}
    for e in root.findall(".//Trade"):
        sym = norm(e.get("symbol") or "")
        und = norm(e.get("underlyingSymbol") or sym)
        dt = (e.get("dateTime") or "")[:8]
        if len(dt) != 8: continue
        if e.get("buySell") == "BUY" and e.get("openCloseIndicator") == "O":
            if und not in first_buy or dt < first_buy[und]: first_buy[und] = dt
        if und not in last_trade or dt > last_trade[und]: last_trade[und] = dt
        if e.get("openCloseIndicator") == "C":
            c = fnum(e.get("cost"))
            if c: closed_cost[und] = closed_cost.get(und, 0.0) + abs(c)
    st = root.find(".//FlexStatement")
    return {"series": series, "flows": flows, "flow_rows": flow_rows, "changeinnav": cin, "fifo": fifo,
            "first_buy": first_buy, "last_trade": last_trade, "closed_cost": closed_cost,
            "stmt_from": st.get("fromDate", "") if st is not None else "", "stmt_to": st.get("toDate", "") if st is not None else "",
            "fifo_stk": fifo_stk}

def flex_data():
    files = sorted(glob.glob(os.path.join(FLEX_DIR, "flex-*.xml")))
    if not files: return None
    mt = max(os.path.getmtime(f) for f in files)
    if _flex_cache["data"] is not None and _flex_cache["mtime"] == mt: return _flex_cache["data"]
    daily_files = [f for f in files if "ytd" not in os.path.basename(f)]
    ytd_files = [f for f in files if "ytd" in os.path.basename(f)]
    daily = _parse_daily(daily_files[-1]) if daily_files else None
    # merge extra daily NAV rows (later than YTD end) into series
    ytd = _parse_ytd(ytd_files[-1]) if ytd_files else {"series": {}, "flows": {}, "flow_rows": [], "changeinnav": {}, "fifo": {}, "fifo_stk": {}, "first_buy": {}, "last_trade": {}, "closed_cost": {}, "stmt_from": "", "stmt_to": ""}
    daily_mtm = {}
    for f in daily_files:
        try:
            r = ET.parse(f).getroot()
            for e in r.findall(".//EquitySummaryByReportDateInBase"):
                d = e.get("reportDate", "")
                if len(d) == 8: ytd["series"][d] = fnum(e.get("total")) or 0.0
            # flows may also post after the YTD file ends (e.g. the ₪83,000 withdrawal on 19/10/2026):
            # without them the TWR chain shows a fake drop. Merge daily-file flows too.
            seen_txns = {r.get("txn") for r in ytd.get("flow_rows", [])}
            for e in r.findall(".//CashTransaction"):
                if e.get("type") == "Deposits/Withdrawals":
                    d = (e.get("reportDate") or "")[:8]; a = fnum(e.get("amount"))
                    fxr = fnum(e.get("fxRateToBase")) or 1.0
                    if len(d) == 8 and a:
                        ytd["flows"][d] = ytd["flows"].get(d, 0.0) + a * fxr
                        txn = e.get("transactionID") or ""
                        if txn and txn not in seen_txns:
                            seen_txns.add(txn)
                            ytd.setdefault("flow_rows", []).append({"date": d, "ils": a, "usd": a * fxr, "fx": fxr, "txn": txn})
            # MTM per statement date (ChangeInNAV) — the daily cron re-downloads the same
            # statement date in 2-3 files, so dedupe by date; chained onto the YTD mtm below.
            # (Naive summing double-counts: first attempt gave net $22,871 instead of $41,208.)
            cin = r.find(".//ChangeInNAV")
            if cin is not None:
                d = cin.get("fromDate", "")
                if len(d) == 8: daily_mtm[d] = fnum(cin.get("mtm")) or 0.0
        except Exception: pass
    # gross MTM since inception = YTD mtm + unique daily mtm after the YTD period ends.
    # Verified 8/11/2026: gross $42,397.00, net (MTM chain) $41,217.13 vs NAV-based $41,207.62.
    ytd_mtm = fnum(ytd["changeinnav"].get("mtm")) or 0.0
    ytd_to = ytd.get("stmt_to", "")
    ytd["gross_mtm"] = (ytd_mtm + sum(v for d, v in daily_mtm.items() if not ytd_to or d > ytd_to)) if ytd_mtm else None
    data = {"daily": daily, "ytd": ytd}
    _flex_cache.update({"mtime": mt, "data": data})
    return data

def dstr(d):  # YYYYMMDD -> DD/MM/YYYY
    return "%s/%s/%s" % (d[6:8], d[4:6], d[0:4]) if d and len(d) == 8 else (d or "—")

# ---------- performance ----------
def performance():
    fd = flex_data()
    if not fd: return []
    series = sorted(fd["ytd"]["series"].items())
    if len(series) < 2: return []
    # assign each flow to the first NAV date >= its date (flows may post on non-business days)
    sdates = [d for d, v in series]
    flows = {}
    for fdte, amt in fd["ytd"]["flows"].items():
        tgt = next((d for d in sdates if d >= fdte), sdates[-1] if sdates else fdte)
        flows[tgt] = flows.get(tgt, 0.0) + amt
    end_d, end_v = series[-1]
    end_date = datetime.strptime(end_d, "%Y%m%d").date()
    def nav_on_or_before(target):
        prev = None
        for d, v in series:
            dd = datetime.strptime(d, "%Y%m%d").date()
            if dd <= target: prev = (d, v, dd)
            else: break
        return prev
    def period(label, start_target):
        base = nav_on_or_before(start_target)
        if not base: return {"label": label, "ok": False}
        sd, sv, sdate = base
        if sdate > start_target + timedelta(days=10) and label != "YTD": pass
        # chain TWR over (start, end]
        twr = 1.0; prev_v = sv; netflow = 0.0
        started = False
        for d, v in series:
            dd = datetime.strptime(d, "%Y%m%d").date()
            if dd <= sdate: continue
            fl = flows.get(d, 0.0); netflow += fl
            denom = prev_v
            if denom and denom > 0: twr *= (v - fl) / denom
            prev_v = v; started = True
        if not started: return {"label": label, "ok": False}
        profit = end_v - sv - netflow
        return {"label": label, "ok": True, "pct": (twr - 1) * 100, "profit": profit,
                "start": sd, "end": end_d, "flows": netflow}
    def months_ago(n):
        m = end_date.month - n; y = end_date.year
        while m <= 0: m += 12; y -= 1
        return date(y, m, min(end_date.day, 28))
    out = [period("חודש", months_ago(1)), period("3 חודשים", months_ago(3)),
           period("חצי שנה", months_ago(6)), period("מתחילת השנה", date(end_date.year, 1, 1) - timedelta(days=1)),
           period("שנה", months_ago(12))]
    return out

def bench_return(sym, start_d, end_d):
    q = get_quote(sym, "2y")
    if not q or not q.get("hist"): return None
    hist = [(datetime.strptime(d, "%Y-%m-%d").date(), c) for d, c in q["hist"] if d != "None"]
    if not hist: return None
    s = None; e = None
    for d, c in hist:
        if d <= start_d: s = c
        if d <= end_d: e = c
    if s and e: return (e / s - 1) * 100
    return None

CHART_INDEX = [("^GSPC", "S&P 500", "#f5a623"), ("^NDX", "Nasdaq 100", "#31c573"),
               ("SOXX", "SOXX", "#c792ea"), ("^VIX", "VIX", "#f45d5d")]
def chart_series():
    # Daily TWR index for the portfolio (100 at the first NAV date, flows chained out)
    # + raw daily closes for the comparison indices, aligned to the portfolio's dates.
    # The client re-bases every visible series to 0% at the chosen range start.
    fd = flex_data()
    if not fd: return None
    series = sorted(fd["ytd"]["series"].items())
    if len(series) < 2: return None
    sdates = [d for d, v in series]
    flows = {}
    for fdte, amt in fd["ytd"]["flows"].items():
        tgt = next((d for d in sdates if d >= fdte), sdates[-1] if sdates else fdte)
        flows[tgt] = flows.get(tgt, 0.0) + amt
    idx = []; prev_v = None
    for d, v in series:
        if prev_v is None: idx.append(100.0)
        else:
            fl = flows.get(d, 0.0)
            idx.append(idx[-1] * (v - fl) / prev_v if prev_v and prev_v > 0 else idx[-1])
        prev_v = v
    # cumulative net $ profit (NAV change minus flows) per date — the chart tooltip
    # shows the $ profit since the chosen range start; at the last date it equals
    # the NAV-based net profit ($41,208 on 06/11/2026).
    cum = []; run = 0.0; prev = None
    for d, v in series:
        if prev is not None:
            run += (v - flows.get(d, 0.0) - prev)
        cum.append(round(run, 2))
        prev = v
    out = {"dates": [datetime.strptime(d, "%Y%m%d").strftime("%Y-%m-%d") for d in sdates],
           "pf": [round(x, 4) for x in idx], "profit": cum, "indices": {}}
    for sym, name, color in CHART_INDEX:
        q = get_quote(sym, "2y")
        if not q or not q.get("hist"): continue
        hist = sorted((datetime.strptime(d, "%Y-%m-%d").date(), c)
                      for d, c in q["hist"] if d != "None" and c is not None)
        if not hist: continue
        vals = []
        for ds in sdates:
            dd = datetime.strptime(ds, "%Y%m%d").date()
            c = None
            for hd, hc in hist:
                if hd <= dd: c = hc
                else: break
            vals.append(c)
        if any(v is None for v in vals): continue
        out["indices"][sym] = {"name": name, "color": color, "values": vals}
    return out

# ---------- helpers ----------
def fmt(v, dec=2):
    if v is None: return "—"
    return ("-$" if v < 0 else "$") + f"{abs(v):,.{dec}f}"
def fmt_ils(v, dec=0):
    if v is None: return "—"
    return ("-₪" if v < 0 else "₪") + f"{abs(v):,.{dec}f}"
def pct(v, sign=True):
    if v is None: return "—"
    return (("+" if v >= 0 and sign else "") + f"{v:.1f}%")
def cls(v): return "pos" if (v or 0) >= 0 else "neg"
def esc(s): return html.escape(str(s or ""))
def method_label(m):
    return {"garp": "GARP", "garp_blocked": "GARP — חסום איכות", "value": "ערך (Value)",
            "book_value": "שווי ספר", "none": "ללא שיטה"}.get(m or "", "—")
def entry_label(it):
    return "ראש רצועת הקנייה" if it.get("method") in ("garp", "garp_blocked") else "מחיר כניסה"
def band_bottom(it):
    return it["fairPrice"] * 0.75 if it.get("method") in ("garp", "garp_blocked") and it.get("fairPrice") else None

def since_entry_pct(sym, price, flex_pos):
    # Return since the position started: unrealized / cost (Flex daily), fallback price / avg cost.
    fp = (flex_pos or {}).get(norm(sym))
    if not fp: return None
    cm = fp.get("costMoney")
    if cm:
        un = fp.get("unreal")
        if un is not None: return un / cm * 100
    cp = fp.get("costPrice")
    if cp and price: return (price / cp - 1) * 100
    return None

def dist_line(p, ref):
    # "המחיר ▲ 11.5% מעל" / "המחיר ▼ 20.0% מתחת" — number isolated dir=ltr so RTL never scrambles it.
    if not p or not ref: return None
    d = (p / ref - 1) * 100
    arrow = "▲" if d >= 0 else "▼"
    word = "מעל" if d >= 0 else "מתחת"
    return "המחיר <span dir='ltr'>%s %.1f%%</span> %s" % (arrow, abs(d), word)

def stock_panel_html(panel_id, it, q, flex_pos):
    # Detail panel for one stock: levels track + key values + GARP screenshots ONLY.
    # No generated price chart (removed 8/11/2026 at Oren's request — screenshots only).
    sym = it["symbol"]; p = q["price"] if q else None
    parts = ["<div class='sigpanel' id='%s' hidden>" % panel_id]
    if p:
        trk = levels_track_html(it, p)
        if trk: parts.append(trk)
    # cells are (label, value_html, dist_html): value on its own line, distance on a second line.
    pos_cells = []
    lvl_cells = []
    if q:
        pos_cells.append(("שינוי יום", "<span class='%s'>%s</span>" % (cls(q["dayPct"]), pct(q["dayPct"])), None))
        if q.get("ma150"): lvl_cells.append(("ממוצע 150", fmt(q["ma150"]), dist_line(p, q["ma150"])))
        if q.get("ma200"): lvl_cells.append(("ממוצע 200", fmt(q["ma200"]), dist_line(p, q["ma200"])))
    fair, entry, exitp = it.get("fairPrice"), it.get("entryPrice"), it.get("exitPrice")
    if p and fair: lvl_cells.append(("מחיר הוגן", fmt(fair), dist_line(p, fair)))
    if p and entry: lvl_cells.append((entry_label(it), fmt(entry), dist_line(p, entry)))
    bot = band_bottom(it)
    if bot: lvl_cells.append(("תחתית רצועת קנייה", fmt(bot), None))
    if p and exitp: lvl_cells.append(("מחיר יציאה", fmt(exitp), dist_line(p, exitp)))
    if it["kind"] == "position":
        fp = (flex_pos or {}).get(norm(sym))
        n = fp["qty"] if fp and fp.get("qty") else it.get("shares")
        if n: pos_cells.append(("כמות", "%g" % n, None))
        if p and n: pos_cells.append(("שווי חי", fmt(p * n, 0), None))
        if fp and fp.get("unreal") is not None:
            pos_cells.append(("לא ממומש (IB)", "<span class='%s'>%s</span>" % (cls(fp["unreal"]), fmt(fp["unreal"], 0)), None))
        se = since_entry_pct(sym, p, flex_pos)
        if se is not None:
            pos_cells.append(("תשואה מאז כניסה", "<span class='%s'>%s</span>" % (cls(se), pct(se)), None))
    def kv_grid(cells):
        return "<div class='sigkv'>" + "".join(
            "<div class='skv'><span class='sfk'>%s</span><b dir='ltr'>%s</b>%s</div>" % (esc(k), vv, ("<span class='sdist'>%s</span>" % dd) if dd else "")
            for k, vv, dd in cells) + "</div>"
    if pos_cells:
        parts.append("<div class='muted small' style='margin-top:14px;margin-bottom:6px'>הפוזיציה</div>" + kv_grid(pos_cells))
    if lvl_cells:
        parts.append("<div class='muted small' style='margin-top:14px;margin-bottom:6px'>רמות וממוצעים</div>" + kv_grid(lvl_cells))
    charts = MANIFEST.get(sym) or []
    for c in charts:
        parts.append("<div style='margin-top:12px'><div class='muted small' style='margin-bottom:6px'>%s</div><img class='chart' src='/charts/%s' alt='גרף GARP' loading='lazy'></div>"
                     % (esc(c.get("caption") or "גרף GARP"), esc(os.path.basename(c["file"]))))
    parts.append("<div style='margin-top:12px'><a href='/garp?s=%s'>לדף המניה המלא ←</a></div></div>" % esc(sym))
    return "".join(parts)

def signals_for(it, q):
    # dicts: {text, kind, level:{label, value, band:(bot, top)|None}|None, ma:bool}
    # thresholds / which signals fire: UNCHANGED. Wording reflects the price's
    # actual side of the level (e.g. above exit -> "מעל מחיר היציאה").
    out = []
    if not q: return out
    p = q["price"]; m = it.get("method")
    if m in ("garp", "garp_blocked") and it.get("entryPrice"):
        top = it["entryPrice"]; bot = band_bottom(it)
        lvl = {"label": "ראש רצועת הקנייה", "value": top, "band": (bot, top) if bot else None}
        if bot and p <= bot: out.append({"text": it["symbol"] + " בתוך רצועת הקנייה (מתחת לתחתית הרצועה)", "kind": "good", "level": lvl})
        elif p <= top: out.append({"text": it["symbol"] + " בתוך רצועת הקנייה", "kind": "good", "level": lvl})
        elif p <= top * 1.05: out.append({"text": it["symbol"] + " מתקרב/ת לרצועת הקנייה", "kind": "warn", "level": lvl})
    elif m in ("value", "book_value") and it.get("entryPrice"):
        e = it["entryPrice"]
        lvl = {"label": "מחיר כניסה", "value": e, "band": None}
        if p <= e: out.append({"text": it["symbol"] + " מתחת למחיר הכניסה", "kind": "good", "level": lvl})
        elif p <= e * 1.05: out.append({"text": it["symbol"] + " מתקרב/ת למחיר הכניסה", "kind": "warn", "level": lvl})
    if it.get("exitPrice") and p >= it["exitPrice"] * 0.95:
        ex = it["exitPrice"]
        lvl = {"label": "מחיר יציאה", "value": ex, "band": None}
        w = "מעל מחיר היציאה" if p >= ex else "מתקרב/ת למחיר היציאה"
        out.append({"text": "%s %s" % (it["symbol"], w), "kind": "warn", "level": lvl})
    if q.get("cross") == "golden": out.append({"text": it["symbol"] + " — צלב זהב: ממוצע 150 חצה מעל 200", "kind": "good", "level": None, "ma": True})
    if q.get("cross") == "death": out.append({"text": it["symbol"] + " — צלב מוות: ממוצע 150 חצה מתחת ל־200", "kind": "bad", "level": None, "ma": True})
    return out

# options: OCC from Flex daily positions (exact symbols), fallback to seed expiry
def flex_occ_map(fd):
    m = {}
    if fd and fd.get("daily"):
        for p in fd["daily"]["positions"]:
            if p["cat"] == "OPT":
                occ = p["symbol"].replace(" ", "")
                und = norm(p.get("underlying") or occ)
                m.setdefault(und, []).append({"occ": occ, "qty": p["qty"], "mark": p["mark"], "value": p["value"],
                                               "costMoney": p["costMoney"], "unreal": p["unreal"]})
    return m

def load_options_data(fd):
    # Yahoo option quotes go stale when a contract stops trading (LEAPS): the last
    # trade can be weeks old (META 410C: Yahoo $320.45 from 21/10 vs IB mark $234.46
    # on 06/11 — an $8,599 gap). If Yahoo's quote is older than the Flex report
    # date, use IB's mark from Flex instead (src "flex").
    occ_map = flex_occ_map(fd)
    flex_date = None
    if fd and fd.get("daily") and fd["daily"].get("date"):
        try: flex_date = datetime.strptime(fd["daily"]["date"], "%Y%m%d").date()
        except Exception: flex_date = None
    out = []
    for o in OPTIONS:
        und = o["underlying"]
        fx = (occ_map.get(und) or [{}])
        fx0 = fx[0] if fx else {}
        occ = fx0.get("occ")
        price = None; asof = ""; live = False
        if occ:
            q = get_quote(occ)
            if q:
                mt = q.get("mktTime")
                qdate = datetime.fromtimestamp(mt).date() if mt else None
                if qdate is None or flex_date is None or qdate >= flex_date:
                    price, asof, live = q["price"], time.strftime("%d/%m %H:%M", time.localtime(q["asof"])), True
        if price is None:
            if fx0.get("mark"):
                price, asof, live = fx0["mark"], (dstr(fd["daily"]["date"]) if fd and fd.get("daily") else ""), "flex"
            else:
                price, asof, live = o.get("price"), (o.get("priceAsOf") or "")[:10], False
        out.append((o, price, asof, live, fx0))
    return out

# ================= PRESENTATION LAYER (UI overhaul 2026-10-20) =================
# Data computations above are frozen. Everything below is rendering only.

CSS = """<style>
:root{
  --bg:#07090d; --bg2:#0a0d13; --panel:#10141e; --panel2:#151b29; --panel3:#0c0f16;
  --line:#1f2839; --line2:#2c3a55; --tx:#eef2fa; --tx2:#a9b5cc; --tx3:#68758f;
  --acc:#4da3ff; --acc2:#7cc4ff; --up:#31c573; --down:#f45d5d; --warn:#f2b84b; --vio:#c792ea;
  --up-bg:rgba(49,197,115,.13); --down-bg:rgba(244,93,93,.13); --warn-bg:rgba(242,184,75,.13); --acc-bg:rgba(77,163,255,.12);
  --r:14px; --r-sm:10px; --r-lg:18px; --hdr:58px;
  --shadow:0 10px 28px rgba(0,0,0,.38), 0 2px 6px rgba(0,0,0,.3);
}
*{box-sizing:border-box}
html{color-scheme:dark}
body{margin:0;background:radial-gradient(1100px 480px at 85% -120px,rgba(77,163,255,.09),transparent 60%),radial-gradient(800px 420px at 0% -80px,rgba(49,197,115,.05),transparent 55%),var(--bg);color:var(--tx);font-family:'Heebo',system-ui,'Segoe UI',Arial,sans-serif;direction:rtl;-webkit-font-smoothing:antialiased}
a{color:var(--acc2);text-decoration:none}
a:hover{text-decoration:underline}
.num,.card .v,td,th,.big{font-variant-numeric:tabular-nums lining-nums}
/* ---------- header ---------- */
header{position:sticky;top:0;z-index:50;background:rgba(9,12,18,.88);backdrop-filter:blur(14px);-webkit-backdrop-filter:blur(14px);border-bottom:1px solid var(--line)}
.hwrap{max-width:1560px;margin:0 auto;padding:0 16px;height:var(--hdr);display:flex;gap:16px;align-items:center}
.brand{display:flex;align-items:center;gap:9px;font-weight:800;font-size:16.5px;color:var(--tx);white-space:nowrap}
.brand svg{display:block}
nav.mainnav{display:flex;gap:4px}
nav.mainnav a{color:var(--tx2);font-size:14px;padding:7px 12px;border-radius:9px;transition:background .15s,color .15s}
nav.mainnav a:hover{color:var(--tx);background:var(--panel2);text-decoration:none}
nav.mainnav a.on{color:#fff;background:var(--panel2);box-shadow:inset 0 -2px 0 var(--acc);font-weight:700}
.hside{margin-inline-start:auto;display:flex;align-items:center;gap:10px}
.clock{font-size:12.5px;color:var(--tx2);font-variant-numeric:tabular-nums;white-space:nowrap}
.mkt{display:inline-flex;align-items:center;gap:6px;font-size:11.5px;font-weight:600;padding:4px 10px;border-radius:20px;border:1px solid var(--line2);color:var(--tx2);white-space:nowrap}
.mkt .dot{width:7px;height:7px;border-radius:50%;background:var(--tx3)}
.mkt.open{color:#8fe6b4;border-color:rgba(49,197,115,.45);background:var(--up-bg)} .mkt.open .dot{background:var(--up);animation:pulse 1.8s infinite}
.mkt.pre{color:#ffd98a;border-color:rgba(242,184,75,.45);background:var(--warn-bg)} .mkt.pre .dot{background:var(--warn)}
@keyframes pulse{0%{box-shadow:0 0 0 0 rgba(49,197,115,.5)}70%{box-shadow:0 0 0 6px rgba(49,197,115,0)}100%{box-shadow:0 0 0 0 rgba(49,197,115,0)}}
.asof{font-size:11px;color:var(--tx3);white-space:nowrap}
.asofline{font-size:11.5px;color:var(--tx3);margin:0 2px 12px}
/* ---------- layout ---------- */
main{max-width:1560px;margin:0 auto;padding:18px 16px 56px}
h2.sec{margin:26px 0 12px;font-size:16px;font-weight:800;display:flex;align-items:center;gap:8px}
h2.sec::before{content:"";width:4px;height:17px;border-radius:2px;background:linear-gradient(180deg,var(--acc),rgba(77,163,255,.25))}
h2.sec:first-child{margin-top:2px}
.grid{display:grid;gap:12px;margin:12px 0}
.g-perf{grid-template-columns:repeat(auto-fit,minmax(205px,1fr))}
.g-3{grid-template-columns:repeat(auto-fit,minmax(230px,1fr))}
.g-2{grid-template-columns:repeat(auto-fit,minmax(300px,1fr))}
.g-idx{grid-template-columns:repeat(auto-fit,minmax(160px,1fr))}
.g-mov{grid-template-columns:repeat(auto-fit,minmax(150px,1fr))}
.g-snap{grid-template-columns:repeat(3,1fr)}
.snap .q{font-size:13px;color:var(--tx2);font-weight:700}
.snap .v{font-size:30px;font-weight:850;margin-top:4px;letter-spacing:-.3px}
.snap .s{font-size:12.5px;color:var(--tx2);margin-top:6px;line-height:1.55}
.card{background:linear-gradient(180deg,var(--panel2),var(--panel));border:1px solid var(--line);border-radius:var(--r);padding:15px 16px;box-shadow:0 1px 0 rgba(255,255,255,.02) inset}
.card .t{color:var(--tx2);font-size:12.5px;font-weight:600}
.card .v{font-size:24px;font-weight:800;margin-top:5px;letter-spacing:-.2px}
.card .s{font-size:12px;color:var(--tx3);margin-top:4px;line-height:1.5}
.pos{color:var(--up)} .neg{color:var(--down)} .warn{color:var(--warn)} .muted{color:var(--tx3)} .small{font-size:12px}
.pill{display:inline-flex;align-items:center;gap:4px;font-weight:700;font-size:13px;padding:3px 10px;border-radius:20px;font-variant-numeric:tabular-nums;direction:ltr}
.pill.pos{background:rgba(49,197,115,.22);border:1px solid rgba(49,197,115,.45)} .pill.neg{background:rgba(244,93,93,.22);border:1px solid rgba(244,93,93,.45)}
.badge{display:inline-block;background:rgba(49,197,115,.12);color:#8fe6b4;border:1px solid rgba(49,197,115,.35);border-radius:20px;padding:1px 9px;font-size:12px;font-weight:600}
.chip{display:inline-block;background:#1a2336;border:1px solid var(--line2);border-radius:14px;padding:1px 8px;font-size:11.5px;margin-inline-end:4px;color:var(--tx2)}
a.chip{color:var(--acc2)} a.chip:hover{border-color:var(--acc);text-decoration:none}
/* ---------- hero ---------- */
.hero{background:linear-gradient(150deg,#131b2c,#0c1119 55%,#0a0e15);border:1px solid #263450;border-radius:var(--r-lg);padding:20px 20px 8px;box-shadow:var(--shadow);overflow:hidden}
.hero .t{color:var(--tx2);font-size:13px;font-weight:600}
.hero .v{font-size:clamp(34px,6vw,46px);font-weight:850;letter-spacing:-.5px;margin-top:2px}
.hero .sub{font-size:12.5px;color:var(--tx3);margin-top:3px}
.hero .dayline{margin-top:12px;display:flex;flex-wrap:wrap;gap:10px;align-items:center;font-size:13.5px}
.chartwrap{position:relative;margin-top:8px}
.chartwrap svg{display:block;width:100%;height:auto}
.chtip{position:absolute;top:2px;background:#0a0e16;border:1px solid var(--line2);border-radius:8px;padding:4px 9px;font-size:12px;pointer-events:none;opacity:0;transition:opacity .12s;white-space:nowrap;box-shadow:var(--shadow);z-index:3}
.chartwrap:hover .chtip{opacity:1}
.axislbl{font-size:10.5px;fill:var(--tx3)}
/* ---------- perf cards ---------- */
.perf .pv{font-size:27px;font-weight:850;margin:2px 0 1px}
.perf .profit{font-size:13px;font-weight:700}
.bench{margin-top:10px;border-top:1px dashed var(--line);padding-top:9px;display:grid;gap:7px}
.bench .brow{display:grid;grid-template-columns:64px 52px 1fr auto;align-items:center;gap:8px;font-size:12px}
.bench .bname{color:var(--tx2);font-weight:600}
.bench .bpct{font-weight:700;text-align:left;font-variant-numeric:tabular-nums}
.btrack{height:5px;background:#1a2130;border-radius:3px;overflow:hidden}
.bfill{height:100%;border-radius:3px;background:var(--acc)}
.bfill.up{background:var(--up)} .bfill.down{background:var(--down)}
.gap{font-size:11px;font-weight:700;padding:1px 7px;border-radius:12px;background:var(--panel3);border:1px solid var(--line)}
.gap.pos{color:var(--up)} .gap.neg{color:var(--down)}
.nodata{border:1px dashed var(--line2);border-radius:var(--r);padding:15px 16px;background:rgba(255,255,255,.015);color:var(--tx3)}
.nodata .t{font-weight:700;color:var(--tx2);font-size:13.5px}
.foot{color:var(--tx3);font-size:12px;line-height:1.6;margin:8px 2px}
.chart-ctrl{display:flex;flex-wrap:wrap;gap:10px;justify-content:space-between;margin-bottom:12px}
.ranges,.chips{display:flex;gap:6px;flex-wrap:wrap}
.rbtn,.chip{cursor:pointer;border:1px solid var(--line2);background:var(--panel2);color:var(--tx2);border-radius:999px;padding:6px 14px;font-size:13px;font-family:inherit}
.rbtn.on{border-color:var(--acc);color:#fff;background:#16283f}
.chip.on{border-color:var(--c);color:#fff;background:#16283f}
.chart-wrap{position:relative;overflow-x:auto}
.chart-wrap svg{min-width:720px}
.chart-tip{position:absolute;z-index:5;background:#0d1320;border:1px solid var(--line2);border-radius:8px;padding:8px 10px;font-size:12.5px;pointer-events:none;min-width:150px;box-shadow:0 6px 18px rgba(0,0,0,.45);line-height:1.7}
.chart-tip .sw{display:inline-block;width:9px;height:9px;border-radius:50%;margin-left:5px}
.chart-legend{display:flex;flex-wrap:wrap;gap:16px;margin-top:10px;font-size:13.5px;color:var(--tx2)}
.lg-item .sw{display:inline-block;width:9px;height:9px;border-radius:50%;margin-left:5px}
/* ---------- donut / bars ---------- */
.donut-flex{display:flex;gap:18px;align-items:center;flex-wrap:wrap}
.donutwrap{position:relative;width:148px;height:148px;flex:0 0 auto;margin:0 auto}
.donutwrap svg{transform:rotate(-90deg)}
.donut-c{position:absolute;inset:0;display:flex;flex-direction:column;align-items:center;justify-content:center;text-align:center}
.donut-c .dv{font-size:19px;font-weight:850}
.donut-c .dt{font-size:11px;color:var(--tx3)}
.legend{flex:1;min-width:170px;display:grid;gap:9px}
.lrow{display:flex;align-items:center;gap:8px;font-size:13px}
.lrow .sw{width:10px;height:10px;border-radius:3px;flex:0 0 auto}
.lrow .lv{margin-inline-start:auto;font-weight:700}
.lrow .lp{color:var(--tx3);font-size:12px;min-width:44px;text-align:left}
.hbar-row{display:grid;grid-template-columns:86px 1fr auto;gap:10px;align-items:center;margin-top:10px;font-size:13px}
.hbar-track{height:9px;background:#1a2130;border-radius:5px;overflow:hidden}
.hbar-fill{height:100%;border-radius:5px}
.gauge{margin-top:10px}
.gauge .gtrack{position:relative;height:10px;background:linear-gradient(90deg,#274058,#3d5a80);border-radius:6px}
.gauge .gfill{position:absolute;top:0;bottom:0;inset-inline-start:0;background:linear-gradient(90deg,var(--acc),var(--acc2));border-radius:6px}
.gauge .gtick{position:absolute;top:-4px;width:2px;height:18px;background:var(--warn)}
.gauge .glbls{display:flex;justify-content:space-between;font-size:11px;color:var(--tx3);margin-top:5px}
/* ---------- signals ---------- */
.sigfeed{display:grid;gap:8px}
.sigrow{display:flex;gap:11px;align-items:flex-start;background:var(--panel);border:1px solid var(--line);border-radius:var(--r-sm);padding:11px 14px;font-size:14px;line-height:1.5}
.sigic{flex:0 0 auto;width:26px;height:26px;border-radius:8px;display:flex;align-items:center;justify-content:center;margin-top:1px}
.sigic.good{background:var(--up-bg);color:var(--up)} .sigic.warn{background:var(--warn-bg);color:var(--warn)} .sigic.bad{background:var(--down-bg);color:var(--down)} .sigic.info{background:var(--acc-bg);color:var(--acc2)}
.sigrow a.sym{font-weight:800;color:var(--tx)} .sigrow a.sym:hover{color:var(--acc2);text-decoration:none}
.sigrow{flex-wrap:wrap}
.sigmain{flex:1 1 200px}
.sigfields{display:flex;gap:7px 16px;flex-wrap:wrap;align-items:center;margin-inline-start:auto}
.sigfields .sf{display:inline-flex;align-items:baseline;gap:6px;white-space:nowrap}
.sfk{color:var(--tx3);font-size:11.5px;font-weight:600}
.sigfields .sf b{font-size:13.5px;font-variant-numeric:tabular-nums}
.sigrow .chev{flex:0 0 auto;color:var(--tx3);align-self:center;transition:transform .18s}
.sigrow[data-exp]{cursor:pointer}
.sigrow[data-exp]:hover{border-color:var(--line2)}
.sigrow.open{border-radius:var(--r-sm) var(--r-sm) 0 0;border-color:var(--line2)}
.sigrow.open .chev{transform:rotate(180deg)}
tr.posrow{cursor:pointer}
tr.posrow.open .chev{transform:rotate(180deg)}
tr.panelrow td{padding:0;border:none}
/* mobile positions cards (shown instead of the table under 760px) */
.poscards{display:none}
.poscard{background:var(--panel3);border:1px solid var(--line);border-radius:var(--r-sm);padding:12px 14px;cursor:pointer}
.poscard.open{border-radius:var(--r-sm) var(--r-sm) 0 0;border-color:var(--line2)}
.poscard.open .chev{transform:rotate(180deg)}
.poscard .chev{flex:0 0 auto;color:var(--tx3);transition:transform .18s}
.pc-top{display:flex;align-items:baseline;gap:8px}
.pc-sym{font-size:15px}
.pc-name{color:var(--tx3);font-size:12.5px;flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.pc-val{font-weight:800;font-size:16px;direction:ltr;font-variant-numeric:tabular-nums}
.pc-row{display:flex;align-items:center;gap:6px;margin-top:9px}
.pc-meta{color:var(--tx3);font-size:12px;margin-inline-start:auto;direction:ltr;white-space:nowrap}
.sigpanel{background:var(--panel3);border:1px solid var(--line2);border-top:none;border-radius:0 0 var(--r-sm) var(--r-sm);padding:14px 16px 16px}
.xcard{cursor:pointer}
.xcard .chev{flex:0 0 auto;color:var(--tx3);transition:transform .18s}
.xcard.open .chev{transform:rotate(180deg)}
.xpanel{grid-column:1/-1;background:var(--panel3);border:1px solid var(--line2);border-radius:var(--r);padding:14px 16px}
/* detail panels: key-value rows, never wide tables (mobile-safe, no RTL clipping) */
.xpanel .pt{font-size:13px;font-weight:700;color:var(--tx2);margin-bottom:4px}
.drow{display:flex;justify-content:space-between;align-items:baseline;gap:14px;padding:9px 2px;border-bottom:1px solid var(--line);font-size:13.5px}
.drow:last-child{border-bottom:none}
.drow .dl{color:var(--tx2);min-width:0}
.drow .dl .muted{font-size:12px}
.drow.sub .dl{padding-right:14px}
.drow .dv{flex:0 0 auto;text-align:left;white-space:nowrap}
.drow .dv .muted{font-size:12px;font-weight:400}
.drow.tot{font-weight:700;border-top:1px solid var(--line2);padding-top:11px;margin-top:2px}
.drow.tot .dl{color:var(--tx1)}
.xpanel .pfoot{font-size:12px;color:var(--tx3);margin-top:10px;line-height:1.5}
.sigpanel>svg{width:100%;height:auto;display:block}
.sigkv{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:8px;margin-top:12px}
.sigkv .skv{background:var(--panel);border:1px solid var(--line);border-radius:9px;padding:10px 12px;min-width:0}
.sigkv .skv .sfk{display:block;margin-bottom:2px}
.sigkv .skv b{font-size:16px;font-variant-numeric:tabular-nums}
.sigkv .sdist{display:block;font-size:12px;color:var(--tx2);margin-top:3px}
/* ---------- movers / indices ---------- */
.tile .tv{font-size:19px;font-weight:800}
.tile .tsym{font-weight:800;font-size:14.5px}
.tile .trow{display:flex;justify-content:space-between;align-items:center;gap:8px}
.spark{display:block}
/* ---------- tables ---------- */
.tblwrap{overflow-x:auto;-webkit-overflow-scrolling:touch;scrollbar-width:thin;scrollbar-color:#2c3a55 transparent;border:1px solid var(--line);border-radius:var(--r);background:var(--panel3);box-shadow:0 1px 0 rgba(255,255,255,.02) inset}
.tblwrap::-webkit-scrollbar{height:8px;width:8px}
.tblwrap::-webkit-scrollbar-thumb{background:#2c3a55;border-radius:4px}
.tblwrap::-webkit-scrollbar-track{background:transparent}
table{width:100%;border-collapse:separate;border-spacing:0;font-size:13.5px;font-variant-numeric:tabular-nums}
th,td{padding:9px 10px;border-bottom:1px solid #171e2c;text-align:right;white-space:nowrap;vertical-align:middle}
thead th{color:var(--tx2);font-weight:700;background:#131926;font-size:12.5px;position:sticky;top:0;z-index:4;border-bottom:1px solid var(--line2)}
tbody tr{transition:background .12s}
tbody tr:hover{background:rgba(77,163,255,.05)}
tr.clickable{cursor:pointer}
table.sortable thead th[data-sort]{cursor:pointer;user-select:none}
table.sortable thead th[data-sort]:hover{color:var(--tx)}
table.sortable thead th .arr{font-size:10px;color:var(--acc)}
.pnlwrap{display:flex;flex-direction:column;gap:3px;align-items:flex-start}
.pnlbar{width:64px;height:4px;background:#1a2130;border-radius:2px;overflow:hidden}
.pnlbar i{display:block;height:100%;border-radius:2px}
.searchbar{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin:12px 0}
.searchbar input[type=search]{background:var(--panel);border:1px solid var(--line2);color:var(--tx);border-radius:10px;padding:9px 13px;font-size:14px;min-width:210px;font-family:inherit}
.searchbar input[type=search]:focus{outline:2px solid rgba(77,163,255,.5);border-color:var(--acc)}
.toggle{display:inline-flex;background:var(--panel);border:1px solid var(--line2);border-radius:12px;padding:3px;gap:2px}
.toggle a{padding:6px 16px;border-radius:9px;color:var(--tx2);font-size:13.5px;font-weight:600;transition:all .15s}
.toggle a:hover{color:var(--tx);text-decoration:none}
.toggle a.on{background:#22314e;color:#fff;font-weight:700;box-shadow:0 2px 8px rgba(0,0,0,.35)}
.closedtbl{opacity:.78} .closedtbl thead th{background:#10141d}
/* ---------- options cards ---------- */
.optgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(265px,1fr));gap:12px}
.optcard .ohead{display:flex;align-items:center;gap:9px}
.optcard .osym{font-size:19px;font-weight:850}
.otype{font-size:11px;font-weight:800;padding:2px 9px;border-radius:12px;background:var(--acc-bg);color:var(--acc2);border:1px solid rgba(77,163,255,.35)}
.otype.put{background:var(--warn-bg);color:var(--warn);border-color:rgba(242,184,75,.35)}
.ochips{display:flex;flex-wrap:wrap;gap:6px;margin-top:11px}
.ochip{background:var(--panel3);border:1px solid var(--line);border-radius:9px;padding:5px 9px;font-size:12px;color:var(--tx2)}
.ochip b{color:var(--tx);font-variant-numeric:tabular-nums}
.money{margin-top:12px}
.money .mtrack{position:relative;height:8px;background:#1a2130;border-radius:5px}
.money .mstrike{position:absolute;top:-3px;width:2px;height:14px;background:var(--warn)}
.money .mprice{position:absolute;top:50%;width:11px;height:11px;border-radius:50%;background:var(--acc2);border:2px solid #0a0e16;transform:translate(50%,-50%);box-shadow:0 0 0 3px rgba(124,196,255,.25)}
.money .mlbls{display:flex;justify-content:space-between;font-size:11px;color:var(--tx3);margin-top:5px}
.orow{display:flex;justify-content:space-between;align-items:baseline;margin-top:10px;border-top:1px dashed var(--line);padding-top:9px}
.orow .ov{font-size:19px;font-weight:800}
/* ---------- stock detail ---------- */
.stockhead{background:linear-gradient(150deg,#131b2c,#0b0f16);border:1px solid #263450;border-radius:var(--r-lg);padding:18px 20px;box-shadow:var(--shadow)}
.stockhead .ssym{font-size:15px;color:var(--tx2);font-weight:700}
.stockhead .sprice{font-size:clamp(32px,5.5vw,42px);font-weight:850;letter-spacing:-.5px}
.w52{margin-top:14px;max-width:520px}
.w52 .wtrack{position:relative;height:8px;border-radius:5px;background:linear-gradient(90deg,rgba(244,93,93,.55),rgba(242,184,75,.5) 50%,rgba(49,197,115,.55))}
.w52 .wmark{position:absolute;top:50%;width:13px;height:13px;border-radius:50%;background:#fff;border:3px solid #0a0e16;transform:translate(50%,-50%);box-shadow:0 1px 6px rgba(0,0,0,.5)}
.w52 .wlbls{display:flex;justify-content:space-between;font-size:11.5px;color:var(--tx3);margin-top:6px;font-variant-numeric:tabular-nums}
.legendrow{display:flex;flex-wrap:wrap;gap:14px;margin-top:10px;font-size:12.5px;color:var(--tx2)}
.legendrow .li{display:inline-flex;align-items:center;gap:6px}
.legendrow .sw{width:16px;height:3px;border-radius:2px}
.legendrow .swd{width:16px;border-top:3px dashed}
/* levels track */
.lvl{position:relative;height:128px;margin:36px 10px 6px;direction:ltr}
.lvl .basetrack{position:absolute;left:0;right:0;top:48px;height:12px;border-radius:6px;background:#1a2130}
.lvl .bandseg{position:absolute;top:48px;height:12px;border-radius:6px;background:linear-gradient(90deg,rgba(49,197,115,.55),rgba(49,197,115,.3));border:1px solid rgba(49,197,115,.5)}
.lvl .lmk{position:absolute;top:43px;width:2px;height:22px;background:var(--tx2)}
.lvl .lmk span{position:absolute;left:50%;transform:translateX(-50%);white-space:nowrap;font-size:11.5px;font-weight:700}
.lvl .lmk.fair{background:var(--acc2)} .lvl .lmk.fair span{color:var(--acc2)}
.lvl .lmk.exit{background:var(--down)} .lvl .lmk.exit span{color:var(--down)}
.lvl .lmk.band{background:var(--up)} .lvl .lmk.band span{color:var(--up)}
.lvl .pmark{position:absolute;top:45px;width:18px;height:18px;border-radius:50%;background:#fff;border:3px solid var(--acc);transform:translateX(-50%);box-shadow:0 0 0 5px rgba(77,163,255,.22);z-index:2}
.lvl .pmark span{position:absolute;left:50%;transform:translateX(-50%);bottom:26px;white-space:nowrap;font-size:12.5px;font-weight:800;color:#fff;background:var(--acc);padding:3px 10px;border-radius:20px}
.lvl .bandlbl{position:absolute;transform:translateX(-50%);font-size:11px;color:#8fe6b4;white-space:nowrap;font-weight:700}
.kv{display:grid;grid-template-columns:repeat(auto-fit,minmax(165px,1fr));gap:10px}
.kv .card .v{font-size:19px}
select{background:var(--panel);color:var(--tx);border:1px solid var(--line2);border-radius:10px;padding:9px 12px;font-size:15px;font-family:inherit}
select:focus{outline:2px solid rgba(77,163,255,.5)}
.note{white-space:pre-wrap;line-height:1.65;background:var(--panel);border:1px solid var(--line);border-radius:var(--r);padding:15px 17px;font-size:14px}
img.chart{max-width:100%;border-radius:var(--r-sm);display:block}
.framecard{padding:12px}
.framecard .cap{font-size:12.5px;color:var(--tx2);margin:2px 2px 9px;font-weight:600}
/* ---------- daily ---------- */
.datepills{display:flex;gap:7px;flex-wrap:wrap;margin:12px 0 4px}
.datepills a{padding:6px 14px;border-radius:20px;border:1px solid var(--line2);color:var(--tx2);font-size:13px;font-weight:600;font-variant-numeric:tabular-nums}
.datepills a:hover{text-decoration:none;color:var(--tx);border-color:var(--acc)}
.datepills a.on{background:#22314e;color:#fff;border-color:#3d5a80}
.hl-item{display:flex;gap:11px;background:linear-gradient(180deg,var(--panel2),var(--panel));border:1px solid var(--line);border-inline-start:3px solid var(--acc);border-radius:var(--r-sm);padding:12px 15px;font-size:14.5px;line-height:1.6}
.hl-num{flex:0 0 auto;width:24px;height:24px;border-radius:50%;background:var(--acc-bg);color:var(--acc2);font-weight:800;font-size:13px;display:flex;align-items:center;justify-content:center;margin-top:1px}
.sechead{display:flex;align-items:center;gap:9px;margin:26px 0 6px}
.sechead h2{margin:0;font-size:16px;font-weight:800}
.srcdot{width:11px;height:11px;border-radius:4px;flex:0 0 auto}
.count{font-size:11.5px;font-weight:700;background:var(--panel2);border:1px solid var(--line2);border-radius:12px;padding:1px 9px;color:var(--tx2)}
.ditem{background:var(--panel);border:1px solid var(--line);border-radius:var(--r);padding:14px 16px;margin:9px 0;transition:border-color .15s}
.ditem:hover{border-color:var(--line2)}
.ditem h3{margin:0 0 6px;font-size:15.5px;line-height:1.5}
.ditem h3 a{color:var(--tx)} .ditem h3 a:hover{color:var(--acc2)}
.ditem p{margin:0;line-height:1.65;color:#c9d3e6;font-size:14px}
.ditem .meta{margin-top:9px;font-size:12px;color:var(--tx3);display:flex;flex-wrap:wrap;gap:7px;align-items:center}
.srclink{font-weight:700}
.empty{border:1px dashed var(--line2);border-radius:var(--r);padding:16px;color:var(--tx3);font-size:13.5px;background:rgba(255,255,255,.015)}
/* ---------- bottom tabs ---------- */
.tabbar{display:none}
@media (max-width:760px){
  nav.mainnav{display:none}
  .clock{display:none}
  main{padding:14px 12px 96px}
  .tabbar{display:flex;position:fixed;bottom:0;left:0;right:0;z-index:60;background:rgba(9,12,18,.94);backdrop-filter:blur(14px);border-top:1px solid var(--line);padding:6px 4px calc(6px + env(safe-area-inset-bottom))}
  .tabbar a{flex:1;display:flex;flex-direction:column;align-items:center;gap:2px;color:var(--tx3);font-size:10.5px;font-weight:600;padding:5px 0 3px;border-radius:10px}
  .tabbar a.on{color:var(--acc2)}
  .tabbar a:hover{text-decoration:none}
  .hero{padding:16px 14px 6px}
  .g-snap{grid-template-columns:1fr}
  .snap .v{font-size:28px}
  .mini-tbl{display:none}
  .poscards{display:grid;gap:10px;grid-template-columns:minmax(0,1fr)}
  .stockhead{padding:15px 14px}
  th,td{padding:8px 8px}
}
:focus-visible{outline:2px solid rgba(77,163,255,.6);outline-offset:2px}
</style>"""

JS = """<script>
(function(){
  function tick(){
    var c=document.getElementById('clock'); if(!c) return;
    var now=new Date();
    c.textContent=now.toLocaleTimeString('he-IL',{timeZone:'Asia/Jerusalem',hour12:false,hour:'2-digit',minute:'2-digit',second:'2-digit'});
    var m=document.getElementById('mkt'); if(!m) return;
    try{
      var et=new Date(now.toLocaleString('en-US',{timeZone:'America/New_York'}));
      var day=et.getDay(), mins=et.getHours()*60+et.getMinutes(), lbl, st;
      if(day===0||day===6){lbl='בורסת ארה״ב · סגור (סוף שבוע)';st='';}
      else if(mins>=570&&mins<960){lbl='בורסת ארה״ב · מסחר פעיל';st='open';}
      else if(mins>=240&&mins<570){lbl='בורסת ארה״ב · טרום־מסחר';st='pre';}
      else if(mins>=960&&mins<1200){lbl='בורסת ארה״ב · אחרי־מסחר';st='pre';}
      else {lbl='בורסת ארה״ב · סגור';st='';}
      m.className='mkt '+st; m.innerHTML='<span class="dot"></span>'+lbl;
    }catch(e){}
  }
  tick(); setInterval(tick,1000);
  // NAV chart crosshair
  document.querySelectorAll('.chartwrap').forEach(function(w){
    var svg=w.querySelector('svg[data-pts]'); if(!svg) return;
    var pts; try{pts=JSON.parse(svg.getAttribute('data-pts'));}catch(e){return;}
    var line=svg.querySelector('.ch-line'), dot=svg.querySelector('.ch-dot'), tip=w.querySelector('.chtip');
    if(!line||!dot||!tip) return;
    var vb=svg.viewBox.baseVal;
    function move(ev){
      var r=svg.getBoundingClientRect();
      var x=(ev.touches?ev.touches[0].clientX:ev.clientX)-r.left;
      var fx=Math.max(0,Math.min(1,x/r.width));
      var i=Math.round(fx*(pts.length-1));
      var px=vb.x+fx*vb.width;
      line.setAttribute('x1',px); line.setAttribute('x2',px); line.style.opacity=1;
      var ns=svg.namespaceURI;
      dot.setAttribute('cx',px); dot.style.opacity=1;
      var yv=pts[i][2]; dot.setAttribute('cy',yv);
      tip.textContent=pts[i][0]+' · '+pts[i][1];
      tip.style.right='auto'; tip.style.left=Math.max(0,Math.min(r.width-120, x-60))+'px';
    }
    function leave(){ line.style.opacity=0; dot.style.opacity=0; }
    svg.addEventListener('mousemove',move); svg.addEventListener('touchmove',move,{passive:true}); svg.addEventListener('mouseleave',leave);
  });
  // sortable tables
  function numOf(td){
    if(!td) return null;
    var dv=td.getAttribute('data-v'); if(dv!==null&&dv!=='') return parseFloat(dv);
    var t=td.textContent.replace(/[$₪,%\\s]/g,'').replace(/\\(/g,'-').replace(/\\)/g,'');
    var m=t.match(/-?\\d+(\\.\\d+)?/); return m?parseFloat(m[0]):null;
  }
  document.querySelectorAll('table.sortable').forEach(function(tbl){
    var ths=tbl.querySelectorAll('thead th');
    ths.forEach(function(th,ci){
      if(th.getAttribute('data-sort')==='no') return;
      th.setAttribute('data-sort','1');
      th.addEventListener('click',function(){
        var tb=tbl.querySelector('tbody'); if(!tb) return;
        var rows=Array.prototype.slice.call(tb.querySelectorAll('tr'));
        var dir=th.getAttribute('data-dir')==='asc'?-1:1;
        ths.forEach(function(o){o.removeAttribute('data-dir'); var a=o.querySelector('.arr'); if(a) a.remove();});
        th.setAttribute('data-dir',dir===1?'asc':'desc');
        var arr=document.createElement('span'); arr.className='arr'; arr.textContent=dir===1?' ▲':' ▼'; th.appendChild(arr);
        rows.sort(function(a,b){
          var na=numOf(a.children[ci]), nb=numOf(b.children[ci]);
          if(na!==null&&nb!==null) return (na-nb)*dir;
          var ta=a.children[ci]?a.children[ci].textContent:'' , tb2=b.children[ci]?b.children[ci].textContent:'';
          return ta.localeCompare(tb2,'he')*dir;
        });
        rows.forEach(function(r){tb.appendChild(r);});
      });
    });
  });
  // search filter
  var si=document.getElementById('tblsearch');
  if(si){ si.addEventListener('input',function(){
    var q=si.value.trim().toLowerCase();
    document.querySelectorAll('[data-filter-rows] tbody tr').forEach(function(r){
      r.style.display=(!q||r.textContent.toLowerCase().indexOf(q)>=0)?'':'none';
    });
  });}
  // clickable rows
  document.querySelectorAll('tr[data-href]').forEach(function(r){
    r.addEventListener('click',function(e){ if(e.target.closest('a')) return; window.location=r.getAttribute('data-href'); });
  });
  // accordion: click a row to expand its panel (one open at a time) — signals rows and positions rows
  document.querySelectorAll('[data-exp]').forEach(function(row){
    var panel=document.getElementById(row.getAttribute('data-exp')); if(!panel) return;
    function toggle(){
      var willOpen=panel.hasAttribute('hidden');
      document.querySelectorAll('.sigpanel').forEach(function(pn){ pn.setAttribute('hidden',''); });
      document.querySelectorAll('[data-exp]').forEach(function(r){ r.setAttribute('aria-expanded','false'); r.classList.remove('open'); });
      if(willOpen){ panel.removeAttribute('hidden'); row.setAttribute('aria-expanded','true'); row.classList.add('open'); }
    }
    row.addEventListener('click',function(e){ if(e.target.closest('a')) return; toggle(); });
    row.addEventListener('keydown',function(e){ if(e.target.closest('a')) return; if(e.key==='Enter'||e.key===' '){ e.preventDefault(); toggle(); } });
  });
  // performance chart: one IB-style chart, YTD default; week/month/3m/ytd ranges; index toggles
  var pd = window.PERF_DATA;
  if (pd && document.getElementById('perfchart')) {
    var curRange = 'ytd';
    var onIdx = {'^GSPC': true, '^NDX': true};
    var CH = {w: 1000, h: 330, pl: 14, pr: 58, pt: 14, pb: 30};  // y-axis (%) on the RIGHT (Oren, 8/11/2026)
    function rangeStart(range) {
      var dates = pd.dates, n = dates.length, last = dates[n - 1];
      if (range === 'ytd') {
        // the series starts at the prior year-end NAV (31/12) — the TWR base the
        // hero and profit card measure from; keep it so the chart's % and $ match them.
        return 0;
      }
      var days = range === 'week' ? 7 : range === 'month' ? 30 : 90;
      var d = new Date(last + 'T12:00:00'); d.setDate(d.getDate() - days);
      var iso = d.toISOString().slice(0, 10);
      for (var i = 0; i < n; i++) if (dates[i] >= iso) return i;
      return 0;
    }
    function seriesPct(vals, s) {
      var v0 = vals[s]; var out = [];
      for (var i = s; i < vals.length; i++) out.push(v0 ? (vals[i] / v0 - 1) * 100 : 0);
      return out;
    }
    function niceStep(span) {
      var raw = span / 4, mag = Math.pow(10, Math.floor(Math.log10(raw)));
      var n = raw / mag;
      return (n < 1.5 ? 1 : n < 3.5 ? 2 : n < 7.5 ? 5 : 10) * mag;
    }
    function draw() {
      var s = rangeStart(curRange);
      var series = [{name: 'התיק', color: '#4da3ff', width: 2.6, vals: seriesPct(pd.pf, s)}];
      Object.keys(pd.indices).forEach(function(sym) {
        if (!onIdx[sym]) return;
        var ix = pd.indices[sym];
        series.push({name: ix.name, color: ix.color, width: 1.8, vals: seriesPct(ix.values, s)});
      });
      var n = pd.pf.length - s;
      var all = []; series.forEach(function(x) { all = all.concat(x.vals); });
      var mn = Math.min.apply(null, all), mx = Math.max.apply(null, all);
      var pad = Math.max((mx - mn) * 0.12, 1);
      mn -= pad; mx += pad;
      var step = niceStep(mx - mn);
      var W = CH.w, H = CH.h, iw = W - CH.pl - CH.pr, ih = H - CH.pt - CH.pb;
      function X(i) { return CH.pl + (n <= 1 ? 0 : i / (n - 1)) * iw; }
      function Y(v) { return CH.pt + (1 - (v - mn) / (mx - mn)) * ih; }
      var svg = "<svg viewBox='0 0 " + W + " " + H + "' style='width:100%;height:auto;display:block' role='img'>";
      var g0 = Math.ceil(mn / step) * step;
      for (var g = g0; g <= mx; g += step) {
        var gy = Y(g);
        var zero = Math.abs(g) < 1e-9;
        svg += "<line x1='" + CH.pl + "' y1='" + gy.toFixed(1) + "' x2='" + (W - CH.pr) + "' y2='" + gy.toFixed(1) + "' stroke='" + (zero ? '#3a4a66' : '#1d2637') + "' stroke-width='" + (zero ? 1.4 : 1) + "'/>";
        svg += "<text x='" + (W - CH.pr + 8) + "' y='" + (gy + 4).toFixed(1) + "' fill='#8b98ad' font-size='12' text-anchor='start' direction='ltr'>" + (g > 0 ? '+' : '') + g.toFixed(0) + "%</text>";
      }
      var ticks = 5;
      for (var t = 0; t < ticks; t++) {
        var ti = Math.round(t * (n - 1) / (ticks - 1));
        var ds = pd.dates[s + ti];
        svg += "<text x='" + X(ti).toFixed(1) + "' y='" + (H - 8) + "' fill='#8b98ad' font-size='12' text-anchor='middle'>" + ds.slice(8, 10) + '/' + ds.slice(5, 7) + "</text>";
      }
      series.forEach(function(x) {
        var pts = x.vals.map(function(v, i) { return X(i).toFixed(1) + ',' + Y(v).toFixed(1); }).join(' ');
        svg += "<polyline points='" + pts + "' fill='none' stroke='" + x.color + "' stroke-width='" + x.width + "' stroke-linejoin='round' stroke-linecap='round'/>";
      });
      svg += "<rect id='perfhover' x='" + CH.pl + "' y='" + CH.pt + "' width='" + iw + "' height='" + ih + "' fill='transparent'/></svg>";
      document.getElementById('perfchart').innerHTML = svg;
      function fmtDol(g) { return (g >= 0 ? '+' : '-') + '$' + Math.abs(g).toLocaleString('en-US', {maximumFractionDigits: 0}); }
      var lg = series.map(function(x, xi) {
        var v = x.vals[x.vals.length - 1];
        var extra = '';
        if (xi === 0 && pd.profit) {
          var g = pd.profit[pd.profit.length - 1] - pd.profit[s];
          extra = " · <span dir='ltr' class='" + (g >= 0 ? 'pos' : 'neg') + "'>רווח נטו " + fmtDol(g) + "</span>";
        }
        return "<span class='lg-item'><span class='sw' style='background:" + x.color + "'></span>" + x.name + " <b dir='ltr' class='" + (v >= 0 ? 'pos' : 'neg') + "'>" + (v >= 0 ? '+' : '') + v.toFixed(1) + "%</b>" + extra + "</span>";
      }).join('');
      document.getElementById('perflegend').innerHTML = lg;
      var hov = document.getElementById('perfhover'), tip = document.getElementById('perftip');
      var wrap = document.querySelector('.chart-wrap');
      hov.addEventListener('mousemove', function(e) {
        var rect = hov.getBoundingClientRect(), wr = wrap.getBoundingClientRect();
        var i = Math.max(0, Math.min(n - 1, Math.round((e.clientX - rect.left) / rect.width * (n - 1))));
        var ds = pd.dates[s + i];
        var html = "<b>" + ds.slice(8, 10) + '/' + ds.slice(5, 7) + '/' + ds.slice(0, 4) + "</b>";
        series.forEach(function(x, xi) {
          var v = x.vals[i];
          var extra = '';
          if (xi === 0 && pd.profit) {
            var g = pd.profit[s + i] - pd.profit[s];
            extra = " · רווח נטו <span dir='ltr' class='" + (g >= 0 ? 'pos' : 'neg') + "'>" + fmtDol(g) + "</span>";
          }
          html += "<div><span class='sw' style='background:" + x.color + "'></span>" + x.name + " <b dir='ltr'>" + (v >= 0 ? '+' : '') + v.toFixed(2) + "%</b>" + extra + "</div>";
        });
        tip.innerHTML = html; tip.hidden = false;
        tip.style.left = Math.max(0, Math.min(e.clientX - wr.left + 14, wr.width - 280)) + 'px';
        tip.style.top = Math.max(0, e.clientY - wr.top - 10) + 'px';
      });
      hov.addEventListener('mouseleave', function() { tip.hidden = true; });
    }
    document.querySelectorAll('.rbtn').forEach(function(b) {
      b.addEventListener('click', function() {
        curRange = b.getAttribute('data-range');
        document.querySelectorAll('.rbtn').forEach(function(x) { x.classList.toggle('on', x === b); });
        draw();
      });
    });
    document.querySelectorAll('.chip').forEach(function(b) {
      b.addEventListener('click', function() {
        var s = b.getAttribute('data-idx');
        onIdx[s] = !onIdx[s];
        b.classList.toggle('on', !!onIdx[s]);
        draw();
      });
    });
    draw();
  }
})();
</script>"""

LOGO_SVG = ("<svg width='26' height='26' viewBox='0 0 26 26' aria-hidden='true'>"
            "<rect x='1' y='1' width='24' height='24' rx='7' fill='#14213a' stroke='#2c3a55'/>"
            "<polyline points='5,17 10,11 14,14 21,6' fill='none' stroke='#4da3ff' stroke-width='2.4' stroke-linecap='round' stroke-linejoin='round'/>"
            "<circle cx='21' cy='6' r='2.2' fill='#31c573'/></svg>")

def _tabicon(kind):
    paths = {
        "home": "<path d='M4 17 L9 10 L13 13 L20 5' fill='none' stroke='currentColor' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'/><path d='M4 21 H20' stroke='currentColor' stroke-width='2' stroke-linecap='round'/>",
        "list": "<path d='M8 6 H20 M8 12 H20 M8 18 H20' stroke='currentColor' stroke-width='2' stroke-linecap='round'/><circle cx='4.5' cy='6' r='1.4' fill='currentColor'/><circle cx='4.5' cy='12' r='1.4' fill='currentColor'/><circle cx='4.5' cy='18' r='1.4' fill='currentColor'/>",
        "chart": "<path d='M5 20 V11 M10.5 20 V6 M16 20 V13 M21 20 V8' stroke='currentColor' stroke-width='2.2' stroke-linecap='round'/>",
        "news": "<rect x='4' y='5' width='16' height='14' rx='2.5' fill='none' stroke='currentColor' stroke-width='1.8'/><path d='M7.5 9.5 H16.5 M7.5 13 H13' stroke='currentColor' stroke-width='1.8' stroke-linecap='round'/>",
        "signal": "<path d='M12 4a5.5 5.5 0 0 0-5.5 5.5v2.6L5 15.5h14l-1.5-3.4V9.5A5.5 5.5 0 0 0 12 4z' fill='none' stroke='currentColor' stroke-width='1.9' stroke-linejoin='round'/><path d='M10 18.5a2 2 0 0 0 4 0' fill='none' stroke='currentColor' stroke-width='1.9' stroke-linecap='round'/>",
        "house": "<path d='M4 11 L12 4 L20 11' fill='none' stroke='currentColor' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'/><path d='M6.5 9.5 V20 H17.5 V9.5' fill='none' stroke='currentColor' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'/>",
    }
    return "<svg width='21' height='21' viewBox='0 0 24 24' aria-hidden='true'>" + paths[kind] + "</svg>"

TABICONS = {"/": "home", "/positions": "list", "/signals": "signal", "/garp": "chart", "/daily": "news", "/house": "house"}
NAV = [("/", "מצב התיק"), ("/positions", "פירוט פוזיציות"), ("/signals", "אותות"), ("/garp", "GARP ושיטה"), ("/daily", "סיכום יומי"), ("/house", "רכישת בית")]

def layout(title, nav, body, asof=""):
    tabs = "".join("<a href='%s' class='%s'>%s<span>%s</span></a>" % (h, "on" if h == nav else "", _tabicon(TABICONS[h]), t) for h, t in NAV)
    return ("<!doctype html><html lang='he' dir='rtl'><head><meta charset='utf-8'>"
            "<meta name='viewport' content='width=device-width,initial-scale=1'><meta name='theme-color' content='#07090d'>"
            "<meta name='color-scheme' content='dark'><title>" + esc(title) + " · תיק ההשקעות</title>" + CSS + "</head><body>"
            "<header><div class='hwrap'><span class='brand'>" + LOGO_SVG + "תיק ההשקעות</span><nav class='mainnav'>"
            + "".join("<a href='%s' class='%s'>%s</a>" % (h, "on" if h == nav else "", t) for h, t in NAV)
            + "</nav><span class='hside'><span class='mkt' id='mkt'><span class='dot'></span>בורסת ארה״ב</span>"
            "<span class='clock' id='clock'>--:--:--</span></span></div>"
            + "</header><main>"
            + ("<div class='asofline'>" + esc(asof) + "</div>" if asof else "")
            + body + "</main><nav class='tabbar'>" + tabs + "</nav>" + JS + "</body></html>")

# ---------- svg chart helpers ----------
def fmtk(v):
    if v is None: return "—"
    a = abs(v)
    if a >= 1e6: return ("-$" if v < 0 else "$") + ("%.2fM" % (a / 1e6))
    if a >= 1e4: return ("-$" if v < 0 else "$") + ("%.0fK" % (a / 1e3))
    return fmt(v, 0)

def _spark_svg(closes, w=96, h=30):
    pts = [c for c in closes if c is not None]
    if len(pts) < 2: return ""
    mn, mx = min(pts), max(pts); rg = (mx - mn) or 1.0
    step = w / (len(pts) - 1)
    xy = [(i * step, h - 2.5 - ((c - mn) / rg) * (h - 5)) for i, c in enumerate(pts)]
    coords = " ".join("%.1f,%.1f" % p for p in xy)
    col = "var(--up)" if pts[-1] >= pts[0] else "var(--down)"
    area = "M%.1f,%.1f L%s L%.1f,%.1f Z" % (xy[0][0], h, " L".join("%.1f,%.1f" % p for p in xy), xy[-1][0], h)
    return ("<svg class='spark' width='%d' height='%d' viewBox='0 0 %d %d' preserveAspectRatio='none' aria-hidden='true'>"
            "<path d='%s' fill='%s' opacity='0.14'/><polyline points='%s' fill='none' stroke='%s' stroke-width='1.6' stroke-linejoin='round'/></svg>"
            % (w, h, w, h, area, col, coords, col))

def spark_from_hist(q, days=30, w=96, h=30):
    if not q or not q.get("hist"): return ""
    closes = [c for d, c in q["hist"] if d != "None"]
    return _spark_svg(closes[-days:], w, h)

def nav_area_svg(series, w=760, h=205):
    if not series or len(series) < 2: return ""
    step = max(1, len(series) // 140)
    pts = series[::step]
    if pts[-1] != series[-1]: pts.append(series[-1])
    vals = [v for _, v in pts]; mn, mx = min(vals), max(vals)
    pad = (mx - mn) * 0.09 or 1.0; lo, hi = mn - pad, mx + pad
    top, bot = 12, h - 26
    X = lambda i: 6 + i * (w - 12) / (len(pts) - 1)
    Y = lambda v: top + (hi - v) / (hi - lo) * (bot - top)
    line = " ".join("%.1f,%.1f" % (X(i), Y(v)) for i, (_, v) in enumerate(pts))
    area = "M%.1f,%.1f L%s L%.1f,%.1f Z" % (X(0), bot, " L".join("%.1f,%.1f" % (X(i), Y(v)) for i, (_, v) in enumerate(pts)), X(len(pts) - 1), bot)
    grid = ""
    for gv in (mx, (mx + mn) / 2, mn):
        grid += "<line x1='6' x2='%d' y1='%.1f' y2='%.1f' stroke='#1c2536' stroke-width='1'/><text class='axislbl' x='%d' y='%.1f' text-anchor='end'>%s</text>" % (w - 6, Y(gv), Y(gv), w - 9, Y(gv) - 3, fmtk(gv))
    data = json.dumps([[dstr(d), fmt(v, 0), round(Y(v), 1)] for d, v in pts])
    return ("<div class='chartwrap'><svg data-pts='%s' viewBox='0 0 %d %d' style='direction:ltr' role='img' aria-label='גרף שווי נקי'>"
            "<defs><linearGradient id='navg' x1='0' y1='0' x2='0' y2='1'>"
            "<stop offset='0' stop-color='#4da3ff' stop-opacity='0.34'/><stop offset='1' stop-color='#4da3ff' stop-opacity='0.02'/></linearGradient></defs>"
            "%s<path d='%s' fill='url(#navg)'/><polyline points='%s' fill='none' stroke='#4da3ff' stroke-width='2.2' stroke-linejoin='round'/>"
            "<line class='ch-line' y1='%d' y2='%d' stroke='#7cc4ff' stroke-width='1' stroke-dasharray='3 3' style='opacity:0'/>"
            "<circle class='ch-dot' r='4' fill='#7cc4ff' stroke='#0a0e16' stroke-width='2' style='opacity:0'/>"
            "<text class='axislbl' x='8' y='%d'>%s</text><text class='axislbl' x='%d' y='%d' text-anchor='end'>%s</text></svg>"
            "<div class='chtip'></div></div>"
            % (esc(data), w, h, grid, area, line, top, bot, bot + 17, dstr(pts[0][0]), w - 8, bot + 17, dstr(pts[-1][0])))

def donut_svg(parts, size=148, sw=21):
    # parts: [(value, color)] — positive values only
    tot = sum(v for v, _ in parts) or 1.0
    r = (size - sw) / 2.0; cx = size / 2.0
    segs = ""; off = 0.0
    for v, col in parts:
        frac = (v / tot) * 100 if v > 0 else 0.0
        if frac > 0:
            segs += ("<circle cx='%.1f' cy='%.1f' r='%.1f' fill='none' stroke='%s' stroke-width='%d' "
                     "pathLength='100' stroke-dasharray='%.2f %.2f' stroke-dashoffset='%.2f'/>"
                     % (cx, cx, r, col, sw, max(frac - 1.2, 0.4), 100 - max(frac - 1.2, 0.4), -off))
        off += frac
    return "<svg width='%d' height='%d' viewBox='0 0 %d %d' aria-hidden='true'>%s</svg>" % (size, size, size, size, segs)

def gauge_html(lev):
    if lev is None: return ""
    fillp = max(0.0, min(lev / 2.0 * 100, 100))
    return ("<div class='gauge'><div class='gtrack'><div class='gfill' style='width:%.1f%%'></div>"
            "<div class='gtick' style='inset-inline-start:50%%'></div></div>"
            "<div class='glbls'><span>0×</span><span>1.0× — ללא מינוף</span><span>2.0×</span></div></div>") % fillp

def fx_exp_day(o):
    return {"META": 17, "MSFT": 17, "NFLX": 17}.get(o["underlying"], "")

def opt_cards_html(opts_data, uquotes=None):
    uquotes = uquotes or {}
    cards = ""
    today_d = date.today()
    for o, price, asof, live, fx in opts_data:
        val = price * o["contracts"] * o.get("multiplier", 100) if price else None
        exp_day = fx_exp_day(o)
        exp_txt = "%s %s %s" % (exp_day, MONTHS[o["expiryMonth"]], o["expiryYear"])
        dte = None
        try:
            if exp_day: dte = (date(int(o["expiryYear"]), int(o["expiryMonth"]), int(exp_day)) - today_d).days
        except Exception: dte = None
        un = fx.get("unreal") if fx else None
        src_txt = "" if live is True else (" · סימון IB" if live == "flex" else " · מחיר שמור")
        chips = ("<span class='ochip'>סטרייק <b>%s</b></span><span class='ochip'>פקיעה <b>%s</b></span>"
                 % (fmt(o["strike"], 0), esc(exp_txt)))
        if dte is not None: chips += "<span class='ochip'>נותרו <b>%d ימים</b></span>" % dte
        chips += "<span class='ochip'>חוזים <b>%d</b></span>" % o["contracts"]
        # moneyness: underlying live price vs strike
        money = ""
        uq = uquotes.get(o["underlying"])
        if uq and o.get("strike"):
            up = uq["price"]; st = o["strike"]
            lo = min(up, st) * 0.82; hi = max(up, st) * 1.12
            rng = (hi - lo) or 1.0
            sp = (st - lo) / rng * 100; pp = (up - lo) / rng * 100
            diff = (up / st - 1) * 100
            state = "מעל הסטרייק" if diff >= 0 else "מתחת לסטרייק"
            money = ("<div class='money'><div class='mtrack'><div class='mstrike' style='left:%.1f%%'></div>"
                     "<div class='mprice' style='left:%.1f%%'></div></div>"
                     "<div class='mlbls'><span>סטרייק %s</span><span>מחיר הבסיס %s · %s <b class='%s'>%s</b></span></div></div>"
                     % (sp, pp, fmt(st, 0), fmt(up), state, cls(diff), pct(diff)))
        cards += ("<div class='card optcard'><div class='ohead'><span class='osym'>%s</span>"
                  "<span class='otype %s'>%s LEAPS</span>"
                  "<span style='margin-inline-start:auto;text-align:left'><span class='muted small'>שווי</span><br><b class='num' style='font-size:17px'>%s</b></span></div>"
                  "<div class='ochips'>%s</div>%s"
                  "<div class='orow'><span class='muted small'>מחיר אופציה (%s%s)</span><span class='ov' style='font-size:16px'>%s</span></div>"
                  "<div class='orow' style='margin-top:6px;border-top:none;padding-top:0'><span class='muted small'>לא ממומש (IB)</span><span class='ov %s' style='font-size:16px'>%s</span></div></div>"
                  % (esc(o["underlying"]), "" if o["optionType"] == "call" else "put",
                     "Call" if o["optionType"] == "call" else "Put", fmt(val, 0),
                     chips, money,
                     esc(asof), src_txt, fmt(price),
                     cls(un), fmt(un, 0) if un is not None else "—"))
    return "<div class='optgrid'>" + cards + "</div>"

def levels_track_html(it, p):
    fair, entry, exitp = it.get("fairPrice"), it.get("entryPrice"), it.get("exitPrice")
    bot = band_bottom(it)
    is_garp = it.get("method") in ("garp", "garp_blocked")
    vals = [v for v in (fair, entry, exitp, bot, p) if v]
    if not vals or not p: return ""
    lo, hi = min(vals), max(vals); rng = (hi - lo) or 1.0
    lo -= rng * 0.14; hi += rng * 0.14; rng = hi - lo
    pos = lambda v: (v - lo) / rng * 100
    out = "<div class='lvl'><div class='basetrack'></div>"
    if is_garp and entry and bot:
        out += "<div class='bandseg' style='left:%.1f%%;width:%.1f%%'></div>" % (pos(bot), pos(entry) - pos(bot))
    # level labels below the track, two rows, greedy de-collision (min 9% of track apart per row)
    labels = []  # (pos%, text, cls, tick?)
    if fair: labels.append((pos(fair), "הוגן " + fmt(fair, 0), "fair", True))
    if exitp: labels.append((pos(exitp), "יציאה " + fmt(exitp, 0), "exit", True))
    if entry: labels.append((pos(entry), entry_label(it) + " " + fmt(entry, 0), "band", True))
    if is_garp and entry and bot:
        labels.append(((pos(bot) + pos(entry)) / 2, "רצועת קנייה %s – %s" % (fmt(bot, 0), fmt(entry, 0)), "bandlbl", False))
    labels.sort(key=lambda t: t[0])
    rows = [[], []]
    for pp, txt, cl, tick in labels:
        r = 0 if all(abs(pp - q) >= 9 for q in rows[0]) else 1
        rows[r].append(pp)
        top = 24 if r == 0 else 42
        if tick:
            out += "<div class='lmk %s' style='left:%.1f%%'><span style='top:%dpx'>%s</span></div>" % (cl, pp, top, esc(txt))
        else:
            out += "<div class='bandlbl' style='left:%.1f%%;top:%dpx'>%s</div>" % (pp, 68 + (18 if r else 0), esc(txt))
    out += "<div class='pmark' style='left:%.1f%%'><span>מחיר %s</span></div>" % (pos(p), fmt(p))
    out += "</div>"
    return out

def price_chart_svg(q, it, w=760, h=300):
    hist = [(d, c) for d, c in (q.get("hist") or []) if d != "None"]
    if len(hist) < 30: return "", ""
    closes = [c for _, c in hist]; dates = [d for d, _ in hist]
    n = min(252, len(closes)); i0 = len(closes) - n
    win = closes[i0:]; wdates = dates[i0:]
    def sma(nn):
        out = []
        for i in range(len(closes)):
            out.append(sum(closes[i - nn + 1:i + 1]) / nn if i >= nn - 1 else None)
        return out[i0:]
    s150, s200 = sma(150), sma(200)
    fair, entry, exitp = it.get("fairPrice"), it.get("entryPrice"), it.get("exitPrice")
    bot = band_bottom(it)
    cand = [v for v in win if v]
    for s in (s150, s200): cand += [v for v in s if v]
    mn, mx = min(cand), max(cand); rng = (mx - mn) or 1.0
    lvls = []
    for v, lbl, col in [(fair, "הוגן", "#7cc4ff"), (entry, entry_label(it), "#31c573"), (bot, "תחתית רצועה", "#31c573"), (exitp, "יציאה", "#f45d5d")]:
        if v and mn - rng * 0.18 <= v <= mx + rng * 0.18: lvls.append((v, lbl, col))
    for v, _, _ in lvls: mn = min(mn, v); mx = max(mx, v)
    pad = (mx - mn) * 0.07 or 1.0; lo, hi = mn - pad, mx + pad
    top, boty = 10, h - 24
    X = lambda i: 6 + i * (w - 12) / (len(win) - 1)
    Y = lambda v: top + (hi - v) / (hi - lo) * (boty - top)
    def pline(vals, col, wd, dash=""):
        pts = " ".join("%.1f,%.1f" % (X(i), Y(v)) for i, v in enumerate(vals) if v is not None)
        return "<polyline points='%s' fill='none' stroke='%s' stroke-width='%s' stroke-linejoin='round' %s/>" % (pts, col, wd, dash)
    area = "M%.1f,%.1f L%s L%.1f,%.1f Z" % (X(0), boty, " L".join("%.1f,%.1f" % (X(i), Y(v)) for i, v in enumerate(win)), X(len(win) - 1), boty)
    grid = ""
    for gv in (mx, (mx + mn) / 2, mn):
        grid += "<line x1='6' x2='%d' y1='%.1f' y2='%.1f' stroke='#1c2536'/><text class='axislbl' x='%d' y='%.1f' text-anchor='end'>%s</text>" % (w - 6, Y(gv), Y(gv), w - 9, Y(gv) - 3, fmt(gv, 0))
    lvl_svg = ""
    for v, lbl, col in lvls:
        lvl_svg += ("<line x1='6' x2='%d' y1='%.1f' y2='%.1f' stroke='%s' stroke-width='1.2' stroke-dasharray='6 4' opacity='0.75'/>"
                    "<text x='10' y='%.1f' font-size='11' font-weight='700' fill='%s'>%s %s</text>"
                    % (w - 6, Y(v), Y(v), col, Y(v), col, esc(lbl), fmt(v, 0)))
    def dfmt(d):
        try: return datetime.strptime(d, "%Y-%m-%d").strftime("%d/%m/%y")
        except Exception: return d or ""
    svg = ("<svg viewBox='0 0 %d %d' style='direction:ltr' role='img' aria-label='גרף מחיר'>"
           "<defs><linearGradient id='pg' x1='0' y1='0' x2='0' y2='1'>"
           "<stop offset='0' stop-color='#4da3ff' stop-opacity='0.26'/><stop offset='1' stop-color='#4da3ff' stop-opacity='0.02'/></linearGradient></defs>"
           "%s<path d='%s' fill='url(#pg)'/>%s%s%s%s"
           "<text class='axislbl' x='8' y='%d'>%s</text><text class='axislbl' x='%d' y='%d' text-anchor='end'>%s</text></svg>"
           % (w, h, grid, area, lvl_svg, pline(s200, "#c792ea", 1.4), pline(s150, "#f2b84b", 1.4), pline(win, "#4da3ff", 2.1),
              boty + 17, dfmt(wdates[0]), w - 8, boty + 17, dfmt(wdates[-1])))
    legend = ("<div class='legendrow'><span class='li'><span class='sw' style='background:#4da3ff'></span>מחיר</span>"
              "<span class='li'><span class='sw' style='background:#f2b84b'></span>ממוצע 150</span>"
              "<span class='li'><span class='sw' style='background:#c792ea'></span>ממוצע 200</span>"
              + "".join("<span class='li'><span class='swd' style='border-color:%s'></span>%s %s</span>" % (c, esc(l), fmt(v)) for v, l, c in lvls) + "</div>")
    return svg, legend

def _sig_icon(kind):
    p = {"good": "<path d='M4 14 L9 8 L13 11 L20 4'/><path d='M14.5 4 H20 V9.5'/>",
         "bad": "<path d='M4 10 L9 16 L13 13 L20 20'/><path d='M14.5 20 H20 V14.5'/>",
         "warn": "<path d='M12 4 L21.5 20 H2.5 Z'/><path d='M12 10 V14'/><circle cx='12' cy='17' r='0.6' fill='currentColor'/>",
         "info": "<rect x='3.5' y='5' width='17' height='16' rx='2.5'/><path d='M3.5 10 H20.5 M8 3 V6.5 M16 3 V6.5'/>"}.get(kind, "")
    return ("<span class='sigic %s'><svg width='15' height='15' viewBox='0 0 24 24' fill='none' stroke='currentColor' "
            "stroke-width='2.2' stroke-linecap='round' stroke-linejoin='round'>%s</svg></span>" % (kind, p))

def _quotes2(syms):
    with ThreadPoolExecutor(max_workers=10) as ex:
        return dict(zip(syms, ex.map(lambda s: get_quote(s, "2y"), syms)))

# ---------- page 1 ----------
def page_home():
    fd = flex_data()
    syms = [i["symbol"] for i in ITEMS]
    qs = get_quotes(syms)
    qs2 = _quotes2([i["symbol"] for i in POS] + STRIP_SYMS)
    opts = load_options_data(fd)
    flex_qty = {}; flex_unreal = {}; flex_pos = {}
    if fd and fd.get("daily"):
        for p in fd["daily"]["positions"]:
            if p["cat"] == "STK":
                flex_qty[norm(p["symbol"])] = p["qty"]
                flex_pos[norm(p["symbol"])] = p
                if p.get("unreal") is not None: flex_unreal[norm(p["symbol"])] = p["unreal"]
    def qty(it):
        return flex_qty.get(norm(it["symbol"]), it.get("shares"))
    def val(it):
        q = qs.get(it["symbol"]); n = qty(it)
        return q["price"] * n if q and n else None
    stock_val = sum(val(i) for i in POS if val(i))
    opt_val = sum((p * o["contracts"] * o.get("multiplier", 100)) for o, p, a, l, fx in opts if p)
    total_live = stock_val + opt_val
    day_usd = 0.0
    for i in POS:
        q = qs.get(i["symbol"]); v = val(i)
        if q and v: day_usd += v - v / (1 + q["dayPct"] / 100.0) if q["dayPct"] != -100 else 0
    day_pct_live = (day_usd / (total_live - day_usd) * 100) if total_live and total_live != day_usd else None
    daily = fd["daily"] if fd else None
    # profit since inception (YTD file + daily files) — computed once here: the hero
    # shows it under the daily profit, and the allocation section reuses it.
    ytd_srs = sorted(fd["ytd"]["series"].items()) if fd and fd["ytd"].get("series") else None
    if ytd_srs:
        ytd_v0 = ytd_srs[0][1]; ytd_v1 = ytd_srs[-1][1]
        ytd_nf = sum(fd["ytd"]["flows"].values())
        ytd_prof = ytd_v1 - ytd_v0 - ytd_nf
        ytd_gross = fd["ytd"].get("gross_mtm")
    else:
        ytd_prof = None; ytd_gross = None
    cs = chart_series()
    ytd_ppct = (cs["pf"][-1] / cs["pf"][0] - 1) * 100 if cs and cs.get("pf") else None
    # (a) hero + NAV chart
    hero = "<div class='hero'><div class='t'>מה שווי התיק?</div>"
    if daily:
        hero += "<div class='v num'>%s</div><div class='sub'>שווי נקי ב־Interactive Brokers · דוח Flex %s</div>" % (
            fmt(daily["total"], 0), dstr(daily["date"]))
    else:
        hero += "<div class='v num'>%s</div><div class='sub'>שווי מחושב חי (אין נתוני Flex זמינים)</div>" % fmt(total_live, 0)
    hero += ("<div class='dayline'>היום (מחושב ממחירים חיים): <span class='pill %s'>%s · %s</span></div>"
             % (cls(day_usd), fmt(day_usd, 0), pct(day_pct_live)))
    if ytd_gross is not None:
        hero += ("<div class='dayline'>רווח מפתיחת התיק: <span class='pill %s'>%s · %s TWR</span> <span class='muted'>(נטו %s)</span></div>"
                 % (cls(ytd_gross), fmt(ytd_gross, 0), pct(ytd_ppct) if ytd_ppct is not None else "—", fmt(ytd_prof, 0) if ytd_prof is not None else "—"))
    # one chart on the home page, not two (Oren, 8/11/2026): the hero NAV area chart is gone;
    # the interactive returns chart (portfolio TWR vs indices) is the single chart.
    hero += "</div>"
    # (b) performance — portfolio vs indices, one interactive chart (IB-style)
    # cs was computed above (the hero needs its TWR too).
    perf_html = "<h2 class='sec'>איך התיק מול המדדים?</h2>"
    if cs:
        ranges = [("week", "שבוע"), ("month", "חודש"), ("3m", "3 חודשים"), ("ytd", "מתחילת השנה")]
        rbtns = "".join("<button class='rbtn%s' data-range='%s'>%s</button>" % (" on" if r == "ytd" else "", r, lbl) for r, lbl in ranges)
        chips = "".join("<button class='chip%s' data-idx='%s' style='--c:%s'>%s</button>" % (" on" if s in ("^GSPC", "^NDX") else "", s, c, n) for s, n, c in CHART_INDEX)
        perf_html += ("<div class='card'><div class='chart-ctrl'><div class='ranges'>%s</div><div class='chips'>%s</div></div>"
                      "<div class='chart-wrap'><div id='perfchart'></div><div class='chart-tip' id='perftip' hidden></div></div>"
                      "<div class='chart-legend' id='perflegend'></div></div>"
                      "<script>var PERF_DATA = %s;</script>") % (rbtns, chips, json.dumps(cs))
        cin = fd["ytd"]["changeinnav"] if fd else {}
        twr = fnum(cin.get("twr"))
        foot = "TWR יומי משורשר מנתוני IB Flex, בניכוי תזרימים; כל סדרה מנורמלת ל־0% בתחילת התקופה."
        if twr is not None: foot += " לפי IB, TWR רשמי YTD: %s (עד 15/10)." % pct(twr)
        perf_html += "<p class='foot'>" + foot + "</p>"
    else:
        perf_html += "<p class='muted'>אין נתוני NAV זמינים.</p>"
    # (c) allocation donut + unrealized panel
    chev = "<svg class='chev' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='currentColor' stroke-width='2.4' stroke-linecap='round' stroke-linejoin='round'><path d='M5 9 L12 16 L19 9'/></svg>"
    alloc_html = "<h2 class='sec'>הקצאה ורווח</h2><div class='grid g-2'>"
    if total_live:
        sp = stock_val / total_live * 100; op = opt_val / total_live * 100
        donut = donut_svg([(stock_val, "#4da3ff"), (opt_val, "#c792ea")])
        legend = ("<div class='lrow'><span class='sw' style='background:#4da3ff'></span>מניות<span class='lp'>%.1f%%</span><span class='lv'>%s</span></div>"
                  "<div class='lrow'><span class='sw' style='background:#c792ea'></span>אופציות LEAPS<span class='lp'>%.1f%%</span><span class='lv'>%s</span></div>"
                  % (sp, fmt(stock_val, 0), op, fmt(opt_val, 0)))
        if daily:
            legend += ("<div class='lrow'><span class='sw' style='background:#f45d5d'></span>מזומן / מרג'ין<span class='lp'></span><span class='lv'>%s</span></div>"
                       % fmt(daily["cash"], 0))
        alloc_html += ("<div class='card'><div class='t'>איך מחולק התיק?</div><div class='donut-flex' style='margin-top:10px'>"
                       "<div class='donutwrap'>%s<div class='donut-c'><div class='dv'>%s</div><div class='dt'>מניות + אופציות</div></div></div>"
                       "<div class='legend'>%s</div></div></div>" % (donut, fmt(total_live, 0), legend))
    if daily:
        tot_unreal = sum((p["unreal"] or 0) for p in daily["positions"])
        stk_unreal = sum((p["unreal"] or 0) for p in daily["positions"] if p["cat"] == "STK")
        opt_unreal = sum((p["unreal"] or 0) for p in daily["positions"] if p["cat"] == "OPT")
        mxu = max(abs(stk_unreal), abs(opt_unreal), 1.0)
        def urow(lbl, v):
            return ("<div class='hbar-row'><span class='muted'>%s</span><span class='hbar-track'>"
                    "<span class='hbar-fill' style='display:block;width:%.0f%%;background:%s'></span></span>"
                    "<b class='%s'>%s</b></div>"
                    % (lbl, abs(v) / mxu * 100, "var(--up)" if v >= 0 else "var(--down)", cls(v), fmt(v, 0)))
        alloc_html += ("<div class='card'><div class='t'>כמה אני מורווח על הנייר?</div>"
                       "<div class='v %s'>%s</div>%s%s<div class='s'>מול עלות FIFO בדוח · IB %s</div></div>"
                       % (cls(tot_unreal), fmt(tot_unreal, 0), urow("מניות", stk_unreal), urow("אופציות", opt_unreal), dstr(daily["date"])))
    # gross profit since inception: IB-native MTM (ChangeInNAV) chained from the YTD file + daily files
    # (daily reports repeat the same statement date in several files — deduped by date in flex_data).
    # Net = NAV-based (end NAV − start NAV − net flows); the two reconcile within ~$10.
    profit_panel = ""
    prof = None  # net profit (USD) — reused by the loans-vs-value card for the after-tax figure
    if fd and fd["ytd"].get("series") and cs:
        srs = ytd_srs; v0 = ytd_v0; v1 = ytd_v1; nf = ytd_nf
        prof = ytd_prof
        ppct = ytd_ppct
        gross = ytd_gross
        # deposits vs withdrawals: totals on the card + per-date table in an expandable panel
        flow_rows = sorted(fd["ytd"].get("flow_rows") or [], key=lambda r: r["date"])
        dep_usd = sum(r["usd"] for r in flow_rows if r["usd"] > 0); wd_usd = -sum(r["usd"] for r in flow_rows if r["usd"] < 0)
        dep_ils = sum(r["ils"] for r in flow_rows if r["ils"] > 0); wd_ils = -sum(r["ils"] for r in flow_rows if r["ils"] < 0)
        flows_line = ("הופקד <span dir='ltr'>%s</span> · נמשך <span dir='ltr'>%s</span> · נטו <span dir='ltr'>%s</span>"
                      % (fmt_ils(dep_ils), fmt_ils(-wd_ils), fmt_ils(dep_ils - wd_ils))) if flow_rows else ("הפקדות נטו <span dir='ltr'>%s</span>" % fmt(nf, 0))
        if flow_rows:
            frows = "".join("<div class='drow'><span class='dl'>%s · %s</span><span class='dv' dir='ltr'><b class='%s'>%s</b> <span class='muted'>%s</span></span></div>"
                            % (dstr(r["date"]), "הפקדה" if r["ils"] > 0 else "משיכה",
                               "pos" if r["ils"] > 0 else "neg", fmt_ils(r["ils"]), fmt(r["usd"], 0)) for r in flow_rows)
            profit_panel = ("<div class='sigpanel xpanel' id='profit-detail' hidden>"
                            "<div class='pt'>פירוט תזרימים — הפקדות ומשיכות</div>%s"
                            "<div class='drow tot'><span class='dl'>סה״כ הופקד</span><span class='dv' dir='ltr'><b class='pos'>%s</b></span></div>"
                            "<div class='drow tot'><span class='dl'>סה״כ נמשך</span><span class='dv' dir='ltr'><b class='neg'>%s</b></span></div>"
                            "<div class='drow tot'><span class='dl'>נטו</span><span class='dv' dir='ltr'><b>%s</b> <span class='muted'>%s</span></span></div>"
                            "<div class='pfoot'>שווי התחלתי %s (%s) · שווי נוכחי %s (%s) · ברוטו = MTM של IB; לא ממומש = FIFO בעמדות הפתוחות</div></div>"
                            % (frows, fmt_ils(dep_ils), fmt_ils(-wd_ils), fmt_ils(dep_ils - wd_ils), fmt(dep_usd - wd_usd, 0),
                               fmt(v0, 0), dstr(srs[0][0]), fmt(v1, 0), dstr(srs[-1][0])))
        if gross is not None and daily:
            unreal_now = sum((p["unreal"] or 0) for p in daily["positions"])
            realized = gross - unreal_now
            alloc_html += ("<div class='card xcard' data-exp='profit-detail' tabindex='0' role='button' aria-expanded='false'>"
                           "<div class='t' style='display:flex;align-items:center;justify-content:space-between'><span>כמה הרווחתי מפתיחת התיק?</span>%s</div>"
                           "<div class='v %s'>%s</div>"
                           "<div class='s'>ממומש %s · לא ממומש %s</div>"
                           "<div class='s'>רווח נטו: <b class='%s'>%s</b> · %s TWR%s</div></div>"
                           % (chev, cls(gross), fmt(gross, 0), fmt(realized, 0), fmt(unreal_now, 0), cls(prof), fmt(prof, 0), pct(ppct) if ppct is not None else "—",
                              " · פירוט בלחיצה" if profit_panel else ""))
        else:
            alloc_html += ("<div class='card xcard' data-exp='profit-detail' tabindex='0' role='button' aria-expanded='false'>"
                           "<div class='t' style='display:flex;align-items:center;justify-content:space-between'><span>כמה הרווחתי מפתיחת התיק?</span>%s</div>"
                           "<div class='v %s'>%s</div><div class='s'>%s TWR מפתיחת התיק</div>"
                           "<div class='s'>%s%s</div></div>"
                           % (chev, cls(prof), fmt(prof, 0), pct(ppct) if ppct is not None else "—", flows_line,
                              " · פירוט בלחיצה" if profit_panel else ""))
        if flow_rows:
            alloc_html += ("<div class='card xcard' data-exp='profit-detail' tabindex='0' role='button' aria-expanded='false'>"
                           "<div class='t' style='display:flex;align-items:center;justify-content:space-between'><span>כמה הפקדתי וכמה משכתי?</span>%s</div>"
                           "<div class='v %s'>%s</div>"
                           "<div class='s'>הופקד %s · נמשך %s</div>"
                           "<div class='s'>הופקד %s · נמשך %s · פירוט בלחיצה</div></div>"
                           % (chev, cls(dep_ils - wd_ils), fmt_ils(dep_ils - wd_ils), fmt_ils(dep_ils), fmt_ils(-wd_ils),
                              fmt(dep_usd, 0), fmt(wd_usd, 0)))
    alloc_html += profit_panel
    alloc_html += "</div>"
    # (d) exposure / leverage
    exp_html = "<h2 class='sec'>חשיפה ומינוף</h2><div class='grid g-2'>"
    if daily:
        gross = daily["stock"] + daily["options"]
        lev = (gross / daily["total"]) if daily["total"] else None
        cash = daily["cash"]
        exp_html += "<div class='card'><div class='t'>האם אני בחוב מרג'ין?</div><div class='v'><span dir='ltr' class='%s'>%s</span></div><div class='s'>מזומן שלילי = חוב מרג'ין בברוקר · IB %s</div></div>" % (cls(cash), fmt(cash, 0), dstr(daily["date"]))
        exp_html += ("<div class='card'><div class='t'>כמה חשיפה יש לי בברוקר?</div><div class='v'>%s</div>%s"
                     "<div class='s'>מינוף בחשבון: %s מהשווי הנקי</div></div>"
                     % (fmt(gross, 0), gauge_html(lev), ("%.2f×" % lev) if lev else "—"))
        stk_pos = sorted([p for p in daily["positions"] if p["cat"] == "STK"], key=lambda p: -(p.get("value") or 0))[:3]
        if stk_pos and daily["total"]:
            crows = ""
            for p in stk_pos:
                share = (p["value"] or 0) / daily["total"] * 100
                crows += ("<div class='hbar-row' style='grid-template-columns:52px 1fr auto'><span><b>%s</b></span>"
                          "<span class='hbar-track'><span class='hbar-fill' style='display:block;width:%.0f%%;background:var(--acc)'></span></span>"
                          "<span class='muted'>%s · %s</span></div>"
                          % (esc(norm(p["symbol"])), min(share, 100), pct(share, sign=False), fmt(p["value"], 0)))
            exp_html += "<div class='card'><div class='t'>איפה מרוכז התיק?</div>%s</div>" % crows
    ils = get_quote("ILS=X")
    ils_rate = ils["price"] if ils else None
    # Norton is separate: its loans did not fund the equity portfolio, so Norton never
    # enters any total or remainder — it appears only as its own informational row (Oren, 8/11/2026).
    pf_planit_loans = PLANIT_LOANS_ILS - NORTON_LOAN_ILS        # 283,400 (יתרת Planit לאחר ניכוי Norton)
    pf_planit_monthly = PLANIT_MONTHLY_ILS - NORTON_MONTHLY_ILS  # 1,023
    total_loans = pf_planit_loans + TESLA_LOAN_BAL_ILS           # 447,958 — portfolio only
    total_monthly = pf_planit_monthly + TESLA_MONTHLY_ILS        # 2,680 — portfolio only
    chev = "<svg class='chev' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='currentColor' stroke-width='2.4' stroke-linecap='round' stroke-linejoin='round'><path d='M5 9 L12 16 L19 9'/></svg>"
    def ils_cell(v, color=False):
        return "<span dir='ltr' class='%s'>%s</span>" % ("neg" if color else "", fmt_ils(v))
    # (merged loans + loans-vs-value card is built below, inside the daily/ils_rate block)
    # loans vs portfolio value, in ILS (portfolio converted at the current USD rate).
    # One merged card (Oren, 8/11/2026): net balance after the portfolio loans + gross
    # return on his own money only. Norton appears only as its own informational row.
    snap_html = ""
    if daily and daily.get("total") and ils_rate:
        pf_ils = daily["total"] * ils_rate
        net_ils = pf_ils - total_loans
        lev_equity = net_ils
        lev_pct = (total_loans / pf_ils * 100) if pf_ils and pf_ils > 0 else None
        # מס משוער = 25% על הרווח הנקי (NAV) — הערכה, לא חישוב מס סופי.
        tax_ils = (prof * 0.25 * ils_rate) if prof is not None and ils_rate else None
        net_after_tax = (pf_ils - total_loans - tax_ils) if tax_ils is not None else None
        # תשואה ברוטו על הכסף שלי בלבד (אורן, 8/11/2026):
        # (רווח ברוטו − ריבית הלוואות התיק) / הכסף שלי שהושקע.
        # הכסף שלי = שווי התחלתי (31/12/2025) + הפקדות נטו − הלוואות התיק.
        # ריבית הלוואות משוערת = החזר חודשי Planit (יתרה) × 7 חודשים (אפריל–נובמבר 2026); טסלה 0%.
        gross_mtm = fd["ytd"].get("gross_mtm") if fd and fd.get("ytd") else None
        flow_rows_lv = sorted(fd["ytd"].get("flow_rows") or [], key=lambda r: r["date"]) if fd and fd.get("ytd") else []
        net_dep_ils = sum(r["ils"] for r in flow_rows_lv) if flow_rows_lv else None
        series_lv = (fd["ytd"].get("series") or {}) if (fd and fd.get("ytd")) else {}
        start_nav_usd = sorted(series_lv.items())[0][1] if series_lv else None
        own_money = (start_nav_usd * ils_rate + net_dep_ils - total_loans) if (start_nav_usd is not None and net_dep_ils is not None) else None
        loan_int_est = pf_planit_monthly * 7
        ret_pct = ((gross_mtm * ils_rate - loan_int_est) / own_money * 100) if (gross_mtm is not None and own_money and own_money > 0) else None
        de_ratio = (total_loans / lev_equity * 100) if lev_equity and lev_equity > 0 else None
        twr_ytd = (cs["pf"][-1] / cs["pf"][0] - 1) * 100 if cs and cs.get("pf") else None
        prof_ils = (prof * ils_rate) if prof is not None else None
        ncls = cls(net_ils)
        lv_rows = []
        lv_rows.append("<div class='drow'><span class='dl'>שווי התיק <span class='muted'>(נקי, Flex %s)</span></span><span class='dv' dir='ltr'><b>%s</b> <span class='muted'>%s</span></span></div>" % (
            dstr(daily["date"]), ils_cell(pf_ils), fmt(daily["total"], 0)))
        lv_rows.append("<div class='drow'><span class='dl'>הלוואות Planit — יתרה לאחר ניכוי Norton <span class='muted'>(%.2f%%, %s/חודש)</span></span><span class='dv'>%s</span></div>" % (
            PLANIT_RATE, ils_cell(pf_planit_monthly), ils_cell(pf_planit_loans, True)))
        lv_rows.append("<div class='drow'><span class='dl'>הלוואות טסלה <span class='muted'>(0%% + מדד, %s/חודש)</span></span><span class='dv'>%s</span></div>" % (
            ils_cell(TESLA_MONTHLY_ILS), ils_cell(TESLA_LOAN_BAL_ILS, True)))
        lv_rows.append("<div class='drow muted'><span class='dl'>Norton — בנפרד, לא בתיק, מידע בלבד <span class='muted'>(התחייבות %s, הועבר %s)</span></span><span class='dv'>%s</span></div>" % (
            fmt(NORTON_COMMIT_USD, 0), fmt_ils(NORTON_WIRED_ILS), ils_cell(NORTON_LOAN_ILS, True)))
        lv_rows.append("<div class='drow tot'><span class='dl'>סה״כ הלוואות בתיק</span><span class='dv'>%s</span></div>" % ils_cell(total_loans, True))
        lv_rows.append("<div class='drow'><span class='dl'>החזר חודשי (הלוואות התיק)</span><span class='dv'>%s</span></div>" % ils_cell(total_monthly))
        lv_rows.append("<div class='drow tot'><span class='dl'>מאזן נטו משוער (תיק − הלוואות)</span><span class='dv' dir='ltr'><b class='%s'>%s</b></span></div>" % (
            ncls, fmt_ils(net_ils)))
        lv_rows.append("<div class='drow'><span class='dl'>מס משוער <span class='muted'>(25%% על רווח נטו %s)</span></span><span class='dv' dir='ltr'><b>%s</b> <span class='muted'>%s</span></span></div>" % (
            fmt(prof, 0) if prof is not None else "—", ils_cell(tax_ils) if tax_ils is not None else "—", fmt(prof * 0.25, 0) if prof is not None else "—"))
        lv_rows.append("<div class='drow tot'><span class='dl'>נטו לאחר מס (סגירה מלאה)</span><span class='dv' dir='ltr'><b class='%s'>%s</b></span></div>" % (
            cls(net_after_tax) if net_after_tax is not None else "", fmt_ils(net_after_tax) if net_after_tax is not None else "—"))
        lv_rows.append("<div class='drow'><span class='dl'>יחס הלוואות / שווי התיק</span><span class='dv' dir='ltr'><b class='%s'>%s</b></span></div>" % (
            ncls, ("%.1f%%" % lev_pct) if lev_pct is not None else "—"))
        lv_rows.append("<div class='drow'><span class='dl'>יחס חוב / הון עצמי</span><span class='dv' dir='ltr'><b>%s</b></span></div>" % (
            ("%.1f%% (%.2f×)" % (de_ratio, de_ratio / 100)) if de_ratio is not None else "—"))
        lv_rows.append("<div class='drow tot'><span class='dl'>תשואה ברוטו על הכסף שלי</span><span class='dv' dir='ltr'><b>%s</b></span></div>" % (
            ("%.1f%%" % ret_pct) if ret_pct is not None else "—"))
        lv_rows.append("<div class='drow sub'><span class='dl'>רווח ברוטו (MTM, IB)</span><span class='dv' dir='ltr'><b>%s</b> <span class='muted'>%s</span></span></div>" % (
            fmt_ils(gross_mtm * ils_rate) if gross_mtm is not None else "—", fmt(gross_mtm, 0) if gross_mtm is not None else "—"))
        lv_rows.append("<div class='drow sub'><span class='dl'>ריבית הלוואות משוערת (Planit, ~7 חודשים)</span><span class='dv'>%s</span></div>" % ils_cell(loan_int_est))
        lv_rows.append("<div class='drow sub'><span class='dl'>הכסף שלי שהושקע <span class='muted'>(שווי התחלתי %s + הפקדות נטו %s − הלוואות %s)</span></span><span class='dv'>%s</span></div>" % (
            fmt_ils(start_nav_usd * ils_rate) if start_nav_usd is not None else "—", fmt_ils(net_dep_ils) if net_dep_ils is not None else "—", fmt_ils(total_loans),
            fmt_ils(own_money) if own_money is not None else "—"))
        lv_tbl = "<div class='pt'>פירוט הלוואות ושווי</div>" + "".join(lv_rows)
        exp_html += ("<div class='card xcard' data-exp='loans-lv-detail' tabindex='0' role='button' aria-expanded='false'>"
                     "<div class='t' style='display:flex;align-items:center;justify-content:space-between'><span>הלוואות מול שווי התיק</span>%s</div>"
                     "<div class='v %s'>%s</div>"
                     "<div class='s'>יתרת נטו משוערת · שווי התיק <span dir='ltr'>%s</span> · Flex %s · שער %s</div>"
                     "<div class='s'>הלוואות בתיק: <b>%s</b> (%s/חודש) · מינוף <b>%s</b> · פירוט בלחיצה</div></div>") % (
            chev, ncls, fmt_ils(net_ils),
            fmt(daily["total"], 0), dstr(daily["date"]), "%.3f" % ils_rate,
            fmt_ils(total_loans), fmt_ils(total_monthly),
            ("%.1f%%" % lev_pct) if lev_pct is not None else "—")
        exp_html += "<div class='sigpanel xpanel' id='loans-lv-detail' hidden>%s</div>" % lv_tbl
        # תמונת מצב — שש השאלות בראש הדף (אורן, 8/11/2026): מובייל תחילה, תשובות במספרים גדולים.
        snap_cards = []
        snap_cards.append("<div class='card snap'><div class='q'>כמה תשואה עשיתי?</div><div class='v %s'>%s</div><div class='s'>מתחילת השנה (TWR) · רווח נטו %s (≈%s)</div></div>" % (
            cls(twr_ytd) if twr_ytd is not None else "", pct(twr_ytd) if twr_ytd is not None else "—",
            fmt(prof, 0) if prof is not None else "—", fmt_ils(prof_ils) if prof_ils is not None else "—"))
        snap_cards.append("<div class='card snap'><div class='q'>מה סכום ההלוואות שהוזרקו לתיק?</div><div class='v neg'>%s</div><div class='s'>Planit %s + טסלה %s · %s לחודש</div></div>" % (
            fmt_ils(total_loans), fmt_ils(pf_planit_loans), fmt_ils(TESLA_LOAN_BAL_ILS), fmt_ils(total_monthly)))
        snap_cards.append("<div class='card snap'><div class='q'>מה יחס הלוואה / הון עצמי?</div><div class='v'>%s</div><div class='s'>(%s) · מינוף %s משווי התיק · הון עצמי %s</div></div>" % (
            ("%.1f%%" % de_ratio) if de_ratio is not None else "—",
            ("%.2f×" % (de_ratio / 100)) if de_ratio is not None else "—",
            ("%.1f%%" % lev_pct) if lev_pct is not None else "—", fmt_ils(lev_equity)))
        snap_cards.append("<div class='card snap'><div class='q'>כמה ריבית שילמתי על ההלוואות?</div><div class='v'>≈%s</div><div class='s'>על הלוואות התיק (משוער, אפריל–נובמבר 2026) · טסלה 0%%</div></div>" % fmt_ils(loan_int_est))
        snap_cards.append("<div class='card snap'><div class='q'>כמה תשואה עשיתי על ההון העצמי?</div><div class='v %s'>%s</div><div class='s'>(רווח ברוטו %s − ריבית %s) / הכסף שלי %s</div></div>" % (
            cls(ret_pct) if ret_pct is not None else "", ("%.1f%%" % ret_pct) if ret_pct is not None else "—",
            fmt_ils(gross_mtm * ils_rate) if gross_mtm is not None else "—", fmt_ils(loan_int_est),
            fmt_ils(own_money) if own_money is not None else "—"))
        snap_cards.append("<div class='card snap'><div class='q'>כמה ישאר לי אם אסגור הכול ואחזיר את ההלוואות?</div><div class='v %s'>%s</div><div class='s'>לפני מס · אחרי מס (25%%): %s</div></div>" % (
            ncls, fmt_ils(net_ils), fmt_ils(net_after_tax) if net_after_tax is not None else "—"))
        snap_html = "<h2 class='sec'>תמונת מצב</h2><div class='grid g-snap'>" + "".join(snap_cards) + "</div>"
    exp_html += "</div>"
    # indices strip — only VIX, SOXX, NDX, GSPC (Oren, 8/11/2026)
    strip = "<h2 class='sec'>מדדים</h2><div class='grid g-idx'>"
    by_sym = {i["symbol"]: i for i in ITEMS}
    for sym in STRIP_SYMS:
        i = by_sym.get(sym)
        if not i: continue
        q = qs.get(i["symbol"])
        strip += ("<div class='card tile'><div class='trow'><span class='tsym'>%s</span><span class='pill %s'>%s</span></div>"
                  "<div class='muted small'>%s</div><div class='tv'>%s</div><div style='margin-top:6px'>%s</div></div>"
                  % (esc(i["symbol"].lstrip("^")), cls(q["dayPct"]) if q else "", (pct(q["dayPct"]) + " היום") if q else "אין נתון",
                     esc(i["name"]), fmt(q["price"]) if q else "—", spark_from_hist(qs2.get(i["symbol"]), 30, 120, 30)))
    strip += "</div>"
    # mini positions — expandable inline (accordion panel per position, screenshots only)
    rows = ""; mrows = []; mcards = []
    for n, i in enumerate(POS):
        q = qs.get(i["symbol"]); v = val(i)
        se = since_entry_pct(i["symbol"], q["price"] if q else None, flex_pos)
        mrows.append((v, ("<tr class='posrow' data-exp='posp-%d' tabindex='0' role='button' aria-expanded='false'><td><a class='sym' href='/garp?s=%s'><b>%s</b></a></td><td>%s</td><td>%s</td>"
                 "<td><span class='pill %s'>%s</span></td><td><span class='pill %s'>%s</span></td><td>%s</td><td><b>%s</b></td><td>%s</td>"
                 "<td><svg class='chev' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='currentColor' stroke-width='2.4' stroke-linecap='round' stroke-linejoin='round'><path d='M5 9 L12 16 L19 9'/></svg></td></tr>"
                 "<tr class='panelrow'><td colspan='9'>%s</td></tr>"
                 % (n, esc(i["symbol"]), esc(i["symbol"]), esc(i["name"]), qty(i) if qty(i) else "—",
                    cls(q["dayPct"]) if q else "", pct(q["dayPct"]) if q else "—",
                    cls(se) if se is not None else "", pct(se) if se is not None else "—",
                    fmt(q["price"]) if q else "אין נתון", fmt(v, 0), spark_from_hist(qs2.get(i["symbol"]), 30, 84, 24),
                    stock_panel_html("posp-%d" % n, i, q, flex_pos)))))
        # mobile card for the same position (panel id suffixed -m; same accordion JS)
        mcards.append((v, ("<div class='pc-item'><div class='poscard' data-exp='posp-%d-m' tabindex='0' role='button' aria-expanded='false'>"
                 "<div class='pc-top'><span class='pc-sym'><a class='sym' href='/garp?s=%s'><b>%s</b></a></span><span class='pc-name'>%s</span><span class='pc-val'>%s</span></div>"
                 "<div class='pc-row'><span class='pill %s'>%s</span><span class='pill %s'>%s</span><span class='pc-meta'>%s</span>"
                 "<svg class='chev' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='currentColor' stroke-width='2.4' stroke-linecap='round' stroke-linejoin='round'><path d='M5 9 L12 16 L19 9'/></svg></div></div>%s</div>"
                 % (n, esc(i["symbol"]), esc(i["symbol"]), esc(i["name"]), fmt(v, 0) if v else "—",
                    cls(q["dayPct"]) if q else "", pct(q["dayPct"]) if q else "—",
                    cls(se) if se is not None else "", pct(se) if se is not None else "—",
                    ("%s × %s" % (qty(i), fmt(q["price"]))) if q and qty(i) else "—",
                    stock_panel_html("posp-%d-m" % n, i, q, flex_pos)))))
    # options (LEAPS) as rows in the positions summary — they were missing from home
    for m, (o, price, asof, live, fx) in enumerate(opts):
        oval = price * o["contracts"] * o.get("multiplier", 100) if price else None
        cm = fx.get("costMoney"); un = fx.get("unreal")
        se = (un / cm * 100) if cm and un is not None else None
        exp_txt = "%s %s %s" % (fx_exp_day(o), MONTHS[o["expiryMonth"]], o["expiryYear"])
        sym_lbl = "%s %s%s" % (o["underlying"], ("%g" % o["strike"]), "C" if o["optionType"] == "call" else "P")
        uq = {o["underlying"]: qs.get(o["underlying"])}
        mrows.append((oval, ("<tr class='posrow' data-exp='optp-%d' tabindex='0' role='button' aria-expanded='false'><td><a class='sym' href='/garp?s=%s'><b>%s</b></a></td><td>%s</td><td>%s</td>"
                 "<td><span class='muted'>—</span></td><td><span class='pill %s'>%s</span></td><td>%s</td><td><b>%s</b></td><td>%s</td>"
                 "<td><svg class='chev' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='currentColor' stroke-width='2.4' stroke-linecap='round' stroke-linejoin='round'><path d='M5 9 L12 16 L19 9'/></svg></td></tr>"
                 "<tr class='panelrow'><td colspan='9'><div class='sigpanel' id='optp-%d' hidden>%s</div></td></tr>"
                 % (m, esc(o["underlying"]), esc(sym_lbl),
                    "אופציית %s · סטרייק %s · פקיעה %s" % ("Call" if o["optionType"] == "call" else "Put", fmt(o["strike"], 0), esc(exp_txt)),
                    "%d חוזה" % o["contracts"],
                    cls(se) if se is not None else "", pct(se) if se is not None else "—",
                    fmt(price) if price else "אין נתון", fmt(oval, 0) if oval else "—",
                    spark_from_hist(qs2.get(o["underlying"]), 30, 84, 24),
                    m, opt_cards_html([(o, price, asof, live, fx)], uq)))))
        mcards.append((oval, ("<div class='pc-item'><div class='poscard' data-exp='optp-%d-m' tabindex='0' role='button' aria-expanded='false'>"
                 "<div class='pc-top'><span class='pc-sym'><a class='sym' href='/garp?s=%s'><b>%s</b></a></span><span class='pc-name'>%s</span><span class='pc-val'>%s</span></div>"
                 "<div class='pc-row'><span class='muted'>—</span><span class='pill %s'>%s</span><span class='pc-meta'>%s</span>"
                 "<svg class='chev' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='currentColor' stroke-width='2.4' stroke-linecap='round' stroke-linejoin='round'><path d='M5 9 L12 16 L19 9'/></svg></div></div><div class='sigpanel' id='optp-%d-m' hidden>%s</div></div>"
                 % (m, esc(o["underlying"]), esc(sym_lbl),
                    "אופציית %s · סטרייק %s · פקיעה %s" % ("Call" if o["optionType"] == "call" else "Put", fmt(o["strike"], 0), esc(exp_txt)),
                    fmt(oval, 0) if oval else "—",
                    cls(se) if se is not None else "", pct(se) if se is not None else "—",
                    ("%d חוזה · %s" % (o["contracts"], fmt(price))) if price else "%d חוזה" % o["contracts"],
                    m, opt_cards_html([(o, price, asof, live, fx)], uq)))))
    # positions sorted by value, descending (stocks + options together)
    rows = "".join(h for _, h in sorted(mrows, key=lambda t: -(t[0] or 0)))
    cards = "".join(h for _, h in sorted(mcards, key=lambda t: -(t[0] or 0)))
    mini = ("<h2 class='sec'>מה יש לי בתיק?</h2><div class='tblwrap mini-tbl'><table><thead><tr><th>סימול</th><th>שם</th><th>כמות</th><th>יום</th><th>מאז כניסה</th><th>מחיר</th><th>שווי</th><th data-sort='no'>מגמה 30 יום</th><th data-sort='no'></th></tr></thead><tbody>"
            + rows + "</tbody></table></div><div class='poscards'>" + cards + "</div><p><a href='/positions'>לכל הפירוט ←</a></p>")
    asof = "מחירים: Yahoo " + time.strftime("%H:%M %d/%m") + " (מטמון 10 דק׳) · Flex: " + (daily["file"] if daily else "—")
    return layout("מצב התיק", "/", snap_html + hero + perf_html + alloc_html + exp_html + mini + strip, asof)

def purchase_tax(price):
    tax = 0.0; prev = 0
    for cap, rate in TAX_BRACKETS:
        if cap is None or price <= cap:
            return tax + (price - prev) * rate
        tax += (cap - prev) * rate; prev = cap
    return tax

def annuity(principal, annual_pct, years):
    r = annual_pct / 100.0 / 12.0; n = years * 12
    if r == 0: return principal / n
    f = (1 + r) ** n
    return principal * r * f / (f - 1)

def _mtg_row(principal, annual_pct):
    pay = annuity(principal, annual_pct, MORT_YEARS)
    return pay, pay * MORT_YEARS * 12 - principal, pay * MORT_YEARS * 12

# ---------- house tab: cash available for buying a home (Oren, 10/11/2026) ----------
def page_house():
    fd = flex_data()
    daily = fd["daily"] if fd else None
    ils = get_quote("ILS=X")
    ils_rate = ils["price"] if ils else None
    meta_q = get_quote("META")
    meta_live = meta_q["price"] if meta_q and meta_q.get("price") else RSU_PRICE_USD  # live price for the reset button
    # portfolio net after loans (Norton excluded — informational only, Oren 8/11/2026)
    pf_planit_loans = PLANIT_LOANS_ILS - NORTON_LOAN_ILS
    total_loans = pf_planit_loans + TESLA_LOAN_BAL_ILS
    pf_ils = net_ils = tax_ils = net_after_tax = None
    if daily and daily.get("total") and ils_rate:
        pf_ils = daily["total"] * ils_rate
        net_ils = pf_ils - total_loans
        ytd_srs = sorted(fd["ytd"]["series"].items()) if fd and fd["ytd"].get("series") else None
        prof = (ytd_srs[-1][1] - ytd_srs[0][1] - sum(fd["ytd"]["flows"].values())) if ytd_srs else None
        tax_ils = (prof * 0.25 * ils_rate) if (prof is not None and ils_rate) else None
        net_after_tax = (pf_ils - total_loans - tax_ils) if tax_ils is not None else None
    rsu_net_ils = (rsu_net_usd(RSU_PRICE_USD) * ils_rate) if ils_rate else None
    if daily is None or ils_rate is None or rsu_net_ils is None:
        return layout("רכישת בית", "/house",
                      "<h2 class='sec'>מזומן זמין לרכישת בית</h2><div class='card'><div class='t'>נתונים חסרים</div><div class='s'>לא הצלחתי לטעון את נתוני Flex או את שער הדולר — נסה לרענן בעוד כמה דקות.</div></div>", "")
    asof = "Flex %s · שער דולר %.3f · RSU נכון ל־%s" % (dstr(daily["date"]), ils_rate, RSU_ASOF)
    # portfolio counts AFTER capital gains tax; RSU at the default realization % (Oren, 10/11/2026)
    pf_net = net_after_tax if net_after_tax is not None else net_ils
    rsu_realized_ils = rsu_net_ils * RSU_PCT_DEFAULT / 100.0
    rsu_shares = sum(sh for _, sh, _ in RSU_GRANTS)
    rsu_total_usd = rsu_shares * RSU_PRICE_USD  # gross value of all shares
    rsu_total_ils = (rsu_total_usd * ils_rate) if ils_rate else None
    rsu_gross_realized_ils = (rsu_total_ils * RSU_PCT_DEFAULT / 100.0) if rsu_total_ils is not None else None
    total = rsu_realized_ils + pf_net + (HOME_VALUE_ILS - MORTGAGE_ILS)
    inp = "width:100%;padding:9px 10px;border-radius:10px;border:1px solid var(--line2);background:var(--panel3);color:var(--tx);font-size:15px"
    chev = "<svg class='chev' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='currentColor' stroke-width='2.4' stroke-linecap='round' stroke-linejoin='round'><path d='M5 9 L12 16 L19 9'/></svg>"
    # purchase costs + top-up mortgage (Oren, 10/11/2026)
    buy_price = PURCHASE_PRICE_DEFAULT
    broker_fee = buy_price * BROKER_PCT * (1 + VAT_RATE)
    lawyer_fee = buy_price * LAWYER_PCT * (1 + VAT_RATE)
    ptax = purchase_tax(buy_price)
    total_cost = buy_price + broker_fee + lawyer_fee + ptax + RENOVATION_ILS
    mtg = max(0.0, total_cost - total)
    prime_rate = PRIME_RATE + PRIME_SPREAD  # 4.00% (prime 4.75% - 0.75)
    share = mtg / 3.0  # equal-thirds mix (Oren, 10/11/2026)
    prime_pay, prime_int, prime_tot = _mtg_row(share, prime_rate)
    fixed_pay, fixed_int, fixed_tot = _mtg_row(share, FIXED_RATE)
    var_pay, var_int, var_tot = _mtg_row(share, VAR_RATE)
    mix_pay = prime_pay + fixed_pay + var_pay
    mix_int = prime_int + fixed_int + var_int
    mix_tot = prime_tot + fixed_tot + var_tot
    purch_html = (
        "<h2 class='sec'>עלות רכישה</h2>"
        "<div class='card' style='margin-bottom:12px'>"
        "<div class='t'>עלות כוללת של רכישה</div>"
        "<div class='v' id='cost-total' dir='ltr'>" + fmt_ils(total_cost) + "</div>"
        "</div>"
        "<div class='card' style='margin-bottom:12px'><div class='t'>מחיר רכישה מבוקש</div>"
        "<input type='number' id='buy-price' value='" + str(PURCHASE_PRICE_DEFAULT) + "' step='50000' min='0' inputmode='numeric' style='" + inp + ";margin-top:8px' dir='ltr'>"
        "<div style='height:10px'></div>"
        "<div class='s' style='margin:10px 0 4px'>שיפוץ (₪)</div>"
        "<input type='number' id='reno-cost' value='" + str(RENOVATION_ILS) + "' step='10000' min='0' inputmode='numeric' style='" + inp + "' dir='ltr'>"
        "<label style='display:flex;align-items:center;gap:8px;margin-top:8px;font-size:13px;font-weight:700;cursor:pointer'><input type='checkbox' id='reno-incl' checked style='width:16px;height:16px;accent-color:var(--acc)'> לכלול שיפוץ בעלות הרכישה</label>"
        "<div class='drow'><span class='dl'>מחיר רכישה</span><span class='dv' dir='ltr' id='cost-price'>" + fmt_ils(buy_price) + "</span></div>"
        "<div class='drow'><span class='dl'>תיווך <span class='muted'>(2% + מע״מ 18%)</span></span><span class='dv' dir='ltr' id='cost-broker'>" + fmt_ils(broker_fee) + "</span></div>"
        "<div class='drow'><span class='dl'>שכ״ט עו״ד <span class='muted'>(0.5% + מע״מ 18%)</span></span><span class='dv' dir='ltr' id='cost-lawyer'>" + fmt_ils(lawyer_fee) + "</span></div>"
        "<div class='drow'><span class='dl'>מס רכישה <span class='muted'>(דירה יחידה, מדרגות 2026)</span></span><span class='dv' dir='ltr' id='cost-tax'>" + fmt_ils(ptax) + "</span></div>"
        "<div class='drow'><span class='dl'>שיפוץ</span><span class='dv' dir='ltr' id='cost-reno'>" + fmt_ils(RENOVATION_ILS) + "</span></div>"
        "<div class='s'>מזומן זמין: <b id='cost-cash'>" + fmt_ils(total) + "</b> · פער למימון: <b id='cost-gap'>" + fmt_ils(mtg) + "</b></div></div>"
        "<h2 class='sec'>משכנתא</h2>"
        "<div class='card xcard' data-exp='mtg-detail' tabindex='0' role='button' aria-expanded='false' style='margin-bottom:12px'>"
        "<div class='t' style='display:flex;align-items:center;justify-content:space-between'><span>משכנתא משלימה — החזר חודשי כולל</span>" + chev + "</div>"
        "<div class='v' dir='ltr'><span id='mtg-monthly'>" + fmt_ils(mix_pay) + "</span> <span class='muted' style='font-size:15px'>/חודש</span></div>"
        "<div class='s'>סכום משכנתא <b id='mtg-amount'>" + fmt_ils(mtg) + "</b> (≈ <span id='mtg-amount-usd'>" + fmt(mtg / ils_rate, 0) + "</span>) · החזר חודשי ≈ <span id='mtg-monthly-usd'>" + fmt(mix_pay / ils_rate, 0) + "</span> · 20 שנה (240 תשלומים) · תמהיל שליש/שליש/שליש</div>"
        "<div class='s' id='mtg-note'>" + ("אין צורך במשכנתא — נשאר עודף " + fmt_ils(total - total_cost) if mtg == 0 else "סכום המשכנתא = עלות כוללת פחות המזומן הזמין · פירוט בלחיצה") + "</div></div>"
        "<div class='sigpanel xpanel' id='mtg-detail' hidden>"
        "<div class='pt'>פירוט לפי מסלול — שליש מהסכום בכל מסלול</div>"
        "<div class='drow'><span class='dl'>פריים −0.75% <span class='muted'>(4.00% · שליש: <span id='trk-prime-share'>" + fmt_ils(share) + "</span>)</span></span><span class='dv' dir='ltr'>החזר <b id='trk-prime-pay'>" + fmt_ils(prime_pay) + "</b> <span class='muted'>/חודש</span></span></div>"
        "<div class='drow sub'><span class='dl'>סה״כ ריבית</span><span class='dv' dir='ltr'><span id='trk-prime-int'>" + fmt_ils(prime_int) + "</span> · סה״כ תשלומים <span id='trk-prime-tot'>" + fmt_ils(prime_tot) + "</span></span></div>"
        "<div class='drow'><span class='dl'>קבועה לא צמודה <span class='muted'>(4.62% · שליש: <span id='trk-fixed-share'>" + fmt_ils(share) + "</span>)</span></span><span class='dv' dir='ltr'>החזר <b id='trk-fixed-pay'>" + fmt_ils(fixed_pay) + "</b> <span class='muted'>/חודש</span></span></div>"
        "<div class='drow sub'><span class='dl'>סה״כ ריבית</span><span class='dv' dir='ltr'><span id='trk-fixed-int'>" + fmt_ils(fixed_int) + "</span> · סה״כ תשלומים <span id='trk-fixed-tot'>" + fmt_ils(fixed_tot) + "</span></span></div>"
        "<div class='drow'><span class='dl'>משתנה כל 5 שנים, לא צמודה <span class='muted'>(4.56% · שליש: <span id='trk-var-share'>" + fmt_ils(share) + "</span>)</span></span><span class='dv' dir='ltr'>החזר <b id='trk-var-pay'>" + fmt_ils(var_pay) + "</b> <span class='muted'>/חודש</span></span></div>"
        "<div class='drow sub'><span class='dl'>סה״כ ריבית</span><span class='dv' dir='ltr'><span id='trk-var-int'>" + fmt_ils(var_int) + "</span> · סה״כ תשלומים <span id='trk-var-tot'>" + fmt_ils(var_tot) + "</span></span></div>"
        "<div class='drow tot'><span class='dl'>סה״כ החזר חודשי</span><span class='dv' dir='ltr'><b id='trk-total-pay'>" + fmt_ils(mix_pay) + "</b> <span class='muted'>/חודש · <span id='trk-total-pay-usd'>" + fmt(mix_pay / ils_rate, 0) + "</span></span></span></div>"
        "<div class='drow'><span class='dl'>סה״כ ריבית (20 שנה)</span><span class='dv' dir='ltr' id='trk-total-int'>" + fmt_ils(mix_int) + "</span></div>"
        "<div class='drow'><span class='dl'>סה״כ תשלומים (20 שנה)</span><span class='dv' dir='ltr' id='trk-total-tot'>" + fmt_ils(mix_tot) + "</span></div>"
        "<div class='pfoot'>שפיצר, בהנחה שהריבית נשארת קבועה 20 שנה. פריים (4.00%) ומשתנה (4.56%) זזים עם הריבית; קבועה (4.62%) נעולה. בפועל הבנקים מערבבים מסלולים (משתנה עד ⅔ מההלוואה).</div></div>"
    )
    body = (
        "<h2 class='sec'>מבט כללי</h2>"
        "<div class='card' style='margin-bottom:12px;padding:12px 14px'><div style='display:flex;gap:10px;justify-content:space-between;text-align:center'>"
        "<div style='flex:1;min-width:0'><div class='s'>שווי נכסים</div><div dir='ltr' id='hdr-equity' style='font-size:17px;font-weight:800;color:var(--up)'>" + fmt_ils(total) + "</div></div>"
        "<div style='flex:1;min-width:0'><div class='s'>עלות רכישה</div><div dir='ltr' id='hdr-cost' style='font-size:17px;font-weight:800;color:var(--warn)'>" + fmt_ils(total_cost) + "</div></div>"
        "<div style='flex:1;min-width:0'><div class='s'>משכנתא</div><div dir='ltr' id='hdr-mtg' style='font-size:17px;font-weight:800;color:var(--down)'>" + fmt_ils(mtg) + "</div></div>"
        "</div></div>"
        "<div id='house-data' data-rsu-net='" + str(int(rsu_net_ils)) + "' data-pf-net='" + str(int(pf_net)) + "' data-ils-rate='" + str(ils_rate) + "' data-rsu-grants='" + json.dumps(RSU_GRANTS) + "' data-vest-grants='" + json.dumps(RSU_VEST_1511) + "' data-rsu-shares='" + str(sum(sh for _, sh, _ in RSU_GRANTS)) + "' data-meta-live='" + str(meta_live) + "' hidden></div>"
        "<h2 class='sec'>שווי נכסים</h2>"
        "<div class='card' style='margin-bottom:12px'>"
        "<div class='t'>סה״כ מזומן זמין</div>"
        "<div class='v' id='house-total' dir='ltr'>" + fmt_ils(total) + "</div>"
        "<div class='s' id='total-parts'>RSU " + fmt_ils(rsu_realized_ils) + " · תיק " + fmt_ils(pf_net) + " · דירה " + fmt_ils(HOME_VALUE_ILS - MORTGAGE_ILS) + "</div>"
        "<div class='btrack' style='height:8px;margin-top:10px'><div class='bfill up' id='fund-bar' style='width:" + str(min(100, round(total / total_cost * 100))) + "%'></div></div>"
        "<div class='s' id='fund-lbl'>" + ("המזומן מכסה את מלוא עלות הרכישה" if total >= total_cost else "המזומן מכסה " + str(round(total / total_cost * 100)) + "% מעלות הרכישה") + "</div>"
        "<div class='s'>התיק וה־RSU אחרי מס. נורטון (₪475,000) בנפרד.</div>"
        "</div>"
        "<div class='grid g-3'>"
        "<div class='card'><div class='t'>מניות Meta (RSU)</div>"
        "<div class='v' id='rsu-total' dir='ltr'>" + fmt_ils(rsu_gross_realized_ils) + "</div>"
        "<div class='s'>(סה״כ <b id='rsu-total-ils' dir='ltr'>" + fmt_ils(rsu_total_ils) + "</b> · <b id='rsu-total-usd' dir='ltr'>" + fmt(rsu_total_usd, 0) + "</b>)</div>"
        "<div class='s' style='margin:10px 0 4px'>מחיר מניית Meta ($)</div>"
        "<input type='number' id='meta-price' value='" + str(RSU_PRICE_USD) + "' step='1' min='0' inputmode='decimal' style='" + inp + "' dir='ltr'>"
        "<div style='margin-top:8px;display:flex;align-items:center;gap:8px'><button type='button' id='meta-reset' style='padding:7px 12px;border-radius:10px;border:1px solid var(--line2);background:var(--panel3);color:var(--tx);font-size:13px;font-weight:600;cursor:pointer'>⟲ איפוס למחיר העדכני</button><span class='s'>מחיר עדכני: <b id='meta-live-lbl' dir='ltr'>" + fmt(meta_live, 2) + "</b></span></div>"
        "<div class='s' style='margin:10px 0 6px'>כמה אחוז מהמניות לממש: <b id='rsu-pct-lbl'>50%</b></div>"
        "<input type='range' id='rsu-pct' min='0' max='100' step='5' value='50' style='width:100%;accent-color:var(--acc)'>"
        "<div class='btrack' style='height:8px;margin-top:10px'><div class='bfill' id='rsu-bar' style='width:" + str(RSU_PCT_DEFAULT) + "%'></div></div>"
        "<div class='s' id='rsu-bar-lbl'>מושכים " + fmt_ils(rsu_gross_realized_ils) + " (" + str(RSU_PCT_DEFAULT) + "%) · נשאר " + fmt_ils(rsu_total_ils - rsu_gross_realized_ils) + "</div>"
        "<div class='s' style='margin-top:8px'>ברוטו למכירה: <b id='rsu-gross-ils' dir='ltr'>" + fmt_ils(rsu_gross_realized_ils) + "</b> (<b id='rsu-gross-usd' dir='ltr'>" + fmt(rsu_total_usd * RSU_PCT_DEFAULT / 100.0, 0) + "</b>)</div>"
        "<div class='s'>נטו למכירה (אחרי מס): <b id='rsu-net-ils' dir='ltr'>" + fmt_ils(rsu_realized_ils) + "</b> (<b id='rsu-usd' dir='ltr'>" + fmt(rsu_net_usd(RSU_PRICE_USD) * RSU_PCT_DEFAULT / 100.0, 0) + "</b>)</div>"
        "</div>"
        "<div class='card'><div class='t'>תיק השקעות</div>"
        "<div class='v' dir='ltr'>" + fmt_ils(pf_net) + "</div>"
        "<div class='s'>שווי תיק " + fmt_ils(pf_ils) + " (Flex " + dstr(daily["date"]) + ") · הלוואות בתיק " + fmt_ils(total_loans) + " (Planit " + fmt_ils(pf_planit_loans) + " + טסלה " + fmt_ils(TESLA_LOAN_BAL_ILS) + ")</div>"
        "<div class='s'>מס רווחי הון משוער (25% על רווח מתחילת השנה): <b>" + (fmt_ils(tax_ils) if tax_ils is not None else "—") + "</b></div></div>"
        "<div class='card'><div class='t'>נדל״ן</div>"
        "<div class='v' id='realestate-total' dir='ltr'>" + fmt_ils(HOME_VALUE_ILS - MORTGAGE_ILS) + "</div>"
        "<div class='s' style='margin:10px 0 4px'>דירה נוכחית — תמורה נטו: <b id='home-net' dir='ltr'>" + fmt_ils(HOME_VALUE_ILS - MORTGAGE_ILS) + "</b></div>"
        "<div class='s' style='margin:10px 0 4px'>שווי הדירה (₪)</div>"
        "<input type='number' id='home-val' value='" + str(HOME_VALUE_ILS) + "' step='50000' min='0' inputmode='numeric' style='" + inp + "' dir='ltr'>"
        "<div class='s' style='margin:10px 0 4px'>יתרת משכנתא (₪)</div>"
        "<input type='number' id='mortgage' value='" + str(MORTGAGE_ILS) + "' step='10000' min='0' inputmode='numeric' style='" + inp + "' dir='ltr'>"
        "<div class='s' style='margin:12px 0 4px'>רמת השרון (ירמיהו 19) — <b id='ramat-val' dir='ltr'>" + fmt_ils(RAMAT_HASHARON_ILS) + "</b></div>"
        "<input type='number' id='ramat-amount' value='" + str(RAMAT_HASHARON_ILS) + "' step='50000' min='0' inputmode='numeric' style='" + inp + "' dir='ltr'>"
        "<label style='display:flex;align-items:center;gap:8px;margin-top:10px;font-size:14px;font-weight:700;cursor:pointer'><input type='checkbox' id='ramat-incl' style='width:18px;height:18px;accent-color:var(--acc)'> להכליל במזומן הזמין</label>"
        "<div class='s'>חלקנו 1/6 (מחיר מלא ₪8M). טרם נחתם; עמלה ומס לא מנוכים.</div>"
        "</div>"
        "</div>" + purch_html +
        "<div class='s' style='margin-top:4px'>מקורות: RSU — מחשבון Meta RSU Calculator (גיליון Summary), נכון ל־" + RSU_ASOF + "; תיק — Flex יומי; שער דולר חי. תרחיש לתכנון, לא ייעוץ.</div>"
        "<script>(function(){var d=document.getElementById('house-data');var pf=parseFloat(d.dataset.pfNet||'0'),rate=parseFloat(d.dataset.ilsRate||'0'),grants=JSON.parse(d.dataset.rsuGrants||'[]'),vgrants=JSON.parse(d.dataset.vestGrants||'[]'),rsuSh=parseFloat(d.dataset.rsuShares||'0');var brackets=[[1978745,0],[2347040,0.035],[6055070,0.05],[20183565,0.08],[null,0.10]];function fmt(v){return '₪'+Math.round(v).toLocaleString('en-US');}function fmtUsd(v){return '$'+Math.round(v).toLocaleString('en-US');}function rsuNetUsd(p){var s=0;for(var i=0;i<grants.length;i++){var g=grants[i];s+=g[1]*(0.5*Math.min(p,g[0])+g[2]*Math.max(p-g[0],0));}return s;}function vestNetUsd(p){var s=0;for(var i=0;i<vgrants.length;i++){var g=vgrants[i];s+=g[1]*(0.5*Math.min(p,g[0])+g[2]*Math.max(p-g[0],0));}return s;}function tax(p){var t=0,prev=0;for(var i=0;i<brackets.length;i++){var cap=brackets[i][0],rate=brackets[i][1];if(cap===null||p<=cap){t+=(p-prev)*rate;break;}t+=(cap-prev)*rate;prev=cap;}return t;}function ann(P,apr){var r=apr/100/12,n=240;if(r===0)return P/n;var f=Math.pow(1+r,n);return P*r*f/(f-1);}function upd(){var pct=parseFloat(document.getElementById('rsu-pct').value||'0');var hv=parseFloat(document.getElementById('home-val').value||'0');var mg=parseFloat(document.getElementById('mortgage').value||'0');var price=parseFloat(document.getElementById('meta-price').value||'0');var rsuUsd=rsuNetUsd(price);var r=rsuUsd*rate*pct/100,h=hv-mg;var ra=document.getElementById('ramat-incl').checked?(parseFloat(document.getElementById('ramat-amount').value||'0')):0;var cash=r+pf+h+ra;document.getElementById('rsu-pct-lbl').textContent=pct+'%';document.getElementById('rsu-total').textContent=fmt(price*rsuSh*rate*pct/100);document.getElementById('rsu-total-ils').textContent=fmt(price*rsuSh*rate);document.getElementById('rsu-total-usd').textContent=fmtUsd(price*rsuSh);document.getElementById('rsu-bar').style.width=pct+'%';document.getElementById('rsu-bar-lbl').textContent='מושכים '+fmt(price*rsuSh*rate*pct/100)+' ('+pct+'%) · נשאר '+fmt(price*rsuSh*rate*(100-pct)/100);document.getElementById('rsu-gross-ils').textContent=fmt(price*rsuSh*rate*pct/100);document.getElementById('rsu-gross-usd').textContent=fmtUsd(price*rsuSh*pct/100);document.getElementById('rsu-net-ils').textContent=fmt(r);document.getElementById('rsu-usd').textContent=fmtUsd(rsuUsd*pct/100);document.getElementById('home-net').textContent=fmt(h);document.getElementById('realestate-total').textContent=fmt(h+ra);document.getElementById('ramat-val').textContent=fmt(parseFloat(document.getElementById('ramat-amount').value||'0'));document.getElementById('ramat-val').style.opacity=document.getElementById('ramat-incl').checked?'1':'0.45';document.getElementById('house-total').textContent=fmt(cash);document.getElementById('total-parts').textContent='RSU '+fmt(r)+' · תיק '+fmt(pf)+' · דירה '+fmt(h)+(ra>0?' · רמה״ש '+fmt(ra):'');var bp=parseFloat(document.getElementById('buy-price').value||'0');var rn=document.getElementById('reno-incl').checked?(parseFloat(document.getElementById('reno-cost').value||'0')):0;var br=bp*0.02*1.18,lw=bp*0.005*1.18,tx=tax(bp),tc=bp+br+lw+tx+rn;var mt=Math.max(0,tc-cash);document.getElementById('cost-price').textContent=fmt(bp);document.getElementById('cost-broker').textContent=fmt(br);document.getElementById('cost-lawyer').textContent=fmt(lw);document.getElementById('cost-tax').textContent=fmt(tx);document.getElementById('cost-reno').textContent=fmt(rn);document.getElementById('cost-total').textContent=fmt(tc);document.getElementById('cost-cash').textContent=fmt(cash);document.getElementById('cost-gap').textContent=fmt(mt);document.getElementById('mtg-amount').textContent=fmt(mt);document.getElementById('mtg-amount-usd').textContent=fmtUsd(mt/rate);document.getElementById('hdr-mtg').textContent=fmt(mt);document.getElementById('hdr-equity').textContent=fmt(cash);document.getElementById('hdr-cost').textContent=fmt(tc);var covRaw=tc>0?cash/tc*100:0,cov=Math.min(100,covRaw);document.getElementById('fund-bar').style.width=cov+'%';document.getElementById('fund-lbl').textContent=covRaw>=100?'המזומן מכסה את מלוא עלות הרכישה':('המזומן מכסה '+Math.round(covRaw)+'% מעלות הרכישה');document.getElementById('mtg-note').textContent=mt===0?'אין צורך במשכנתא — נשאר עודף '+fmt(cash-tc):'סכום המשכנתא = עלות כוללת פחות המזומן הזמין · פירוט בלחיצה';var tracks=[['prime',4.00],['fixed',4.62],['var',4.56]];var mixPay=0,mixInt=0,mixTot=0;for(var i=0;i<tracks.length;i++){var sh=mt/3,pay=ann(sh,tracks[i][1]);mixPay+=pay;mixInt+=pay*240-sh;mixTot+=pay*240;document.getElementById('trk-'+tracks[i][0]+'-share').textContent=fmt(sh);document.getElementById('trk-'+tracks[i][0]+'-pay').textContent=fmt(pay);document.getElementById('trk-'+tracks[i][0]+'-int').textContent=fmt(pay*240-sh);document.getElementById('trk-'+tracks[i][0]+'-tot').textContent=fmt(pay*240);}document.getElementById('mtg-monthly').textContent=fmt(mixPay);document.getElementById('mtg-monthly-usd').textContent=fmtUsd(mixPay/rate);document.getElementById('trk-total-pay-usd').textContent=fmtUsd(mixPay/rate);document.getElementById('trk-total-pay').textContent=fmt(mixPay);document.getElementById('trk-total-int').textContent=fmt(mixInt);document.getElementById('trk-total-tot').textContent=fmt(mixTot);}['rsu-pct','home-val','mortgage','buy-price','meta-price','ramat-amount','reno-cost'].forEach(function(id){document.getElementById(id).addEventListener('input',upd);});document.getElementById('ramat-incl').addEventListener('change',upd);document.getElementById('reno-incl').addEventListener('change',upd);document.getElementById('meta-reset').addEventListener('click',function(){var live=parseFloat(d.dataset.metaLive||'0');if(!live)return;var i=document.getElementById('meta-price');i.value=live;i.dispatchEvent(new Event('input',{bubbles:true}));});upd();})();</script>"
    )
    return layout("רכישת בית", "/house", body, asof)


# ---------- signals page ----------
def page_signals():
    qs = get_quotes([i["symbol"] for i in POS + WATCH])
    fd = flex_data()
    daily = fd["daily"] if fd else None
    flex_pos = {}
    if daily:
        for p in daily["positions"]:
            if p["cat"] == "STK": flex_pos[norm(p["symbol"])] = p
    sigs = []
    for it in POS + WATCH:
        q = qs.get(it["symbol"])
        for s in signals_for(it, q):
            sigs.append((it, q, s))
    def sig_row(idx, it, q, s):
        sym = it["symbol"]; t = s["text"]; p = q["price"]
        tok = t.split(" ", 1)[0]
        if tok == sym and " " in t:
            main_txt = "<a class='sym' href='/garp?s=%s'>%s</a>%s" % (esc(sym), esc(sym), esc(t[len(tok):]))
        else:
            main_txt = esc(t)
        fields = ""
        if s.get("ma"):
            fields += "<span class='sf'><span class='sfk'>ממוצע 150</span><b>%s</b></span>" % fmt(q.get("ma150"))
            fields += "<span class='sf'><span class='sfk'>ממוצע 200</span><b>%s</b></span>" % fmt(q.get("ma200"))
        elif s.get("level"):
            lv = s["level"]
            fields += "<span class='sf'><span class='sfk'>%s</span><b>%s</b></span>" % (esc(lv["label"]), fmt(lv["value"]))
            if lv.get("band"):
                fields += "<span class='sf'><span class='sfk'>רצועת קנייה</span><b>%s – %s</b></span>" % (fmt(lv["band"][0]), fmt(lv["band"][1]))
        fields += "<span class='sf'><span class='sfk'>מחיר נוכחי</span><b>%s</b></span>" % fmt(p)
        if s.get("level"):
            g = (p / s["level"]["value"] - 1) * 100
            fields += "<span class='sf'><span class='sfk'>פער מהרמה</span><span class='pill %s'>%s</span></span>" % (cls(g), pct(g))
        return ("<div class='sigitem'><div class='sigrow' data-exp='sigp-%d' tabindex='0' role='button' aria-expanded='false'>%s"
                "<span class='sigmain'>%s</span><span class='sigfields'>%s</span>"
                "<svg class='chev' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='currentColor' stroke-width='2.4' stroke-linecap='round' stroke-linejoin='round'><path d='M5 9 L12 16 L19 9'/></svg></div>"
                % (idx, _sig_icon(s["kind"]), main_txt, fields)
                + stock_panel_html("sigp-%d" % idx, it, q, flex_pos) + "</div>")
    sig_html = "<h2 class='sec'>אותות</h2><div class='sigfeed'>"
    sig_html += ("".join(sig_row(n, it, q, s) for n, (it, q, s) in enumerate(sigs)) if sigs else "<div class='empty'>אין אותות כניסה/יציאה/צלב פעילים כרגע.</div>")
    sig_html += "<div class='sigrow'>" + _sig_icon("info") + "<div>בדיקות GARP מחדש אחרי דוחות (09:00 בבוקר שאחרי): NFLX — 21/10 · V — 28/10 · MSFT — 29/10 · MA — 30/10</div></div></div>"
    asof = "מחירים: Yahoo " + time.strftime("%H:%M %d/%m") + " (מטמון 10 דק׳) · Flex: " + (daily["file"] if daily else "—")
    return layout("אותות", "/signals", sig_html, asof)

# ---------- page 2 ----------
def page_positions(mode="day"):
    fd = flex_data()
    daily = fd["daily"] if fd else None
    fifo = fd["ytd"].get("fifo_stk", {}) if fd else {}
    first_buy = fd["ytd"]["first_buy"] if fd else {}
    closed_cost = fd["ytd"]["closed_cost"] if fd else {}
    flex_pos = {}
    if daily:
        for p in daily["positions"]:
            if p["cat"] == "STK": flex_pos[norm(p["symbol"])] = p
    syms = [i["symbol"] for i in POS]
    qs = get_quotes(syms)
    qs2 = _quotes2(syms)
    und_syms = sorted({o["underlying"] for o in OPTIONS})
    uq = get_quotes(und_syms)
    def qty(i):
        fp = flex_pos.get(norm(i["symbol"]))
        return fp["qty"] if fp else i.get("shares")
    def val(i):
        q = qs.get(i["symbol"]); n = qty(i)
        return q["price"] * n if q and n else None
    tot = sum(v for i in POS if (v := val(i))) or 1
    toggle = "<div class='toggle'>" + "".join(
        "<a href='/positions?p=%s' class='%s'>%s</a>" % (m, "on" if m == mode else "", t)
        for m, t in [("day", "היום"), ("month", "החודש"), ("entry", "מאז כניסה")]) + "</div>"
    def pnl_cell(v, p, dec=0):
        if v is None: return "<td class='muted'>—</td>"
        wdt = min(100, abs(p) * 8) if p is not None else 0
        return ("<td data-v='%s'><span class='pnlwrap'><b class='%s'>%s</b>"
                "<span class='pnlbar'><i style='width:%.0f%%;background:%s'></i></span></span></td>"
                % (v, cls(v), fmt(v, dec), wdt, "var(--up)" if v >= 0 else "var(--down)"))
    head_extra = ""
    if mode == "day": head_extra = "<th>שינוי יום</th><th>רווח יום $</th>"
    elif mode == "month": head_extra = "<th>שינוי חודש</th><th>רווח חודש $ (לפי כמות נוכחית)</th>"
    else: head_extra = "<th>כניסה ראשונה</th><th>עלות ממוצעת</th><th>ממומש</th><th>לא ממומש</th><th>סה״כ מאז כניסה</th>"
    rows = ""; prows = []
    for i in POS:
        s = i["symbol"]; ns = norm(s); q = qs.get(s); v = val(i)
        fp = flex_pos.get(ns); fg = fifo.get(ns, {})
        base = ("<td><b>" + esc(s) + "</b></td><td data-v='" + (("%g" % qty(i)) if qty(i) else "") + "'>" + (("%g" % qty(i)) if qty(i) else "—") + "</td><td data-v='" + (str(q["price"]) if q else "") + "'>" + (fmt(q["price"]) if q else "אין נתון")
                + "</td><td data-v='" + (str(v) if v else "") + "'><b>" + fmt(v, 0) + "</b> <span class='muted'>(" + (f"{v/tot*100:.1f}%" if v else "—") + ")</span></td>"
                + "<td data-sort='no'>" + spark_from_hist(qs2.get(s), 30, 84, 24) + "</td>")
        if mode == "day":
            d_usd = (v - v / (1 + q["dayPct"] / 100.0)) if q and v and q["dayPct"] != -100 else None
            extra = ("<td data-v='%s'><span class='pill %s'>%s</span></td>" % (q["dayPct"] if q else "", cls(q["dayPct"]) if q else "", pct(q["dayPct"]) if q else "—")) + pnl_cell(d_usd, q["dayPct"] if q else None)
        elif mode == "month":
            if q and q.get("monthClose") and qty(i):
                m_usd = qty(i) * (q["price"] - q["monthClose"]); m_pct = (q["price"] / q["monthClose"] - 1) * 100
                extra = ("<td data-v='%s'><span class='pill %s'>%s</span></td>" % (m_pct, cls(m_pct), pct(m_pct))) + pnl_cell(m_usd, m_pct)
            else:
                extra = "<td colspan='2' class='muted'>אין נתון חודשי</td>"
        else:
            fb = first_buy.get(ns); avg = fp["costPrice"] if fp else None
            realized = fg.get("realized"); unreal = (fp["unreal"] if fp else fg.get("unrealized"))
            totp = (realized or 0) + (unreal or 0) if (realized is not None or unreal is not None) else None
            cost_tot = (fp["costMoney"] if fp else 0) or 0
            cost_tot = (cost_tot or 0) + (closed_cost.get(ns, 0) or 0)
            tpct = (totp / cost_tot * 100) if totp is not None and cost_tot else None
            if totp is not None:
                wdt = min(100, abs(tpct) * 3) if tpct is not None else 0
                tot_cell = ("<td data-v='%s'><span class='pnlwrap'><span><b class='%s'>%s</b> <span class='muted'>(%s)</span></span>"
                            "<span class='pnlbar'><i style='width:%.0f%%;background:%s'></i></span></span></td>"
                            % (totp, cls(totp), fmt(totp, 0), pct(tpct), wdt, "var(--up)" if totp >= 0 else "var(--down)"))
            else:
                tot_cell = "<td class='muted'>—</td>"
            extra = ("<td>%s</td><td data-v='%s'>%s</td><td class='%s' data-v='%s'>%s</td><td class='%s' data-v='%s'>%s</td>" % (
                dstr(fb) if fb else "—", avg if avg is not None else "", fmt(avg), cls(realized), realized if realized is not None else "", fmt(realized, 0) if realized is not None else "—",
                cls(unreal), unreal if unreal is not None else "", fmt(unreal, 0) if unreal is not None else "—")) + tot_cell
        d150 = ((q["price"]/q["ma150"]-1)*100) if q and q.get("ma150") else None
        d200 = ((q["price"]/q["ma200"]-1)*100) if q and q.get("ma200") else None
        entry_html = fmt(i.get("entryPrice")) + ((" <span class='muted'>(" + entry_label(i) + ")</span>") if i.get("entryPrice") else "")
        prows.append((v, ("<tr class='clickable' data-href='/garp?s=%s'>" % esc(s) + base + extra
                 + "<td data-v='" + (str(q["ma150"]) if q and q.get("ma150") else "") + "'>" + (fmt(q.get("ma150")) if q else "—") + " <span class='muted'>(" + pct(d150) + ")</span></td><td data-v='" + (str(q["ma200"]) if q and q.get("ma200") else "") + "'>"
                 + (fmt(q.get("ma200")) if q else "—") + " <span class='muted'>(" + pct(d200) + ")</span></td><td>" + esc(method_label(i.get("method")))
                 + "</td><td data-v='" + (str(i.get("fairPrice")) if i.get("fairPrice") else "") + "'>" + fmt(i.get("fairPrice")) + "</td><td>" + entry_html + "</td><td data-v='" + (str(i.get("exitPrice")) if i.get("exitPrice") else "") + "'>" + fmt(i.get("exitPrice")) + "</td></tr>")))
    # positions sorted by value, descending (default order; the table stays user-sortable)
    rows = "".join(h for _, h in sorted(prows, key=lambda t: -(t[0] or 0)))
    search = "<input type='search' id='tblsearch' placeholder='🔎 חיפוש מניה…' aria-label='חיפוש מניה'>"
    tbl = ("<h2 class='sec'>מניות — פירוט מלא</h2><div class='searchbar'>" + toggle + search + "</div>"
           "<div class='tblwrap' data-filter-rows><table class='sortable'><thead><tr><th>סימול</th><th>כמות</th><th>מחיר</th><th>שווי (משקל)</th><th data-sort='no'>מגמה 30 יום</th>" + head_extra +
           "<th>ממוצע 150 (מרחק)</th><th>ממוצע 200 (מרחק)</th><th>שיטה</th><th>מחיר הוגן</th><th>כניסה / ראש רצועה</th><th>יציאה</th></tr></thead><tbody>" + rows + "</tbody></table></div>")
    if mode == "entry":
        tbl += ("<p class='foot'>מאז כניסה: לכל מניה בנפרד כמו בדוח אינטראקטיב — ממומש ולא־ממומש מ-FIFO של IB (דוח YTD עד %s; לא־ממומש מעודכן לדוח היומי %s), אחוז מול עלות כוללת (פתוחה + סגורה). כמויות ועלות ממוצעת: Flex יומי.</p>"
                % (dstr(fd["ytd"]["stmt_to"]) if fd else "—", dstr(daily["date"]) if daily else "—"))
    fifo_all = fd["ytd"]["fifo"] if fd else {}
    open_any = set()
    if daily:
        for p in daily["positions"]:
            open_any.add(norm(p.get("underlying") or p["symbol"]))
    pos_syms = {norm(i["symbol"]) for i in POS}
    closed_rows = ""
    for ns, fg in sorted(fifo_all.items()):
        if ns in open_any or ns in pos_syms: continue
        if not (fg.get("cats", set()) & {"STK", "OPT"}): continue
        if not fg.get("realized") and not fg.get("total"): continue
        cc = closed_cost.get(ns, 0)
        rpct = (fg["realized"] / cc * 100) if cc else None
        closed_rows += "<tr><td><b>%s</b></td><td>%s</td><td>%s</td><td class='%s' data-v='%s'>%s <span class='muted'>(%s)</span></td></tr>" % (
            esc(ns), dstr(first_buy.get(ns)) if first_buy.get(ns) else "—", dstr(fd["ytd"]["last_trade"].get(ns)) if fd else "—",
            cls(fg["realized"]), fg["realized"], fmt(fg["realized"], 0), pct(rpct))
    ctbl = ""
    if closed_rows:
        ctbl = ("<h2 class='sec'>פוזיציות שנסגרו (2026, ממומש בלבד)</h2><div class='tblwrap'><table class='sortable closedtbl'><thead><tr><th>סימול</th><th>כניסה ראשונה</th><th>עסקה אחרונה</th><th>רווח ממומש</th></tr></thead><tbody>" + closed_rows + "</tbody></table></div>"
                "<p class='foot'>מקור: FIFO של IB מדוח ה-YTD (עד %s). כולל גם סימבולים מחוץ לרשימת המעקב.</p>" % (dstr(fd["ytd"]["stmt_to"]) if fd else "—"))
    opts = load_options_data(fd)
    otbl = "<h2 class='sec'>אופציות LEAPS</h2>" + opt_cards_html(opts, uq)
    return layout("פירוט פוזיציות", "/positions", tbl + ctbl + otbl, "מחירים: Yahoo · כמויות/עלויות: IB Flex")

# ---------- page 3 ----------
def page_garp(sel):
    stocks = POS + WATCH
    if not sel or sel not in [s["symbol"] for s in stocks]: sel = "META"
    it = next(s for s in stocks if s["symbol"] == sel)
    q = get_quote(sel)
    q2 = get_quote(sel, "2y")
    fd = flex_data()
    opts_sel = "<form method='get' action='/garp'><select name='s' onchange='this.form.submit()' aria-label='בחירת מניה'>" + "".join(
        "<option value='%s' %s>%s — %s</option>" % (esc(s["symbol"]), "selected" if s["symbol"] == sel else "", esc(s["symbol"]), esc(s["name"])) for s in stocks) + "</select></form>"
    fair, entry, exitp = it.get("fairPrice"), it.get("entryPrice"), it.get("exitPrice")
    bot = band_bottom(it); p = q["price"] if q else None
    def dist(v): return pct((p/v-1)*100) if p and v else "—"
    # flagship header
    head = "<div class='stockhead'><div class='ssym'>%s · %s &nbsp;<span class='badge'>%s</span></div>" % (esc(sel), esc(it["name"]), esc(method_label(it.get("method"))))
    head += "<div style='display:flex;align-items:baseline;gap:13px;flex-wrap:wrap;margin-top:4px'><span class='sprice num'>%s</span>" % fmt(p)
    if q: head += "<span class='pill %s' style='font-size:15px'>%s היום</span>" % (cls(q["dayPct"]), pct(q["dayPct"]))
    head += "</div>"
    if q and q.get("high52") and q.get("low52") and q["high52"] > q["low52"]:
        wp = max(0.0, min(100.0, (p - q["low52"]) / (q["high52"] - q["low52"]) * 100))
        head += ("<div class='w52' dir='ltr'><div class='wtrack'><div class='wmark' style='left:%.1f%%'></div></div>"
                 "<div class='wlbls'><span>שפל 52 שבועות %s</span><span>שיא 52 שבועות %s</span></div></div>"
                 % (wp, fmt(q["low52"]), fmt(q["high52"])))
    head += "</div>"
    # big price chart
    chart_sec = ""
    if q2:
        svg, legend = price_chart_svg(q2, it)
        if svg:
            chart_sec = "<h2 class='sec'>גרף מחיר — שנה אחרונה, ממוצעים ורמות שיטה</h2><div class='card framecard'>%s%s</div>" % (svg, legend)
    # levels track
    track = levels_track_html(it, p) if p else ""
    track_sec = ("<h2 class='sec'>מחיר מול רמות</h2><div class='card' style='padding:6px 14px 2px'>" + track + "</div>") if track else ""
    # stats grid (same cards as before, restyled)
    kv = "<h2 class='sec'>רמות ונתוני שיטה</h2><div class='kv'>"
    kv += "<div class='card'><div class='t'>סיווג שיטה</div><div class='v'>%s</div></div>" % esc(method_label(it.get("method")))
    kv += "<div class='card'><div class='t'>מחיר נוכחי</div><div class='v'>%s</div><div class='%s'>%s היום</div></div>" % (fmt(p), cls(q["dayPct"]) if q else "", pct(q["dayPct"]) if q else "")
    if fair: kv += "<div class='card'><div class='t'>מחיר הוגן</div><div class='v'>%s</div><div class='muted'>מרחק: %s</div></div>" % (fmt(fair), dist(fair))
    if entry:
        kv += "<div class='card'><div class='t'>%s</div><div class='v'>%s</div><div class='muted'>מרחק: %s</div></div>" % (entry_label(it), fmt(entry), dist(entry))
    if it.get("method") in ("garp", "garp_blocked") and fair:
        kv += "<div class='card'><div class='t'>רצועת קנייה (ראש–תחתית)</div><div class='v'>%s – %s</div></div>" % (fmt(entry), fmt(bot))
    if exitp: kv += "<div class='card'><div class='t'>מחיר יציאה</div><div class='v'>%s</div><div class='muted'>מרחק: %s</div></div>" % (fmt(exitp), dist(exitp))
    if q and q.get("ma150"): kv += "<div class='card'><div class='t'>ממוצע נע 150 / 200</div><div class='v'>%s / %s</div><div class='muted'>מרחק: %s / %s · שיא 52ש׳ %s · שפל %s</div></div>" % (fmt(q["ma150"]), fmt(q["ma200"]), pct((p/q["ma150"]-1)*100), pct((p/q["ma200"]-1)*100), fmt(q.get("high52")), fmt(q.get("low52")))
    ns = norm(sel); fg = ((fd["ytd"].get("fifo_stk") or fd["ytd"]["fifo"]).get(ns) if fd else None)
    if fg and it["kind"] == "position":
        kv += "<div class='card'><div class='t'>מאז כניסה (IB FIFO)</div><div class='v %s'>%s</div><div class='muted'>ממומש %s · לא ממומש %s · כניסה %s</div></div>" % (
            cls(fg["total"]), fmt(fg["total"], 0), fmt(fg["realized"], 0), fmt(fg["unrealized"], 0), dstr(fd["ytd"]["first_buy"].get(ns)) if fd["ytd"]["first_buy"].get(ns) else "—")
    kv += "</div>"
    # my-position stats (Flex daily + first buy + month)
    pos_sec = ""
    if it["kind"] == "position" and fd:
        fp = None
        if fd.get("daily"):
            for pp in fd["daily"]["positions"]:
                if pp["cat"] == "STK" and norm(pp["symbol"]) == ns: fp = pp
        shares = fp["qty"] if fp else it.get("shares")
        live_val = (p * shares) if (p and shares) else None
        mret = ((p / q["monthClose"] - 1) * 100) if q and q.get("monthClose") and p else None
        cards = "<div class='kv'>"
        if shares: cards += "<div class='card'><div class='t'>כמות מניות</div><div class='v'>%g</div></div>" % shares
        if live_val: cards += "<div class='card'><div class='t'>שווי חי</div><div class='v'>%s</div></div>" % fmt(live_val, 0)
        if fp and fp.get("costPrice"): cards += "<div class='card'><div class='t'>עלות ממוצעת (IB)</div><div class='v'>%s</div></div>" % fmt(fp["costPrice"])
        if fp and fp.get("unreal") is not None: cards += "<div class='card'><div class='t'>לא ממומש (IB, %s)</div><div class='v %s'>%s</div></div>" % (dstr(fd["daily"]["date"]), cls(fp["unreal"]), fmt(fp["unreal"], 0))
        fb = fd["ytd"]["first_buy"].get(ns)
        if fb: cards += "<div class='card'><div class='t'>כניסה ראשונה</div><div class='v'>%s</div></div>" % dstr(fb)
        if mret is not None: cards += "<div class='card'><div class='t'>שינוי החודש</div><div class='v %s'>%s</div></div>" % (cls(mret), pct(mret))
        cards += "</div>"
        if "<div class='card'>" in cards: pos_sec = "<h2 class='sec'>הפוזיציה שלי</h2>" + cards
    leaps = [o for o in load_options_data(fd) if o[0]["underlying"] == sel]
    leap_html = ""
    if leaps:
        leap_html = "<h2 class='sec'>אופציות LEAPS על %s</h2>%s" % (esc(sel), opt_cards_html(leaps, {sel: q} if q else {}))
    charts = MANIFEST.get(sel) or []
    chart_html = "<h2 class='sec'>גרפי GARP</h2>"
    if charts:
        for c in charts:
            chart_html += "<div class='card framecard'><div class='cap'>%s</div><img class='chart' src='/charts/%s' alt='גרף GARP'></div>" % (esc(c.get("caption", "")), esc(os.path.basename(c["file"])))
    else:
        chart_html += "<div class='empty'>אין גרף GARP שמור למניה זו.</div>"
    note = "<h2 class='sec'>הערות וניתוח</h2><div class='note'>%s</div>" % esc(it.get("note") or "אין הערה שמורה.")
    return layout("GARP — " + sel, "/garp", "<h2 class='sec'>בחירת מניה</h2>" + opts_sel + "<div style='height:14px'></div>" + head + chart_sec + track_sec + kv + pos_sec + leap_html + chart_html + note)

# ---------- page 4: daily digest ----------
DIGEST_DIR = os.path.join(BASE, "digest")
SECTIONS = [("email", "מיילים"), ("discord", "דיסקורד"), ("whatsapp", "וואטסאפ"), ("x", "X"), ("youtube", "YouTube")]
SRC_COLORS = {"email": "#4da3ff", "discord": "#8b9cf9", "whatsapp": "#31c573", "x": "#9aa7bd", "youtube": "#f45d5d"}
def digest_dates():
    try:
        return sorted([os.path.basename(f)[:-5] for f in glob.glob(os.path.join(DIGEST_DIR, "20??-??-??.json"))], reverse=True)
    except Exception: return []
def linkify(text, syms):
    out = esc(text)
    for s in sorted(syms, key=len, reverse=True):
        if len(s) < 3: continue
        out = re.sub(r"(?<![A-Za-z])" + re.escape(s) + r"(?![A-Za-z])",
                     "<a href='/garp?s=%s'><b>%s</b></a>" % (s, s), out)
    return out
def _pill_date(d):
    return (d[8:10] + "/" + d[5:7] + "/" + d[0:4]) if len(d) == 10 else d
def page_daily(dsel):
    dates = digest_dates()
    if not dsel:
        try:
            ptr = json.load(open(os.path.join(DIGEST_DIR, "latest.json"), encoding="utf-8"))
            dsel = ptr.get("date")
        except Exception: dsel = None
    if not dsel and dates: dsel = dates[0]
    switcher = "<div class='datepills'>" + "".join(
        "<a href='/daily?d=%s' class='%s'>%s</a>" % (d, "on" if d == dsel else "", _pill_date(d)) for d in dates[:14]) + "</div>"
    if not dsel:
        return layout("סיכום יומי", "/daily", "<h2 class='sec'>סיכום יומי</h2><div class='empty'>טרם הגיע סיכום ראשון לאתר. הסיכומים מוזנים מהדיג'סט היומי.</div>")
    try:
        dg = json.load(open(os.path.join(DIGEST_DIR, dsel + ".json"), encoding="utf-8"))
    except Exception:
        return layout("סיכום יומי", "/daily", "<h2 class='sec'>סיכום יומי</h2>" + switcher + "<div class='empty'>אין סיכום לתאריך זה.</div>")
    body = "<h2 class='sec'>סיכום יומי — %s</h2>%s" % (_pill_date(dsel), switcher)
    if dg.get("generated_at"): body += "<p class='muted small'>עודכן: %s · מקור: דיג'סט החדשות הפיננסיות (Space)</p>" % esc(dg["generated_at"])
    if dg.get("highlights"):
        body += "<h2 class='sec'>עיקרי היום</h2><div class='sigfeed'>" + "".join(
            "<div class='hl-item'><span class='hl-num'>%d</span><div>%s</div></div>" % (n + 1, linkify(h, KNOWN_SYMS))
            for n, h in enumerate(dg["highlights"])) + "</div>"
    if dg.get("summary"):
        body += "<h2 class='sec'>תקציר</h2><div class='note'>%s</div>" % linkify(dg["summary"], KNOWN_SYMS)
    secs = dg.get("sections", {})
    for key, label in SECTIONS:
        sec = secs.get(key) or {}
        items = sec.get("items") or []
        body += ("<div class='sechead'><span class='srcdot' style='background:%s'></span><h2>%s</h2>"
                 "<span class='count'>%d פריטים</span></div>" % (SRC_COLORS.get(key, "#4da3ff"), label, len(items)))
        meta = []
        if sec.get("updated_at"): meta.append("עודכן " + sec["updated_at"])
        if sec.get("note"): meta.append(sec["note"])
        if meta: body += "<p class='muted small' style='margin:0 0 4px'>%s</p>" % esc(" · ".join(meta))
        if not items:
            body += "<div class='empty'>טרם עודכן היום.</div>"; continue
        for it in items:
            chips = ""
            for t in (it.get("tickers") or []):
                if t in KNOWN_SYMS: chips += "<a class='chip' href='/garp?s=%s'>%s</a>" % (esc(t), esc(t))
                else: chips += "<span class='chip'>%s</span>" % esc(t)
            title = esc(it.get("headline") or "")
            if it.get("url"): title = "<a href='%s' target='_blank' rel='noopener'>%s</a>" % (esc(it["url"]), title)
            meta2 = esc(it.get("source_name") or "")
            if it.get("time"): meta2 += (" · " + esc(it["time"])) if meta2 else esc(it["time"])
            if it.get("url"): meta2 += " · <a class='srclink' href='%s' target='_blank' rel='noopener'>למקור ←</a>" % esc(it["url"])
            body += ("<div class='ditem'><h3>%s</h3><p>%s</p><div class='meta'>%s%s</div></div>") % (
                title, linkify(it.get("summary") or "", KNOWN_SYMS), meta2, (" · " + chips) if chips else "")
    return layout("סיכום יומי", "/daily", body, "סיכום מיום " + _pill_date(dsel))

class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def do_GET(self):
        u = urllib.parse.urlparse(self.path); qs = urllib.parse.parse_qs(u.query)
        try:
            if u.path == "/": body, ct = page_home(), "text/html; charset=utf-8"
            elif u.path == "/signals": body, ct = page_signals(), "text/html; charset=utf-8"
            elif u.path == "/positions": body, ct = page_positions((qs.get("p") or ["day"])[0]), "text/html; charset=utf-8"
            elif u.path == "/garp": body, ct = page_garp((qs.get("s") or ["META"])[0]), "text/html; charset=utf-8"
            elif u.path == "/house": body, ct = page_house(), "text/html; charset=utf-8"
            elif u.path == "/daily": body, ct = page_daily((qs.get("d") or [None])[0]), "text/html; charset=utf-8"
            elif u.path.startswith("/charts/"):
                name = os.path.basename(u.path)
                fp = os.path.join(BASE, "charts", name)
                if not os.path.isfile(fp): return self.send_error(404)
                data = open(fp, "rb").read()
                self.send_response(200); self.send_header("Content-Type", "image/png"); self.send_header("Content-Length", str(len(data))); self.end_headers(); self.wfile.write(data); return
            elif u.path == "/health": body, ct = "ok", "text/plain"
            else: return self.send_error(404)
            b = body.encode() if isinstance(body, str) else body
            self.send_response(200); self.send_header("Content-Type", ct); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)
        except Exception as e:
            self.send_error(500, str(e))

if __name__ == "__main__":
    ThreadingHTTPServer(("127.0.0.1", 8080), H).serve_forever()
