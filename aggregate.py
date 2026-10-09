#!/usr/bin/env python3
"""Gathers every feed in sources.json, sorts each story into the page's tabs, and writes news.json.

Tabs: AI supply chain, Data centres, AI safety, China, US, UK, India. A story can sit in more than one tab.
Standard library only. Run:  python3 aggregate.py
"""
import concurrent.futures as cf
import email.utils
import html
import json
import os
import re
import sys
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
MAX_AGE_DAYS = 30
MAX_PER_FEED = 20
TIMEOUT = 20
UA = "Mozilla/5.0 (compatible; PerceptronicsNewsBot/1.0; +https://www.perceptronics.org)"

TABS = ["AI supply chain", "Data centres", "AI safety", "China", "US", "UK", "India"]

# ---- relevance filters (f in sources.json): 1 = AI only, 2 = data centres only, 3 = AI or supply chain
AI_RE = re.compile(r"\b(AI|A\.I\.|artificial intelligence|machine learning|generative|chatbot|ChatGPT|OpenAI|Anthropic|Gemini|DeepSeek|Grok|LLM|deepfake|algorithm|facial recognition)\b", re.I)
DC_RE = re.compile(r"\bdata ?(center|centre)s?\b|\bhyperscal|\bAI (campus|factory|factories)\b|\bcompute\b", re.I)
SC_RE = re.compile(r"\b(chips?|semiconductors?|TSMC|ASML|foundry|foundries|lithograph\w*|HBM|GPUs?|Nvidia|export controls?|rare earths?|critical minerals?|gallium|germanium|supply chains?|data ?(center|centre)s?|data (labell?ers|workers)|content moderators)\b", re.I)

# ---- topic and place rules: what a story is about decides its tabs
# (US / UK / AI stay case-sensitive so ordinary words like "us" or "uk" don't match)
RX_SC = re.compile(r"\b(chips?|semiconductors?|TSMC|ASML|foundry|foundries|lithograph\w*|HBM|GPUs?|Nvidia|export controls?|rare earths?|critical minerals?|gallium|germanium|supply chains?|data (labell?ers|workers)|content moderators)\b", re.I)
RX_DC = re.compile(r"\bdata ?(center|centre)s?\b|\bhyperscal\w*|\bAI (campus|factory|factories)\b", re.I)
RX_CN = re.compile(r"\b(China|Chinese|Beijing|Shanghai|Shenzhen|Hangzhou|Huawei|SMIC|Alibaba|Tencent|Baidu|DeepSeek|Moonshot|ByteDance|Xiaomi|Xi Jinping)\b")
RX_US = re.compile(r"\b(U\.S\.|US|USA|United States|America|Americans?|Washington|White House|Congress\w*|Senate|Senators?|Pentagon|FTC|Trump|Biden|Silicon Valley|California|Texas|Virginia|Arizona|Ohio|Nevada|Commerce Department|Capitol Hill)\b")
RX_UK = re.compile(r"\b(UK|U\.K\.|Britain|British|England|Scotland|Wales|London|Westminster|Whitehall|Starmer|Ofcom|DSIT|Downing Street|Manchester|Cumbria)\b")
RX_IN = re.compile(r"\b(India|Indian|Indians|Delhi|Mumbai|Bengaluru|Bangalore|Hyderabad|Chennai|Pune|Modi|MeitY|Lok Sabha|Rajya Sabha|Maharashtra|Tamil Nadu|Telangana|Karnataka|Gujarat|Reliance|Adani|Infosys|Wipro)\b")
RX_SAF = re.compile(r"\b(AI safety|AI Safety Institutes?|AI Security Institutes?|AISI|CAISI|frontier (AI|models?)|AI (Act|regulations?|governance|treaty|treaties|laws?|bills?|rules|oversight|safeguards?|guardrails?|standards)|(regulat\w+|legislat\w+|govern\w+) (of |on |for )?(AI|artificial intelligence)|(AI|artificial intelligence) (regulat\w+|legislation|governance)|safety (testing|evaluations?|standards|institutes?|commitments)|catastrophic risks?|loss of control|existential risks?|Global Digital Compact|Hiroshima (AI )?Process|Bletchley|AI (Action|Impact|Safety|Seoul|Paris|Bletchley) Summit|International AI Safety Report|executive order on AI|SB ?53|RAISE Act|Council of Europe|OECD AI)\b", re.I)
PLACE_RULES = [("China", RX_CN), ("US", RX_US), ("UK", RX_UK), ("India", RX_IN)]

# Company blogs, press-release wires and investor-hype outlets are excluded. Google News links hide the real
# domain, so those are matched by publisher name.
BLOCKED_HOSTS = ("openai.com", "anthropic.com", "blog.google", "deepmind.google", "blogs.microsoft.com", "ai.meta.com",
                 "x.ai", "blogs.nvidia.com", "blog.samaltman.com", "microsoft.ai", "venturebeat.com", "techcrunch.com",
                 "wired.com", "theverge.com", "prnewswire.com", "businesswire.com", "globenewswire.com")
BLOCKED_PUBLISHERS = {p.lower() for p in (
    "Stock Titan", "Simply Wall St", "Simply Wall Street", "Benzinga", "MarketBeat", "TipRanks", "PR Newswire",
    "Business Wire", "GlobeNewswire", "EIN Presswire", "ACCESS Newswire", "Newsfile", "openPR", "Markets Insider",
    "markets.businessinsider.com", "The Motley Fool", "Seeking Alpha", "InvestorPlace", "24/7 Wall St.", "eWeek",
    "Florida National News", "Morningstar", "Investing.com", "Zacks", "Barchart", "Yahoo Finance", "Finimize",
    "GuruFocus", "Insider Monkey", "Nasdaq", "TechRadar", "ZDNET", "PCMag", "CNET", "Gadgets 360", "Stocktwits",
    "TradingView", "Tom's Hardware", "Simply Wall St.", "Investopedia", "StockStory", "Money Morning", "Kiplinger",
)}
TITLE_BLOCK = re.compile(r"\b(smartphones?|Snapdragon|iPhone|Galaxy S?\d*|Pixel \d|OnePlus|iQOO|Realme|Redmi|Motorola|price in India|specifications?|unboxing|hands-on)\b|^\s*(sponsored|advertorial|partner content|press release)\b|\b(webinar|register now|price target|buy rating|analyst rating|should you buy|stock picks?|earnings preview|best AI (tools|stocks)|stocks? (poised|to buy|to watch))\b", re.I)

SUB_RULES = [
    ("Protests & opposition", re.compile(r"\b(protest\w*|oppos\w*|resident\w*|moratori\w*|lawsuit\w*|sued|sues|petition\w*|rezon\w*|backlash|activist\w*|bans?|banned|reject\w*|pushback|push(ing)? back|fight\w*|grassroots|community group\w*|object\w*|halt\w*|controvers\w*)\b", re.I)),
    ("Energy & water", re.compile(r"\b(water|electric\w*|energy|power|grid|emission\w*|gas|nuclear|megawatt\w*|gigawatt\w*|MW|GW|utility|utilities|cooling|drought|carbon)\b", re.I)),
    ("Local economy", re.compile(r"\b(jobs?|tax\w*|incentive\w*|subsid\w*|econom\w*|suppliers?|wages?|employment|livelihood\w*|abatement\w*|property values?|local (business|revenue)|revenue)\b", re.I)),
]


def dc_sub(title, desc):
    text = f"{title} {desc}"
    for name, rx in SUB_RULES:
        if rx.search(text):
            return name
    return "Where they're going up"


def passes(f, text):
    if not f:
        return True
    if f == 1:
        return bool(AI_RE.search(text))
    if f == 2:
        return bool(DC_RE.search(text))
    return bool(AI_RE.search(text) or SC_RE.search(text))


def tabs_for(src, title, desc):
    text = f"{title} {desc}"
    tabs = set(src.get("hint", [])) - {"Data centres"}
    if RX_SC.search(text):
        tabs.add("AI supply chain")
    if RX_DC.search(text):
        tabs.add("Data centres")
    if RX_SAF.search(text):
        tabs.add("AI safety")
    for name, rx in PLACE_RULES:
        if rx.search(text):
            tabs.add(name)
    return [t for t in TABS if t in tabs]


def strip_tags(s):
    s = re.sub(r"<[^>]+>", " ", s or "")
    return re.sub(r"\s+", " ", html.unescape(s)).strip()


def parse_date(s):
    if not s:
        return None
    s = s.strip()
    try:
        d = email.utils.parsedate_to_datetime(s)
        if d.tzinfo is None:
            d = d.replace(tzinfo=timezone.utc)
        return d.astimezone(timezone.utc)
    except Exception:
        pass
    try:
        d = datetime.fromisoformat(s.replace("Z", "+00:00"))
        if d.tzinfo is None:
            d = d.replace(tzinfo=timezone.utc)
        return d.astimezone(timezone.utc)
    except Exception:
        return None


def local(tag):
    return tag.rsplit("}", 1)[-1]


def child_text(el, *names):
    for c in el:
        if local(c.tag) in names and (c.text or "").strip():
            return c.text.strip()
    return ""


def parse_feed(xml_bytes):
    root = ET.fromstring(xml_bytes)
    items = []
    for el in root.iter():
        if local(el.tag) not in ("item", "entry"):
            continue
        title = strip_tags(child_text(el, "title"))
        link = child_text(el, "link")
        if not link:
            for c in el:
                if local(c.tag) == "link" and c.get("href") and c.get("rel") in (None, "alternate"):
                    link = c.get("href")
                    break
        desc = strip_tags(child_text(el, "description", "summary", "content", "encoded"))[:240]
        date = parse_date(child_text(el, "pubDate", "published", "updated", "date"))
        pub = ""
        for c in el:
            if local(c.tag) == "source" and (c.text or "").strip():
                pub = c.text.strip()
        items.append({"title": title, "link": link, "desc": desc, "date": date, "pub": pub})
    return items


class _Redirect(urllib.request.HTTPRedirectHandler):
    """Python 3.9's urllib doesn't follow HTTP 308; treat it like 301."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if code == 308:
            code = 301
        return super().redirect_request(req, fp, code, msg, headers, newurl)

    http_error_308 = urllib.request.HTTPRedirectHandler.http_error_302


_OPENER = urllib.request.build_opener(_Redirect)


def fetch(src):
    req = urllib.request.Request(src["url"], headers={"User-Agent": UA, "Accept": "application/rss+xml, application/atom+xml, application/xml, text/xml, */*"})
    with _OPENER.open(req, timeout=TIMEOUT) as r:
        return r.read()


def process(src):
    status = {"name": src["name"], "ok": False, "count": 0, "error": ""}
    try:
        items = parse_feed(fetch(src))
    except Exception as e:  # network error, HTTP error or unparseable feed
        status["error"] = str(e)[:120]
        return status, []
    is_gn = "news.google.com" in src["url"]
    cutoff = datetime.now(timezone.utc) - timedelta(days=MAX_AGE_DAYS)
    out = []
    for it in items[: MAX_PER_FEED * 4]:
        title, link = it["title"], it["link"]
        if not title or not link:
            continue
        source_name = src["name"]
        desc = it["desc"]
        if is_gn:
            # Google News titles end with " - Publisher"; show the real publisher
            pub = it["pub"]
            if pub and title.endswith(" - " + pub):
                title = title[: -(len(pub) + 3)]
            source_name = pub or src["name"]
            desc = ""
        if any(h in link for h in BLOCKED_HOSTS):
            continue
        if source_name.lower() in BLOCKED_PUBLISHERS or TITLE_BLOCK.search(title):
            continue
        if it["date"] and it["date"] < cutoff:
            continue
        if not passes(src.get("f"), f"{title} {desc}"):
            continue
        tabs = tabs_for(src, title, desc)
        if not tabs:
            continue  # not about any of our tabs
        rec = {"title": title, "link": link, "desc": desc[:180], "date": it["date"].isoformat(timespec="minutes") if it["date"] else None,
               "source": source_name, "tabs": tabs}
        if "Data centres" in tabs:
            rec["sub"] = dc_sub(title, desc)
        out.append(rec)
        if len(out) >= MAX_PER_FEED:
            break
    status.update(ok=True, count=len(out))
    return status, out


LOCALES = {"US": "hl=en-US&gl=US&ceid=US:en", "IN": "hl=en-IN&gl=IN&ceid=IN:en", "GB": "hl=en-GB&gl=GB&ceid=GB:en"}


def main():
    sources = json.load(open(os.path.join(HERE, "sources.json"), encoding="utf-8"))
    for s in sources:  # Google News searches are stored as plain queries
        if "gn" in s:
            s["url"] = "https://news.google.com/rss/search?q=" + urllib.parse.quote(s["gn"], safe="") + "&" + LOCALES[s.get("loc", "US")]
    results, statuses = [], []
    with cf.ThreadPoolExecutor(max_workers=8) as ex:
        for st, items in ex.map(process, sources):
            statuses.append(st)
            results.extend(items)

    seen, merged = set(), []
    for it in sorted(results, key=lambda x: x["date"] or "", reverse=True):
        key = it["link"].lower()
        tkey = "t:" + re.sub(r"\W+", " ", it["title"].lower())[:70]
        if key in seen or tkey in seen:
            continue
        seen.add(key)
        seen.add(tkey)
        merged.append(it)

    payload = {
        "generated": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "sources_ok": sum(1 for s in statuses if s["ok"]),
        "sources_total": len(statuses),
        "items": merged,
    }
    with open(os.path.join(HERE, "news.json"), "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, separators=(",", ":"))

    print(f"{len(merged)} stories · {payload['sources_ok']}/{payload['sources_total']} sources ok")
    for s in statuses:
        if not s["ok"]:
            print(f"  FAILED  {s['name']:<30} {s['error']}")
    per_tab = {t: sum(1 for it in merged if t in it["tabs"]) for t in TABS}
    print("  per tab:", per_tab)
    if payload["sources_ok"] == 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
