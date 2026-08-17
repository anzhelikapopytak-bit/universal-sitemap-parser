#!/usr/bin/env python3
"""
Universal Analysis Engine V3 CHECKPOINTED

Purpose
-------
Read only pending rows for one PROJECT_ID from Universal Parser Hub,
classify pages using rules supplied by the Control spreadsheet, compare
competitor BRAND/CATEGORY pages with the project's own pages, write visible
project result sheets, cache page analysis, and mark queue rows processed.

Important architecture rule
---------------------------
This file contains NO production GEO/domain/competitor-specific branches.
All site-specific classification/extraction rules arrive in the payload.

Existing repository secret:
    GOOGLE_SERVICE_ACCOUNT_JSON

Expected payload (GZIP + Base64URL JSON), schema_version = 1:
{
  "schema_version": 1,
  "run_id": "AN_FR_...",
  "project_id": "FR",
  "hub_spreadsheet_id": "...",
  "control_spreadsheet_id": "...",
  "sources": [
    {
      "project_id": "FR",
      "geo": "FR",
      "source_id": "FR_JEUX_CA",
      "role": "competitor",
      "enabled": true,
      "site_url": "https://jeux.ca",
      "sitemap_url": "https://jeux.ca/sitemap_index.xml",

      "brand_url_patterns":
        "suffix:-casino|footprint:brand-banner-bonus-text",

      "brand_extraction_rule":
        "url-tail",

      "bonus_footprint":
        "data-testid:brand-banner-bonus-text|"
        "data-testid:brand-banner-additional-bonus",

      "category_url_patterns":
        "path:/bonus/|h1-regex:(bonus|casino)",

      "affiliate_network": "",
      "ref_rule": ""
    }
  ],
  "engine": {
    "timeout_seconds": 25,
    "retries": 3,
    "retry_backoff_seconds": 1.5,
    "max_workers": 12,
    "user_agent": "Mozilla/5.0 ..."
  }
}

Rule DSL
--------
OR groups use:
    |

AND inside one group uses:
    &&

Supported match tokens:
    suffix:TEXT
    prefix:TEXT
    contains:TEXT
    path:TEXT
    source-sitemap:TEXT
    footprint:TEXT
    h1:TEXT
    regex-url:REGEX
    regex-html:REGEX
    h1-regex:REGEX

A bare token beginning with "/" is treated as path:.
Any other bare token is treated as contains:.

Example:
    path:/casinos/&&footprint:casino-head__bonus

Extraction DSL
--------------
Brand Extraction Rule is a priority list separated by "|":
    attr:data-product|attr:data-brand|url-tail
    url-after:/casinos-en-ligne/|url-tail
    h1|url-tail

Bonus Footprint is a priority/combination list:
    attr:data-offer
    class:bonus-title|generic
    data-testid:brand-banner-bonus-text|data-testid:brand-banner-additional-bonus

Ref Rule:
    attr:data-affiliate-url
    href-regex:/go/|/visit/|ref=|aff
If blank, the engine uses a generic affiliate-link heuristic.
"""

from __future__ import annotations

import base64
import concurrent.futures
import gzip
import html as html_lib
import json
import os
import random
import re
import ssl
import sys
import time
import traceback
import unicodedata
from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple
from urllib.parse import urljoin, urlsplit, unquote

import requests
from google.oauth2 import service_account
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError


SCHEMA_VERSION = 1

QUEUE_SHEET = "_GP_URL_QUEUE"
CACHE_SHEET = "_GP_ANALYSIS_CACHE"
ANALYSIS_RUNS_SHEET = "_GP_ANALYSIS_RUNS"

# Enrichment-only circuit breaker. If one host repeatedly rejects optional
# Bonus/ref_link fetches with HTTP 403, stop enrichment for that host for the
# rest of the current run. BRAND/CATEGORY classification is never affected.
ENRICHMENT_403_DISABLE_THRESHOLD = 50

QUEUE_REQUIRED_HEADERS = [
    "Run ID",
    "Exported At",
    "Project ID",
    "GEO",
    "Source ID",
    "Site URL",
    "Role",
    "URL",
    "Last Modified",
    "Source Sitemap",
    "Processed",
    "Analysis Run ID",
]

CACHE_HEADERS = [
    "Project ID",
    "GEO",
    "Source ID",
    "Site URL",
    "Role",
    "URL",
    "Last Modified",
    "Source Sitemap",
    "Detected Type",
    "Brand",
    "Brand Key",
    "Category Key",
    "URL Key",
    "H1",
    "H1 Key",
    "Bonus",
    "Ref Link",
    "Analyzed At",
    "Analysis Run ID",
    "Error",
]

ANALYSIS_RUN_HEADERS = [
    "Run ID",
    "Project ID",
    "Phase",
    "Pending At Start",
    "Processed",
    "Brands",
    "Categories",
    "Missing Brands",
    "Missing Categories",
    "Errors",
    "Started At",
    "Updated At",
    "Finished At",
    "Message",
]

MAIN_BRANDS_HEADERS = [
    "Our URL",
    "Our Last Modified",
    "Our Parsing Date",
    "Our Brand Name",
    "Our Page Type",
    "Competitor",
    "Competitor URL",
    "Last Modified",
    "Parsing Date",
    "Page Type",
    "MATCH / MISSING",
    "Brand Name",
    "Bonus",
    "SEO Comment",
]

MISSING_BRANDS_HEADERS = [
    "URL",
    "BRAND",
    "Bonus",
    "ref_link",
    "Affiliate Comment",
    "Affiliate Network",
    "SEO content",
    "Comments",
]

CATEGORIES_HEADERS = [
    "Our URL",
    "Page type",
    "Competitor URL",
    "Competitor",
    "Status - MATCH / MISSING",
    "Parsing date",
    "SEO comment",
]

MISSING_CATEGORIES_HEADERS = [
    "Date",
    "URL",
    "Top keywords",
    "Search volume",
    "Seo comment",
    "Competitor",
    "Page type",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def safe_text(value: object) -> str:
    return "" if value is None else str(value).strip()


def decode_payload(value: str) -> dict:
    raw = safe_text(value)
    if not raw:
        raise ValueError("PARSER_PAYLOAD_GZIP_B64 is empty.")

    padding = "=" * ((4 - len(raw) % 4) % 4)
    compressed = base64.urlsafe_b64decode((raw + padding).encode("ascii"))
    decoded = gzip.decompress(compressed).decode("utf-8")
    payload = json.loads(decoded)

    if int(payload.get("schema_version", 0)) != SCHEMA_VERSION:
        raise ValueError(
            f"Unsupported analysis payload schema_version={payload.get('schema_version')!r}; "
            f"expected {SCHEMA_VERSION}."
        )

    return payload


def normalize_space(value: str) -> str:
    return re.sub(r"\s+", " ", safe_text(value)).strip()


def strip_tags(raw: str) -> str:
    text = re.sub(r"(?is)<script\b[^>]*>.*?</script\s*>", " ", raw or "")
    text = re.sub(r"(?is)<style\b[^>]*>.*?</style\s*>", " ", text)
    text = re.sub(r"(?is)<[^>]+>", " ", text)
    return normalize_space(html_lib.unescape(text))


def extract_h1(raw: str) -> str:
    match = re.search(r"(?is)<h1\b[^>]*>(.*?)</h1\s*>", raw or "")
    return strip_tags(match.group(1)) if match else ""


def path_of(url: str) -> str:
    try:
        return unquote(urlsplit(url).path or "/")
    except Exception:
        return ""


def host_of(url: str) -> str:
    try:
        host = (urlsplit(url).hostname or "").lower()
    except Exception:
        host = ""
    return host[4:] if host.startswith("www.") else host


def is_http_403_error(message: str) -> bool:
    return bool(re.search(r"\bHTTP\s+403\b", safe_text(message), flags=re.I))


def is_non_content_url(url: str) -> bool:
    u = safe_text(url).lower()
    path = path_of(u).lower()

    bad_parts = (
        "/tag/",
        "/author/",
        "/feed",
        "/wp-json/",
        "/privacy",
        "/terms",
        "/cookies",
        "/contact",
    )
    if any(x in path for x in bad_parts):
        return True

    bad_ext = (
        ".jpg", ".jpeg", ".png", ".webp", ".gif", ".svg", ".pdf",
        ".zip", ".css", ".js", ".xml", ".xml.gz",
    )
    return path.endswith(bad_ext)


def ascii_fold(value: str) -> str:
    value = unicodedata.normalize("NFKD", safe_text(value))
    return "".join(ch for ch in value if not unicodedata.combining(ch))


def generic_key(value: str) -> str:
    s = ascii_fold(html_lib.unescape(safe_text(value))).lower()
    s = re.sub(r"\b20\d{2}\b", " ", s)
    s = s.replace("&", " and ")
    s = re.sub(r"[^a-z0-9]+", " ", s)
    weak = {
        "the", "a", "an", "and", "or", "of", "for", "to", "in", "on",
        "with", "guide", "review", "reviews", "avis", "casino", "casinos",
        "online", "site", "sites", "best", "top",
    }
    tokens = [x for x in s.split() if x not in weak]
    return "".join(tokens)


def clean_brand_display(value: str) -> str:
    raw = html_lib.unescape(unquote(safe_text(value)))
    raw = re.sub(r"\.html?$", "", raw, flags=re.I)
    raw = raw.replace("_", "-").replace("+", "-")
    raw = re.sub(r"-+", "-", raw).strip("- ")

    suffixes = (
        "-casino-en-ligne",
        "-casino-review",
        "-casino-reviews",
        "-casino-avis",
        "-review",
        "-reviews",
        "-avis",
        "-bonus",
        "-casino",
    )
    low = raw.lower()
    for suffix in suffixes:
        if low.endswith(suffix):
            raw = raw[: -len(suffix)]
            low = raw.lower()

    raw = re.sub(r"[-_]+", " ", raw)
    raw = normalize_space(raw)
    return " ".join(part.capitalize() if not part.isupper() else part for part in raw.split())


def brand_key(value: str) -> str:
    s = ascii_fold(safe_text(value)).lower()
    s = s.replace("&", "and")
    s = re.sub(r"[\s_-]+", "", s)

    # Generic suffix cleanup only; no GEO/domain branching.
    for suffix in ("casino", "bonus", "avis", "review", "reviews", "online"):
        if len(s) > len(suffix) + 2 and s.endswith(suffix):
            s = s[: -len(suffix)]

    return re.sub(r"[^a-z0-9]", "", s)


def url_tail(url: str) -> str:
    parts = [x for x in path_of(url).split("/") if x]
    return parts[-1] if parts else ""


def url_key(url: str) -> str:
    return generic_key(url_tail(url))


def split_or(rule: str) -> List[str]:
    """
    Split DSL OR groups on top-level "|" only.

    This preserves regex alternation inside parentheses, e.g.
        h1-regex:(bonus|casino)
    while still allowing:
        suffix:-casino|footprint:bonus-box
    """
    raw = safe_text(rule)
    if not raw:
        return []

    out: List[str] = []
    buf: List[str] = []
    paren_depth = 0
    in_class = False
    escaped = False

    for ch in raw:
        if escaped:
            buf.append(ch)
            escaped = False
            continue

        if ch == "\\":
            buf.append(ch)
            escaped = True
            continue

        if ch == "[" and not in_class:
            in_class = True
            buf.append(ch)
            continue

        if ch == "]" and in_class:
            in_class = False
            buf.append(ch)
            continue

        if not in_class:
            if ch == "(":
                paren_depth += 1
                buf.append(ch)
                continue

            if ch == ")" and paren_depth > 0:
                paren_depth -= 1
                buf.append(ch)
                continue

            if ch == "|" and paren_depth == 0:
                item = "".join(buf).strip()
                if item:
                    out.append(item)
                buf = []
                continue

        buf.append(ch)

    item = "".join(buf).strip()
    if item:
        out.append(item)

    return out


def rule_needs_html(rule: str) -> bool:
    low = safe_text(rule).lower()
    return any(
        token in low
        for token in ("footprint:", "h1:", "regex-html:", "h1-regex:")
    )


@dataclass(frozen=True)
class SourceConfig:
    project_id: str
    geo: str
    source_id: str
    role: str
    enabled: bool
    site_url: str
    sitemap_url: str
    brand_url_patterns: str
    brand_extraction_rule: str
    bonus_footprint: str
    category_url_patterns: str
    affiliate_network: str
    ref_rule: str

    @staticmethod
    def from_dict(data: dict, default_project_id: str) -> "SourceConfig":
        return SourceConfig(
            project_id=safe_text(data.get("project_id") or default_project_id),
            geo=safe_text(data.get("geo")),
            source_id=safe_text(data.get("source_id")),
            role=safe_text(data.get("role") or "competitor").lower(),
            enabled=bool(data.get("enabled", True)),
            site_url=safe_text(data.get("site_url")),
            sitemap_url=safe_text(data.get("sitemap_url")),
            brand_url_patterns=safe_text(data.get("brand_url_patterns")),
            brand_extraction_rule=safe_text(data.get("brand_extraction_rule")),
            bonus_footprint=safe_text(data.get("bonus_footprint")),
            category_url_patterns=safe_text(data.get("category_url_patterns")),
            affiliate_network=safe_text(data.get("affiliate_network")),
            ref_rule=safe_text(data.get("ref_rule")),
        )


@dataclass(frozen=True)
class QueueRow:
    sheet_row: int
    export_run_id: str
    exported_at: str
    project_id: str
    geo: str
    source_id: str
    site_url: str
    role: str
    url: str
    last_modified: str
    source_sitemap: str
    processed: str
    analysis_run_id: str


@dataclass
class AnalysisResult:
    queue: QueueRow
    source: SourceConfig
    detected_type: str = "OTHER"
    brand: str = ""
    brand_key: str = ""
    category_key: str = ""
    url_key: str = ""
    h1: str = ""
    h1_key: str = ""
    bonus: str = ""
    ref_link: str = ""
    analyzed_at: str = ""
    error: str = ""

    def cache_row(self, run_id: str) -> List[object]:
        return [
            self.queue.project_id,
            self.queue.geo,
            self.queue.source_id,
            self.queue.site_url,
            self.queue.role,
            self.queue.url,
            self.queue.last_modified,
            self.queue.source_sitemap,
            self.detected_type,
            self.brand,
            self.brand_key,
            self.category_key,
            self.url_key,
            self.h1,
            self.h1_key,
            self.bonus,
            self.ref_link,
            self.analyzed_at,
            run_id,
            self.error,
        ]


class HttpFetcher:
    def __init__(
        self,
        timeout_seconds: int = 25,
        retries: int = 3,
        retry_backoff_seconds: float = 1.5,
        user_agent: str = "Mozilla/5.0 (compatible; UniversalAnalysisEngine/1.0)",
    ):
        self.timeout = max(5, int(timeout_seconds))
        self.retries = max(1, int(retries))
        self.backoff = max(0.1, float(retry_backoff_seconds))
        self.user_agent = user_agent
        self._local = {}

    def _session(self) -> requests.Session:
        # One session per worker thread.
        import threading
        tid = threading.get_ident()
        if tid not in self._local:
            session = requests.Session()
            session.headers.update(
                {
                    "User-Agent": self.user_agent,
                    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                    "Accept-Language": "*",
                    "Cache-Control": "no-cache",
                }
            )
            self._local[tid] = session
        return self._local[tid]

    def fetch_text(self, url: str) -> str:
        last_error: Optional[Exception] = None

        for attempt in range(1, self.retries + 1):
            try:
                response = self._session().get(
                    url,
                    timeout=self.timeout,
                    allow_redirects=True,
                )

                if response.status_code >= 400:
                    raise requests.HTTPError(
                        f"HTTP {response.status_code} for {url}"
                    )

                response.encoding = response.encoding or response.apparent_encoding or "utf-8"
                return response.text

            except Exception as exc:
                last_error = exc
                if attempt < self.retries:
                    time.sleep(self.backoff * attempt)

        raise RuntimeError(str(last_error) if last_error else f"Fetch failed: {url}")


class PageContext:
    def __init__(self, row: QueueRow, fetcher: HttpFetcher):
        self.row = row
        self.fetcher = fetcher
        self._html: Optional[str] = None
        self._h1: Optional[str] = None
        self.fetch_attempted = False
        self.fetch_error = ""

    @property
    def url(self) -> str:
        return self.row.url

    @property
    def path(self) -> str:
        return path_of(self.row.url)

    @property
    def source_sitemap(self) -> str:
        return self.row.source_sitemap

    def html(self) -> str:
        if self._html is not None:
            return self._html

        self.fetch_attempted = True
        try:
            self._html = self.fetcher.fetch_text(self.row.url)
        except Exception as exc:
            self.fetch_error = safe_text(exc)
            self._html = ""
        return self._html

    def h1(self) -> str:
        if self._h1 is not None:
            return self._h1
        self._h1 = extract_h1(self.html())
        return self._h1


def slug_of(url: str) -> str:
    slug = url_tail(url)
    return re.sub(r"\.(?:html?|php|aspx?)$", "", slug, flags=re.I)


def normalize_footprint_text(value: str) -> str:
    s = ascii_fold(html_lib.unescape(safe_text(value))).lower()
    s = re.sub(r"\s+", " ", s).strip()
    return s


def footprint_matches(raw_html: str, footprint_spec: str) -> bool:
    raw = normalize_footprint_text(raw_html)
    compact = re.sub(r"\s*=\s*", "=", raw.replace('"', "").replace("'", ""))
    spec = normalize_footprint_text(footprint_spec)
    spec = re.sub(r"\s*=\s*", "=", spec.replace('"', "").replace("'", "")).strip()
    if not spec:
        return False
    tokens = [x for x in spec.split() if x]
    return bool(tokens) and all(token in raw or token in compact for token in tokens)


def match_rule_token(token: str, ctx: PageContext) -> bool:
    token = safe_text(token)
    if not token:
        return False

    lower = token.lower()

    # Generic rule negation. Example:
    #   not:slug-regex:^(bonus|guide)
    if lower.startswith("not:"):
        return not match_rule_token(token[4:].strip(), ctx)

    url_lower = ctx.url.lower()
    path_lower = ctx.path.lower()
    source_lower = ctx.source_sitemap.lower()
    slug = slug_of(ctx.url)
    slug_lower = slug.lower()

    if lower.startswith("suffix:"):
        needle = token.split(":", 1)[1].strip().lower()
        p = path_lower.rstrip("/")
        n = needle.rstrip("/")
        return bool(n) and p.endswith(n)

    if lower.startswith("prefix:"):
        needle = token.split(":", 1)[1].strip().lower()
        return bool(needle) and slug_lower.startswith(needle)

    if lower.startswith("contains:"):
        needle = token.split(":", 1)[1].strip().lower()
        return bool(needle) and needle in url_lower

    if lower.startswith("path:"):
        needle = token.split(":", 1)[1].strip().lower()
        return bool(needle) and needle in path_lower

    if lower.startswith("source-sitemap:"):
        needle = token.split(":", 1)[1].strip().lower()
        return bool(needle) and needle in source_lower

    if lower.startswith("footprint:"):
        spec = token.split(":", 1)[1].strip()
        return bool(spec) and footprint_matches(ctx.html(), spec)

    if lower.startswith("h1:"):
        needle = token.split(":", 1)[1].strip().lower()
        return bool(needle) and needle in ctx.h1().lower()

    if lower.startswith("regex-url:"):
        pattern = token.split(":", 1)[1].strip()
        return bool(pattern) and bool(re.search(pattern, ctx.url, flags=re.I))

    if lower.startswith("path-regex:"):
        pattern = token.split(":", 1)[1].strip()
        return bool(pattern) and bool(re.search(pattern, ctx.path, flags=re.I))

    if lower.startswith("slug-regex:"):
        pattern = token.split(":", 1)[1].strip()
        return bool(pattern) and bool(re.search(pattern, slug, flags=re.I))

    if lower.startswith("regex-html:"):
        pattern = token.split(":", 1)[1].strip()
        return bool(pattern) and bool(re.search(pattern, ctx.html(), flags=re.I | re.S))

    if lower.startswith("h1-regex:"):
        pattern = token.split(":", 1)[1].strip()
        return bool(pattern) and bool(re.search(pattern, ctx.h1(), flags=re.I))

    if token.startswith("/"):
        return token.lower() in path_lower

    return token.lower() in url_lower


def matches_rule(rule: str, ctx: PageContext) -> bool:
    raw = safe_text(rule)
    if not raw:
        return False

    for or_group in split_or(raw):
        and_tokens = [x.strip() for x in or_group.split("&&") if x.strip()]
        if and_tokens and all(match_rule_token(token, ctx) for token in and_tokens):
            return True

    return False


def extract_attr(raw: str, name: str) -> str:
    if not raw or not name:
        return ""
    pattern = re.compile(
        rf"""{re.escape(name)}\s*=\s*(["'])(.*?)\1""",
        flags=re.I | re.S,
    )
    match = pattern.search(raw)
    return html_lib.unescape(match.group(2)).strip() if match else ""


def extract_text_by_class_contains(raw: str, token: str) -> str:
    if not raw or not token:
        return ""

    tag_re = re.compile(
        r"""<([a-z0-9]+)\b[^>]*class=(["'])(.*?)\2[^>]*>(.*?)</\1\s*>""",
        flags=re.I | re.S,
    )
    target = token.lower()

    for match in tag_re.finditer(raw):
        classes = match.group(3).lower()
        if target in classes:
            text = strip_tags(match.group(4))
            if text:
                return text
    return ""


def extract_text_by_data_testid(raw: str, test_id: str) -> str:
    if not raw or not test_id:
        return ""

    pattern = re.compile(
        rf"""<([a-z0-9]+)\b[^>]*data-testid=(["']){re.escape(test_id)}\2[^>]*>(.*?)</\1\s*>""",
        flags=re.I | re.S,
    )
    match = pattern.search(raw)
    return strip_tags(match.group(3)) if match else ""


def normalize_brand_slug(value: str) -> str:
    s = ascii_fold(safe_text(value)).lower()
    return re.sub(r"[^a-z0-9]+", "-", s).strip("-")


def add_brand_to_lexicon(lexicon: Dict[str, dict], brand: str) -> None:
    key = brand_key(brand)
    slug = normalize_brand_slug(brand)
    if not key or not slug:
        return
    current = lexicon.get(key)
    if current is None or len(slug) > len(current.get("slug", "")):
        lexicon[key] = {"brand": safe_text(brand), "key": key, "slug": slug}


def find_brand_in_lexicon_tail(slug: str, lexicon: Optional[Dict[str, dict]]) -> str:
    if not lexicon:
        return ""
    haystack = "-" + re.sub(r"[^a-z0-9]+", "-", ascii_fold(slug).lower()).strip("-") + "-"
    best: Optional[dict] = None
    for item in lexicon.values():
        item_slug = safe_text(item.get("slug"))
        if not item_slug:
            continue
        needle = "-" + item_slug + "-"
        if not haystack.endswith(needle):
            continue
        if best is None or len(item_slug) > len(safe_text(best.get("slug"))):
            best = item
    return safe_text(best.get("brand")) if best else ""


def normalize_generic_brand_name(value: str) -> str:
    s = ascii_fold(safe_text(value)).lower()
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return normalize_space(s)


def is_generic_promo_brand(value: str) -> bool:
    s = normalize_generic_brand_name(value)
    if not s:
        return True

    exact = {
        "bonus", "casino", "casinos", "promotion", "promo", "tournoi",
        "bienvenue", "accueil", "paiements", "retraits", "rewards",
        "live", "strategie", "fournisseurs", "machines a sous",
        "depot minimum", "sans depot", "pour mobile",
        "sans verification identite", "sans inscription",
        "realite virtuelle", "top 10 des casinos en ligne",
        "qui paient le mieux", "a paiement rapide", "comptes rendus de",
        "keno en ligne", "sites de machines a sous",
        "notre systeme evaluation", "celebrites jeux",
        "adaptations du jeu video en salles de casino",
        "deal or no deal", "diamond", "le", "la", "les", "un", "une",
        "site", "jeu", "jeux", "online", "en ligne",
    }
    if s in exact:
        return True

    if len(s.split()) > 5:
        return True

    if re.search(
        r"^(?:bonus|promotion|promo|tournoi|pack|site|jeux du site|"
        r"meilleurs jeux du site|cascade de cash|monday motivation|octobre|"
        r"bienvenue de|exclusifs du programme)",
        s,
        flags=re.I,
    ):
        return True

    if re.search(
        r"(?: depot minimum| machines a sous| methode de retrait| bonus et revue)$",
        s,
        flags=re.I,
    ):
        return True

    return False


def clean_promo_brand_candidate(value: str) -> str:
    s = safe_text(value)
    s = re.sub(r"\.(?:html?|php|aspx?)$", "", s, flags=re.I)
    s = re.sub(r"^(?:le-|la-|les-)", "", s, flags=re.I)
    s = re.sub(
        r"^(?:bonus|promotion|tournoi|offre|code-promo)-",
        "",
        s,
        flags=re.I,
    )
    s = re.sub(
        r"-(?:bonus|promotion|tournoi|offre)$",
        "",
        s,
        flags=re.I,
    )
    s = s.strip("-_")

    normalized = normalize_space(re.sub(r"[-_]+", " ", s))
    if not normalized or is_generic_promo_brand(normalized):
        return ""
    return s


def trim_promo_words(value: str) -> str:
    s = safe_text(value).strip("-_")
    previous = None

    while s and s != previous:
        previous = s
        s = re.sub(
            r"^(?:site|pack|bienvenue|bonus|promo|promotion|cashback|"
            r"fidelite|ludotheque|octobre|oktoberfest|septembre|novembre|"
            r"decembre|monday|friday|weekend)-+",
            "",
            s,
            flags=re.I,
        )
        s = s.strip("-_")

    return s


def is_weak_brand_token(value: str) -> bool:
    s = normalize_generic_brand_name(value)
    weak = {
        "bonus", "casino", "casinos", "promotion", "promo", "tournoi",
        "bienvenue", "accueil", "site", "jeux", "jeu", "online",
        "en ligne", "le", "la", "les", "un", "une",
    }
    return not s or s in weak


def extract_after_last_connector(value: str) -> str:
    source = safe_text(value).lower()
    connectors = [
        "-en-exclusivite-sur-le-site-",
        "-en-exclusivite-sur-",
        "-sur-le-site-",
        "-sur-",
        "-chez-",
        "-avec-le-site-",
        "-avec-la-",
        "-avec-le-",
        "-avec-",
        "-pour-le-site-",
        "-pour-la-",
        "-pour-le-",
        "-pour-",
        "-du-site-",
        "-site-",
        "-offerts-par-",
        "-offert-par-",
        "-par-",
        "-au-",
        "-aux-",
        "-de-",
    ]

    best_index = -1
    best_connector = ""
    for connector in connectors:
        idx = source.rfind(connector)
        if idx > best_index:
            best_index = idx
            best_connector = connector

    if best_index == -1:
        return ""

    return source[best_index + len(best_connector):].strip("-_")


def extract_simple_promo_brand(slug: str) -> str:
    s = safe_text(slug)
    s = re.sub(r"\.(?:html?|php|aspx?)$", "", s, flags=re.I)
    s = re.sub(r"-casino(?:-en-ligne)?$", "", s, flags=re.I)
    s = re.sub(r"-casinos$", "", s, flags=re.I)
    s = s.strip("-_")

    if not s:
        return ""

    tokens = [x for x in s.split("-") if x]
    if len(tokens) > 3:
        return ""

    candidate = clean_promo_brand_candidate(s)
    if not candidate or is_generic_promo_brand(candidate.replace("-", " ")):
        return ""

    return candidate


def extract_promo_tail_brand(
    slug: str,
    lexicon: Optional[Dict[str, dict]] = None,
) -> str:
    """
    Generic extraction strategy for promotion/news URLs whose final phrase is
    the brand before a -casino suffix. It mirrors the proven old FR parser
    behavior, but is selected by Config rather than by domain name.
    """
    original = safe_text(slug)
    s = re.sub(r"-casino(?:-en-ligne)?$", "", original, flags=re.I)
    s = re.sub(r"-casinos$", "", s, flags=re.I)
    s = s.strip("-_")

    if not s:
        return ""

    strong = extract_after_last_connector(s)
    if strong:
        candidate = trim_promo_words(clean_promo_brand_candidate(strong))
        if (
            candidate
            and len([x for x in candidate.split("-") if x]) <= 4
            and not is_generic_promo_brand(candidate.replace("-", " "))
        ):
            return candidate

    # Short, clean <brand>-casino slugs are safer than a shorter lexicon tail
    # (e.g. Rocket Spin must not collapse to Spin).
    simple = extract_simple_promo_brand(original)
    if simple:
        return simple

    lexicon_match = find_brand_in_lexicon_tail(s, lexicon)
    if lexicon_match:
        return normalize_brand_slug(lexicon_match)

    match = re.search(
        r"-(?:bonus|promotion|promo|tournoi)-(?:de-|du-|des-)?([a-z0-9-]+)$",
        s,
        flags=re.I,
    )
    if match:
        candidate = trim_promo_words(clean_promo_brand_candidate(match.group(1)))
        if (
            candidate
            and len([x for x in candidate.split("-") if x]) <= 3
            and not is_generic_promo_brand(candidate.replace("-", " "))
        ):
            return candidate

    if re.search(
        r"(?:bonus|promotion|promo|cashback|tournoi|free-spins|"
        r"tours-gratuits|offert|offerts|bienvenue)",
        s,
        flags=re.I,
    ):
        tokens = [x for x in s.split("-") if x]
        if tokens:
            tail = trim_promo_words(tokens[-1])
            if (
                tail
                and not is_weak_brand_token(tail)
                and not is_generic_promo_brand(tail)
            ):
                return tail

    return ""


def extract_review_directory_brand(slug: str) -> str:
    s = safe_text(slug)
    s = re.sub(r"-casino$", "", s, flags=re.I)
    s = re.sub(r"^casino-", "", s, flags=re.I)
    return clean_promo_brand_candidate(s)


def extract_casinobonus_style_brand(slug: str) -> str:
    s = safe_text(slug)
    for pattern in (
        r"-casino-bonus-et-revue$",
        r"-bonus-et-revue$",
        r"-casino-bonus$",
        r"-casino$",
        r"-bonus$",
    ):
        s = re.sub(pattern, "", s, flags=re.I)

    s = re.sub(r"^avis-(?:sur-)?", "", s, flags=re.I)
    s = re.sub(r"^analyse-(?:de-)?", "", s, flags=re.I)
    return clean_promo_brand_candidate(s)


def extract_review_title_brand(slug: str) -> str:
    s = re.sub(r"-casino$", "", safe_text(slug), flags=re.I)

    prefixes = (
        r"^le-bonus-de-bienvenue-exclusif-",
        r"^le-bonus-de-bienvenue-",
        r"^le-bonus-d-accueil-",
        r"^le-bonus-accueil-",
        r"^bonus-de-bienvenue-exclusif-",
        r"^bonus-de-bienvenue-",
        r"^bonus-d-accueil-",
        r"^bonus-accueil-",
        r"^avis-sur-",
        r"^avis-",
        r"^analyse-de-",
        r"^analyse-",
        r"^casino-",
    )

    for pattern in prefixes:
        if re.search(pattern, s, flags=re.I):
            s = re.sub(pattern, "", s, count=1, flags=re.I)
            break

    return clean_promo_brand_candidate(s)


def format_brand_display(value: str) -> str:
    display = clean_brand_display(value)
    compact = brand_key(display)
    aliases = {
        "888": "888",
        "party": "Party",
        "letslucky": "LetsLucky",
        "quickwin": "QuickWin",
        "playojo": "PlayOJO",
        "jackpotcity": "Jackpot City",
    }
    return aliases.get(compact, display)


def extract_brand(
    ctx: PageContext,
    source: SourceConfig,
    brand_lexicon: Optional[Dict[str, dict]] = None,
) -> str:
    rules = split_or(source.brand_extraction_rule) or ["url-tail"]

    for rule in rules:
        low = rule.lower()
        value = ""

        if low == "url-tail":
            value = url_tail(ctx.url)

        elif low == "profile:promo-tail":
            value = extract_promo_tail_brand(slug_of(ctx.url), brand_lexicon)

        elif low == "profile:review-directory":
            value = extract_review_directory_brand(slug_of(ctx.url))

        elif low == "profile:casinobonus-style":
            value = extract_casinobonus_style_brand(slug_of(ctx.url))

        elif low == "profile:review-title":
            value = extract_review_title_brand(slug_of(ctx.url))

        elif low.startswith("url-after:"):
            segment = rule.split(":", 1)[1].strip().strip("/")
            parts = [x for x in path_of(ctx.url).split("/") if x]
            parts_lower = [x.lower() for x in parts]
            try:
                index = parts_lower.index(segment.lower())
                if index + 1 < len(parts):
                    value = parts[index + 1]
            except ValueError:
                value = ""

        elif low == "h1":
            value = ctx.h1()

        elif low.startswith("attr:"):
            value = extract_attr(ctx.html(), rule.split(":", 1)[1].strip())

        elif low.startswith("class:"):
            value = extract_text_by_class_contains(
                ctx.html(), rule.split(":", 1)[1].strip()
            )

        elif low.startswith("data-testid:"):
            value = extract_text_by_data_testid(
                ctx.html(), rule.split(":", 1)[1].strip()
            )

        elif low.startswith("regex-html:"):
            pattern = rule.split(":", 1)[1].strip()
            match = re.search(pattern, ctx.html(), flags=re.I | re.S)
            if match:
                value = match.group(1) if match.groups() else match.group(0)

        elif low.startswith("regex-url:"):
            pattern = rule.split(":", 1)[1].strip()
            match = re.search(pattern, ctx.url, flags=re.I)
            if match:
                value = match.group(1) if match.groups() else match.group(0)

        value = format_brand_display(value)
        if value and not is_generic_promo_brand(value):
            return value

    return ""


def generic_bonus(raw: str) -> str:
    plain = strip_tags(raw)
    patterns = (
        r"\b\d{1,3}\s*%\s*(?:up\s*to|jusqu[’'`]?a|jusqu[’'`]?à|bonus)?\s*(?:C?\$|€|£)?\s*\d{1,6}(?:[.,]\d{1,2})?(?:\s*\+\s*\d{1,5}\s*(?:free\s*spins?|tours?\s+gratuits?|FS))?",
        r"\b(?:C?\$|€|£)\s*\d{1,6}(?:[.,]\d{1,2})?(?:\s*\+\s*\d{1,5}\s*(?:free\s*spins?|tours?\s+gratuits?|FS))?",
        r"\b\d{1,5}\s*(?:free\s*spins?|tours?\s+gratuits?|FS)\b",
    )

    for pattern in patterns:
        match = re.search(pattern, plain, flags=re.I)
        if match:
            return normalize_space(match.group(0))[:300]

    return ""


def extract_bonus(ctx: PageContext, source: SourceConfig) -> str:
    rule = safe_text(source.bonus_footprint)
    if not rule or rule.lower() == "skip":
        return ""

    collected: List[str] = []

    for token in split_or(rule):
        low = token.lower()
        value = ""

        if low == "generic":
            value = generic_bonus(ctx.html())

        elif low.startswith("attr:"):
            value = extract_attr(ctx.html(), token.split(":", 1)[1].strip())

        elif low.startswith("class:"):
            value = extract_text_by_class_contains(
                ctx.html(), token.split(":", 1)[1].strip()
            )

        elif low.startswith("data-testid:"):
            value = extract_text_by_data_testid(
                ctx.html(), token.split(":", 1)[1].strip()
            )

        elif low.startswith("regex-html:"):
            pattern = token.split(":", 1)[1].strip()
            match = re.search(pattern, ctx.html(), flags=re.I | re.S)
            if match:
                value = match.group(1) if match.groups() else match.group(0)

        # Legacy/unrecognized values get a safe generic fallback.
        else:
            value = generic_bonus(ctx.html())

        value = normalize_space(value)
        if value and value not in collected:
            collected.append(value)

    return normalize_space(" ".join(collected))[:500]


def extract_all_hrefs(raw: str, base_url: str) -> List[str]:
    out: List[str] = []
    seen: Set[str] = set()

    for match in re.finditer(
        r"""(?is)<a\b[^>]*\bhref\s*=\s*(["'])(.*?)\1""",
        raw or "",
    ):
        href = html_lib.unescape(match.group(2)).strip()
        if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
            continue
        absolute = urljoin(base_url, href)
        if absolute not in seen:
            seen.add(absolute)
            out.append(absolute)

    return out


def extract_ref_link(ctx: PageContext, source: SourceConfig) -> str:
    rule = safe_text(source.ref_rule)

    if rule:
        for token in split_or(rule):
            low = token.lower()

            if low.startswith("attr:"):
                value = extract_attr(ctx.html(), token.split(":", 1)[1].strip())
                if value:
                    return urljoin(ctx.url, value)

            if low.startswith("href-regex:"):
                pattern = token.split(":", 1)[1].strip()
                for href in extract_all_hrefs(ctx.html(), ctx.url):
                    if re.search(pattern, href, flags=re.I):
                        return href

            if low.startswith("regex-html:"):
                pattern = token.split(":", 1)[1].strip()
                match = re.search(pattern, ctx.html(), flags=re.I | re.S)
                if match:
                    value = match.group(1) if match.groups() else match.group(0)
                    return urljoin(ctx.url, html_lib.unescape(value))

    priority = re.compile(
        r"(/go/|/visit/|/play/|/out/|/redirect|[?&]ref=|aff(?:iliate)?|click|track)",
        flags=re.I,
    )
    for href in extract_all_hrefs(ctx.html(), ctx.url):
        if priority.search(href):
            return href

    return ""


def category_key_from_context(ctx: PageContext) -> Tuple[str, str, str]:
    h1 = ctx.h1()
    h1_key = generic_key(h1)
    u_key = url_key(ctx.url)
    return (h1_key or u_key, u_key, h1)


def classify_row(
    row: QueueRow,
    source: SourceConfig,
    fetcher: HttpFetcher,
    enrich_missing_brand: bool = False,
    brand_lexicon: Optional[Dict[str, dict]] = None,
) -> AnalysisResult:
    result = AnalysisResult(
        queue=row,
        source=source,
        analyzed_at=utc_now(),
        url_key=url_key(row.url),
    )

    if is_non_content_url(row.url):
        result.detected_type = "OTHER"
        return result

    ctx = PageContext(row, fetcher)

    try:
        if matches_rule(source.brand_url_patterns, ctx):
            result.detected_type = "BRAND"
            result.brand = extract_brand(ctx, source, brand_lexicon)
            result.brand_key = brand_key(result.brand)

            # A URL may satisfy a broad configured brand pattern while the
            # configured extractor correctly rejects it as generic/article-like.
            # Treat that as OTHER, not ERROR, so it is checkpointed once.
            if not result.brand or not result.brand_key:
                result.detected_type = "OTHER"
                result.brand = ""
                result.brand_key = ""
                return result

            if enrich_missing_brand:
                result.bonus = extract_bonus(ctx, source)
                result.ref_link = extract_ref_link(ctx, source)

            if ctx.fetch_error:
                result.error = ctx.fetch_error
            return result

        if matches_rule(source.category_url_patterns, ctx):
            result.detected_type = "CATEGORY"
            cat_key, u_key, h1 = category_key_from_context(ctx)
            result.category_key = cat_key
            result.url_key = u_key
            result.h1 = h1
            result.h1_key = generic_key(h1)

            if not result.category_key:
                result.error = "CATEGORY matched but category key is empty."
                return result

            if ctx.fetch_error and rule_needs_html(source.category_url_patterns):
                result.error = ctx.fetch_error
            return result

        # If HTML was explicitly required by configured rules and the fetch failed,
        # do not silently mark the URL as OTHER; let a later run retry it.
        if ctx.fetch_error and (
            rule_needs_html(source.brand_url_patterns)
            or rule_needs_html(source.category_url_patterns)
        ):
            result.error = ctx.fetch_error
            return result

        result.detected_type = "OTHER"
        return result

    except Exception as exc:
        result.error = safe_text(exc)
        return result



class SheetsHub:
    """
    Small Google Sheets client with transport-level retries.

    A transient TLS/SSL EOF from Google must not destroy a long analysis run.
    Every API request is rebuilt and retried with exponential backoff.
    """

    GOOGLE_API_ATTEMPTS = 7
    GOOGLE_API_BACKOFF_SECONDS = 1.5
    GOOGLE_API_MAX_BACKOFF_SECONDS = 30.0

    def __init__(self, spreadsheet_id: str, service_account_json: str):
        self._service_account_info = json.loads(service_account_json)
        self._credentials = service_account.Credentials.from_service_account_info(
            self._service_account_info,
            scopes=["https://www.googleapis.com/auth/spreadsheets"],
        )
        self.spreadsheet_id = spreadsheet_id
        self.service = self._build_service()
        self._sheets: Optional[Dict[str, dict]] = None

    def _build_service(self):
        return build(
            "sheets",
            "v4",
            credentials=self._credentials,
            cache_discovery=False,
        )

    def _rebuild_service(self) -> None:
        # Re-create httplib2 transport after SSL/connection failures.
        self.service = self._build_service()

    @staticmethod
    def _retryable_google_error(exc: Exception) -> bool:
        if isinstance(exc, HttpError):
            status = getattr(getattr(exc, "resp", None), "status", None)
            return status in {408, 409, 425, 429, 500, 502, 503, 504}

        if isinstance(exc, (ssl.SSLError, ConnectionError, TimeoutError, OSError)):
            return True

        message = safe_text(exc).lower()
        retry_markers = (
            "ssl",
            "eof occurred",
            "connection reset",
            "connection aborted",
            "broken pipe",
            "temporarily unavailable",
            "timed out",
            "timeout",
            "remote end closed",
            "server disconnected",
        )
        return any(marker in message for marker in retry_markers)

    def _execute(self, request_factory, label: str):
        last_error: Optional[Exception] = None

        for attempt in range(1, self.GOOGLE_API_ATTEMPTS + 1):
            try:
                request = request_factory()
                # googleapiclient also has its own retry path for 5xx/429.
                return request.execute(num_retries=2)
            except Exception as exc:
                last_error = exc

                if (
                    attempt >= self.GOOGLE_API_ATTEMPTS
                    or not self._retryable_google_error(exc)
                ):
                    raise

                delay = min(
                    self.GOOGLE_API_MAX_BACKOFF_SECONDS,
                    self.GOOGLE_API_BACKOFF_SECONDS * (2 ** (attempt - 1)),
                )
                delay += random.uniform(0.0, 0.75)

                print(
                    f"[google-retry] {label}: attempt {attempt}/"
                    f"{self.GOOGLE_API_ATTEMPTS} failed: {exc}; "
                    f"retry in {delay:.1f}s",
                    flush=True,
                )
                time.sleep(delay)

                try:
                    self._rebuild_service()
                except Exception:
                    # The next request attempt will surface a persistent rebuild problem.
                    pass

        if last_error:
            raise last_error
        raise RuntimeError(f"Google API request failed without exception: {label}")

    @staticmethod
    def q(title: str) -> str:
        return "'" + title.replace("'", "''") + "'"

    def sheets(self) -> Dict[str, dict]:
        if self._sheets is None:
            result = self._execute(
                lambda: self.service.spreadsheets().get(
                    spreadsheetId=self.spreadsheet_id,
                    fields="sheets.properties",
                ),
                "spreadsheets.get",
            )
            self._sheets = {
                x["properties"]["title"]: x["properties"]
                for x in result.get("sheets", [])
            }
        return self._sheets

    def ensure_sheet(
        self,
        title: str,
        headers: Sequence[str],
        hidden: bool = False,
    ) -> None:
        if title not in self.sheets():
            self._execute(
                lambda: self.service.spreadsheets().batchUpdate(
                    spreadsheetId=self.spreadsheet_id,
                    body={
                        "requests": [
                            {
                                "addSheet": {
                                    "properties": {
                                        "title": title,
                                        "hidden": bool(hidden),
                                    }
                                }
                            }
                        ]
                    },
                ),
                f"addSheet:{title}",
            )
            self._sheets = None

        first = self.get_values(f"{self.q(title)}!1:1")
        if not first or not any(safe_text(x) for x in first[0]):
            self.update_values(
                f"{self.q(title)}!A1",
                [list(headers)],
            )

    def get_values(self, a1_range: str) -> List[List[object]]:
        result = self._execute(
            lambda: self.service.spreadsheets().values().get(
                spreadsheetId=self.spreadsheet_id,
                range=a1_range,
            ),
            f"values.get:{a1_range}",
        )
        return result.get("values", [])

    @staticmethod
    def _sheet_title_from_a1_part(sheet_part: str) -> str:
        """Convert an A1 sheet token like '1_ MAIN Brands' back to its title."""
        value = safe_text(sheet_part).strip()
        if len(value) >= 2 and value[0] == "'" and value[-1] == "'":
            value = value[1:-1].replace("''", "'")
        return value

    def ensure_row_capacity(
        self,
        sheet_title: str,
        required_last_row: int,
        growth_step: int = 1000,
    ) -> None:
        """Ensure a GRID sheet has enough rows before a values write.

        The caller controls the growth step. Normal run preallocation uses an
        exact deficit (step=1); last-moment write protection can still grow in
        larger blocks. This prevents Google Sheets HTTP 400 grid-limit errors.
        """
        if required_last_row <= 0:
            return
        if growth_step <= 0:
            raise ValueError("growth_step must be greater than zero")

        props = self.sheets().get(sheet_title)
        if props is None:
            # Refresh once in case the sheet was created after the metadata cache.
            self._sheets = None
            props = self.sheets().get(sheet_title)
        if props is None:
            raise ValueError(f"Sheet not found while checking row capacity: {sheet_title}")

        grid = props.get("gridProperties") or {}
        current_rows = int(grid.get("rowCount") or 0)
        if current_rows >= required_last_row:
            return

        missing_rows = required_last_row - current_rows
        blocks = (missing_rows + growth_step - 1) // growth_step
        rows_to_add = blocks * growth_step
        sheet_id = props.get("sheetId")
        if sheet_id is None:
            raise ValueError(f"Sheet has no sheetId: {sheet_title}")

        self._execute(
            lambda: self.service.spreadsheets().batchUpdate(
                spreadsheetId=self.spreadsheet_id,
                body={
                    "requests": [
                        {
                            "appendDimension": {
                                "sheetId": sheet_id,
                                "dimension": "ROWS",
                                "length": rows_to_add,
                            }
                        }
                    ]
                },
            ),
            f"appendRows:{sheet_title}:+{rows_to_add}",
        )

        new_row_count = current_rows + rows_to_add
        # Keep the local metadata cache in sync so consecutive writes do not
        # perform unnecessary growth requests in the same run.
        props.setdefault("gridProperties", {})["rowCount"] = new_row_count
        print(
            f"[sheet-grow] {sheet_title}: {current_rows} -> {new_row_count} "
            f"(+{rows_to_add}); required={required_last_row}",
            flush=True,
        )

    def ensure_append_capacity(
        self,
        a1_range: str,
        additional_rows: int,
    ) -> None:
        """Reserve enough physical rows for an upcoming append workload.

        The caller already knows how many queue rows are going to be processed.
        We use that count to reserve capacity once, before analysis starts, instead
        of discovering the grid limit one chunk at a time while writing results.
        Existing unused grid rows are reused; only the actual deficit is added.
        """
        if additional_rows <= 0:
            return
        if "!" not in a1_range:
            raise ValueError(
                f"ensure_append_capacity requires a sheet-qualified range: {a1_range}"
            )

        sheet_part, _ = a1_range.rsplit("!", 1)
        sheet_title = self._sheet_title_from_a1_part(sheet_part)
        existing_rows = len(self.get_values(a1_range))
        required_last_row = existing_rows + int(additional_rows)

        props = self.sheets().get(sheet_title)
        current_rows = int(((props or {}).get("gridProperties") or {}).get("rowCount") or 0)
        deficit = max(0, required_last_row - current_rows)

        if deficit > 0:
            self.ensure_row_capacity(
                sheet_title,
                required_last_row,
                growth_step=1,  # add exactly the missing number of rows
            )

        print(
            f"[sheet-reserve] {sheet_title}: existing_data={existing_rows}; "
            f"planned={additional_rows}; required={required_last_row}; "
            f"grid_before={current_rows}; added={deficit}",
            flush=True,
        )

    def _ensure_capacity_for_update(
        self,
        a1_range: str,
        payload: Sequence[Sequence[object]],
    ) -> None:
        """Best-effort A1 parsing for row-based values.update writes."""
        if not payload or "!" not in a1_range:
            return

        sheet_part, cell_part = a1_range.rsplit("!", 1)
        # values.update calls in this script start from an explicit row, e.g.
        # A1, A1090, A12:N12, K500:L500. Column-only ranges are ignored.
        start_match = re.match(r"\s*(?:[A-Za-z]+)?(\d+)", cell_part)
        if not start_match:
            return

        start_row = int(start_match.group(1))
        required_last_row = start_row + len(payload) - 1
        sheet_title = self._sheet_title_from_a1_part(sheet_part)
        if sheet_title:
            self.ensure_row_capacity(sheet_title, required_last_row, growth_step=1000)

    def update_values(
        self,
        a1_range: str,
        values: Sequence[Sequence[object]],
    ) -> None:
        payload = [list(x) for x in values]
        if not payload:
            return

        # Always make sure the destination rows physically exist before writing.
        self._ensure_capacity_for_update(a1_range, payload)

        self._execute(
            lambda: self.service.spreadsheets().values().update(
                spreadsheetId=self.spreadsheet_id,
                range=a1_range,
                valueInputOption="RAW",
                body={"values": payload},
            ),
            f"values.update:{a1_range}",
        )

    def append_values(
        self,
        a1_range: str,
        values: Sequence[Sequence[object]],
        chunk_size: int = 500,
    ) -> None:
        rows = [list(x) for x in values]
        if not rows:
            return

        for start in range(0, len(rows), chunk_size):
            chunk = rows[start : start + chunk_size]
            self._execute(
                lambda chunk=chunk: self.service.spreadsheets().values().append(
                    spreadsheetId=self.spreadsheet_id,
                    range=a1_range,
                    valueInputOption="RAW",
                    insertDataOption="INSERT_ROWS",
                    body={"values": chunk},
                ),
                f"values.append:{a1_range}",
            )

    def append_values_idempotent(
        self,
        a1_range: str,
        values: Sequence[Sequence[object]],
        chunk_size: int = 200,
    ) -> None:
        """
        Append rows by first resolving the exact destination row and then using
        values.update. Retrying an update to the same A1 range is idempotent,
        unlike retrying values.append after an ambiguous SSL EOF.

        Intended for a project Control spreadsheet where only this analysis run
        writes the visible output sheets.
        """
        rows = [list(x) for x in values]
        if not rows:
            return

        if "!" not in a1_range:
            raise ValueError(
                f"append_values_idempotent requires a sheet-qualified range: {a1_range}"
            )

        sheet_part, columns_part = a1_range.rsplit("!", 1)
        first_col_match = re.match(r"\s*([A-Za-z]+)", columns_part)
        if not first_col_match:
            raise ValueError(f"Cannot parse start column from range: {a1_range}")

        first_col = first_col_match.group(1).upper()
        existing = self.get_values(a1_range)
        next_row = len(existing) + 1

        for start in range(0, len(rows), chunk_size):
            chunk = rows[start : start + chunk_size]
            target = f"{sheet_part}!{first_col}{next_row}"
            self.update_values(target, chunk)
            next_row += len(chunk)

    def batch_update_cells(
        self,
        data: Sequence[dict],
        chunk_size: int = 250,
    ) -> None:
        payload = list(data)
        if not payload:
            return

        for start in range(0, len(payload), chunk_size):
            chunk = payload[start : start + chunk_size]
            self._execute(
                lambda chunk=chunk: self.service.spreadsheets().values().batchUpdate(
                    spreadsheetId=self.spreadsheet_id,
                    body={
                        "valueInputOption": "RAW",
                        "data": chunk,
                    },
                ),
                "values.batchUpdate",
            )

def header_map(headers: Sequence[object]) -> Dict[str, int]:
    return {
        safe_text(name): index
        for index, name in enumerate(headers)
        if safe_text(name)
    }


def assert_headers(mapping: Dict[str, int], required: Sequence[str], label: str) -> None:
    missing = [name for name in required if name not in mapping]
    if missing:
        raise ValueError(f"{label}: missing columns: {', '.join(missing)}")


def row_value(row: Sequence[object], mapping: Dict[str, int], header: str) -> str:
    index = mapping.get(header)
    if index is None or index >= len(row):
        return ""
    return safe_text(row[index])


def load_queue(hub: SheetsHub, project_id: str) -> List[QueueRow]:
    values = hub.get_values(f"{hub.q(QUEUE_SHEET)}!A:L")
    if not values:
        raise ValueError(f"{QUEUE_SHEET} is empty or missing.")

    mapping = header_map(values[0])
    assert_headers(mapping, QUEUE_REQUIRED_HEADERS, QUEUE_SHEET)

    out: List[QueueRow] = []

    for sheet_row, row in enumerate(values[1:], start=2):
        if row_value(row, mapping, "Project ID") != project_id:
            continue

        processed = row_value(row, mapping, "Processed").upper()
        if processed not in ("", "ERROR"):
            continue

        url = row_value(row, mapping, "URL")
        if not url:
            continue

        out.append(
            QueueRow(
                sheet_row=sheet_row,
                export_run_id=row_value(row, mapping, "Run ID"),
                exported_at=row_value(row, mapping, "Exported At"),
                project_id=row_value(row, mapping, "Project ID"),
                geo=row_value(row, mapping, "GEO"),
                source_id=row_value(row, mapping, "Source ID"),
                site_url=row_value(row, mapping, "Site URL"),
                role=row_value(row, mapping, "Role").lower(),
                url=url,
                last_modified=row_value(row, mapping, "Last Modified"),
                source_sitemap=row_value(row, mapping, "Source Sitemap"),
                processed=processed,
                analysis_run_id=row_value(row, mapping, "Analysis Run ID"),
            )
        )

    return out


def analysis_sheet_prefix(project_id: str) -> str:
    value = re.sub(r"[^A-Za-z0-9_-]+", "_", safe_text(project_id)).strip("_")
    return (value or "PROJECT")[:45]


def output_sheet_names(project_id: str) -> Dict[str, str]:
    # Visible results live in the project Control spreadsheet, not in Hub.
    # One Control spreadsheet is the compact working file for its PROJECT_ID,
    # so we keep the familiar old-parser sheet names without project prefixes.
    return {
        "main_brands": "1_ MAIN Brands",
        "missing_brands": "2_Missing Brands",
        "categories": "3_Categories",
        "missing_categories": "4_Missing Categories",
    }


def load_existing_cache(
    hub: SheetsHub,
    project_id: str,
) -> Tuple[Dict[str, AnalysisResult], Dict[str, AnalysisResult]]:
    values = hub.get_values(f"{hub.q(CACHE_SHEET)}!A:T")
    if len(values) < 2:
        return {}, {}

    mapping = header_map(values[0])
    assert_headers(mapping, CACHE_HEADERS, CACHE_SHEET)

    own_brands: Dict[str, AnalysisResult] = {}
    own_categories: Dict[str, AnalysisResult] = {}

    for row in values[1:]:
        if row_value(row, mapping, "Project ID") != project_id:
            continue
        if row_value(row, mapping, "Role").lower() != "our":
            continue
        if row_value(row, mapping, "Error"):
            continue

        fake_queue = QueueRow(
            sheet_row=0,
            export_run_id="",
            exported_at="",
            project_id=project_id,
            geo=row_value(row, mapping, "GEO"),
            source_id=row_value(row, mapping, "Source ID"),
            site_url=row_value(row, mapping, "Site URL"),
            role="our",
            url=row_value(row, mapping, "URL"),
            last_modified=row_value(row, mapping, "Last Modified"),
            source_sitemap=row_value(row, mapping, "Source Sitemap"),
            processed="YES",
            analysis_run_id=row_value(row, mapping, "Analysis Run ID"),
        )

        result = AnalysisResult(
            queue=fake_queue,
            source=SourceConfig(
                project_id=project_id,
                geo=fake_queue.geo,
                source_id=fake_queue.source_id,
                role="our",
                enabled=True,
                site_url=fake_queue.site_url,
                sitemap_url="",
                brand_url_patterns="",
                brand_extraction_rule="",
                bonus_footprint="",
                category_url_patterns="",
                affiliate_network="",
                ref_rule="",
            ),
            detected_type=row_value(row, mapping, "Detected Type"),
            brand=row_value(row, mapping, "Brand"),
            brand_key=row_value(row, mapping, "Brand Key"),
            category_key=row_value(row, mapping, "Category Key"),
            url_key=row_value(row, mapping, "URL Key"),
            h1=row_value(row, mapping, "H1"),
            h1_key=row_value(row, mapping, "H1 Key"),
            bonus=row_value(row, mapping, "Bonus"),
            ref_link=row_value(row, mapping, "Ref Link"),
            analyzed_at=row_value(row, mapping, "Analyzed At"),
            error="",
        )

        if result.detected_type == "BRAND" and result.brand_key:
            own_brands.setdefault(result.brand_key, result)

        if result.detected_type == "CATEGORY":
            for key in (result.category_key, result.h1_key, result.url_key):
                if key:
                    own_categories.setdefault(key, result)

    return own_brands, own_categories


def load_output_keys(
    hub: SheetsHub,
    names: Dict[str, str],
) -> Dict[str, Set[str]]:
    out = {
        "main_brands": set(),
        "brand_site": set(),
        "missing_brands": set(),
        "missing_brand_keys": set(),
        "categories": set(),
        "missing_categories": set(),
    }

    main = hub.get_values(f"{hub.q(names['main_brands'])}!A:N")
    for row in main[1:]:
        if len(row) > 6 and safe_text(row[6]):
            out["main_brands"].add(safe_text(row[6]).lower())
        if len(row) > 11:
            competitor = host_of(safe_text(row[5]))
            bkey = brand_key(safe_text(row[11]))
            if competitor and bkey:
                out["brand_site"].add(competitor + "|" + bkey)

    missing = hub.get_values(f"{hub.q(names['missing_brands'])}!A:H")
    for row in missing[1:]:
        if row and safe_text(row[0]):
            out["missing_brands"].add(safe_text(row[0]).lower())
        if len(row) > 1:
            bkey = brand_key(safe_text(row[1]))
            if bkey:
                out["missing_brand_keys"].add(bkey)

    cats = hub.get_values(f"{hub.q(names['categories'])}!A:G")
    for row in cats[1:]:
        if len(row) > 2 and safe_text(row[2]):
            out["categories"].add(safe_text(row[2]).lower())

    missing_cats = hub.get_values(f"{hub.q(names['missing_categories'])}!A:G")
    for row in missing_cats[1:]:
        if len(row) > 1 and safe_text(row[1]):
            out["missing_categories"].add(safe_text(row[1]).lower())

    return out


def find_our_category(
    own_categories: Dict[str, AnalysisResult],
    result: AnalysisResult,
) -> Optional[AnalysisResult]:
    for key in (result.h1_key, result.url_key, result.category_key):
        if key and key in own_categories:
            return own_categories[key]
    return None


def run_parallel(
    rows: Sequence[QueueRow],
    source_map: Dict[str, SourceConfig],
    fetcher: HttpFetcher,
    max_workers: int,
    enrich_missing_brand: bool,
    brand_lexicon: Optional[Dict[str, dict]] = None,
) -> List[AnalysisResult]:
    out: List[AnalysisResult] = []

    def one(row: QueueRow) -> AnalysisResult:
        source = source_map[row.source_id]
        return classify_row(
            row,
            source,
            fetcher,
            enrich_missing_brand=enrich_missing_brand,
            brand_lexicon=brand_lexicon,
        )

    if not rows:
        return out

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as pool:
        future_map = {pool.submit(one, row): row for row in rows}
        for future in concurrent.futures.as_completed(future_map):
            row = future_map[future]
            try:
                out.append(future.result())
            except Exception as exc:
                source = source_map[row.source_id]
                out.append(
                    AnalysisResult(
                        queue=row,
                        source=source,
                        analyzed_at=utc_now(),
                        error=safe_text(exc),
                    )
                )

    out.sort(key=lambda item: item.queue.sheet_row)
    return out



@dataclass
class RunStats:
    pending_total: int
    handled: int = 0
    brands: int = 0
    categories: int = 0
    missing_brands: int = 0
    missing_categories: int = 0
    errors: int = 0
    skipped: int = 0


def iter_chunks(items: Sequence[QueueRow], size: int) -> Iterable[List[QueueRow]]:
    size = max(1, int(size))
    for start in range(0, len(items), size):
        yield list(items[start : start + size])


def update_analysis_run(
    hub: SheetsHub,
    run_sheet_row: int,
    started_at: str,
    stats: RunStats,
    phase: str,
    message: str,
    finished: bool = False,
) -> None:
    now = utc_now()
    finished_at = now if finished else ""

    hub.update_values(
        f"{hub.q(ANALYSIS_RUNS_SHEET)}!C{run_sheet_row}:N{run_sheet_row}",
        [[
            phase,
            stats.pending_total,
            stats.handled,
            stats.brands,
            stats.categories,
            stats.missing_brands,
            stats.missing_categories,
            stats.errors,
            started_at,
            now,
            finished_at,
            message,
        ]],
    )


def checkpoint_batch(
    hub: SheetsHub,
    run_id: str,
    run_sheet_row: int,
    started_at: str,
    stats: RunStats,
    successful_results: Sequence[AnalysisResult],
    failed_results: Sequence[AnalysisResult],
    queue_updates_extra: Optional[Sequence[dict]] = None,
    message_prefix: str = "Running",
) -> None:
    """
    Commit one completed analysis chunk.

    Order is deliberate:
      1) cache successful page analysis;
      2) queue completion/error marks;
      3) progress status.

    If a visible Control write happened immediately before this checkpoint and
    the process dies here, the next run de-duplicates visible output by URL.
    """
    successful = list(successful_results)
    failed = list(failed_results)

    # Cache only successful results. ERROR queue rows are retried later, so
    # repeatedly caching failed attempts would only bloat the technical Hub.
    if successful:
        hub.append_values(
            f"{hub.q(CACHE_SHEET)}!A:T",
            [result.cache_row(run_id) for result in successful],
            chunk_size=250,
        )

    queue_updates: List[dict] = list(queue_updates_extra or [])

    for result in successful:
        queue_updates.append(
            {
                "range": (
                    f"{hub.q(QUEUE_SHEET)}!"
                    f"K{result.queue.sheet_row}:L{result.queue.sheet_row}"
                ),
                "values": [["YES", run_id]],
            }
        )

    for result in failed:
        queue_updates.append(
            {
                "range": (
                    f"{hub.q(QUEUE_SHEET)}!"
                    f"K{result.queue.sheet_row}:L{result.queue.sheet_row}"
                ),
                "values": [["ERROR", run_id]],
            }
        )

    hub.batch_update_cells(queue_updates, chunk_size=200)

    update_analysis_run(
        hub=hub,
        run_sheet_row=run_sheet_row,
        started_at=started_at,
        stats=stats,
        phase="RUNNING",
        message=(
            f"{message_prefix}. Progress {stats.handled}/{stats.pending_total}; "
            f"errors={stats.errors}; brands={stats.brands}; "
            f"categories={stats.categories}."
        ),
        finished=False,
    )

    print(
        f"[progress] {stats.handled}/{stats.pending_total} | "
        f"brands={stats.brands} | categories={stats.categories} | "
        f"errors={stats.errors}",
        flush=True,
    )


def main() -> int:
    started_at = utc_now()
    run_id = safe_text(os.environ.get("PARSER_RUN_ID"))
    payload_raw = safe_text(os.environ.get("PARSER_PAYLOAD_GZIP_B64"))
    service_json = safe_text(os.environ.get("GOOGLE_SERVICE_ACCOUNT_JSON"))

    if not run_id:
        raise ValueError("PARSER_RUN_ID is empty.")
    if not service_json:
        raise ValueError("GOOGLE_SERVICE_ACCOUNT_JSON is empty.")

    payload = decode_payload(payload_raw)

    if safe_text(payload.get("run_id")) != run_id:
        raise ValueError("Run ID mismatch between workflow input and payload.")

    project_id = safe_text(payload.get("project_id"))
    hub_id = safe_text(payload.get("hub_spreadsheet_id"))
    control_id = safe_text(payload.get("control_spreadsheet_id"))

    if not project_id:
        raise ValueError("project_id is empty.")
    if not hub_id:
        raise ValueError("hub_spreadsheet_id is empty.")
    if not control_id:
        raise ValueError("control_spreadsheet_id is empty.")

    source_list = [
        SourceConfig.from_dict(x, project_id)
        for x in payload.get("sources", [])
        if isinstance(x, dict)
    ]

    source_map = {
        x.source_id: x
        for x in source_list
        if x.enabled and x.project_id == project_id and x.source_id
    }

    if not source_map:
        raise ValueError("No enabled source configs for this project.")

    engine = payload.get("engine") or {}
    fetcher = HttpFetcher(
        timeout_seconds=int(engine.get("timeout_seconds", 25)),
        retries=int(engine.get("retries", 3)),
        retry_backoff_seconds=float(engine.get("retry_backoff_seconds", 1.5)),
        user_agent=safe_text(
            engine.get("user_agent")
            or "Mozilla/5.0 (compatible; UniversalAnalysisEngine/3.0)"
        ),
    )

    max_workers = max(1, min(32, int(engine.get("max_workers", 12))))
    checkpoint_size = max(25, min(500, int(engine.get("checkpoint_size", 200))))

    # Hub stores only shared technical state/queue/cache/status.
    hub = SheetsHub(hub_id, service_json)
    hub.ensure_sheet(CACHE_SHEET, CACHE_HEADERS, hidden=True)
    hub.ensure_sheet(ANALYSIS_RUNS_SHEET, ANALYSIS_RUN_HEADERS, hidden=True)

    # Visible business results are written directly to the project's Control file.
    control = SheetsHub(control_id, service_json)
    names = output_sheet_names(project_id)
    control.ensure_sheet(names["main_brands"], MAIN_BRANDS_HEADERS)
    control.ensure_sheet(names["missing_brands"], MISSING_BRANDS_HEADERS)
    control.ensure_sheet(names["categories"], CATEGORIES_HEADERS)
    control.ensure_sheet(names["missing_categories"], MISSING_CATEGORIES_HEADERS)

    pending = load_queue(hub, project_id)
    stats = RunStats(pending_total=len(pending))

    # The queue is already populated from exported sitemaps/URLs, so at this
    # point we know exactly how many rows this run may process. Reserve that
    # amount of append capacity on every visible result sheet before analysis.
    # Each processed URL can contribute at most one row to any one of these
    # result sheets, therefore len(pending) is a safe upper bound per sheet.
    if pending:
        planned_rows = len(pending)
        for reserve_range in (
            f"{control.q(names['main_brands'])}!A:N",
            f"{control.q(names['missing_brands'])}!A:H",
            f"{control.q(names['categories'])}!A:G",
            f"{control.q(names['missing_categories'])}!A:G",
        ):
            control.ensure_append_capacity(reserve_range, planned_rows)

    run_rows_before = hub.get_values(f"{hub.q(ANALYSIS_RUNS_SHEET)}!A:N")
    run_sheet_row = len(run_rows_before) + 1

    hub.update_values(
        f"{hub.q(ANALYSIS_RUNS_SHEET)}!A{run_sheet_row}:N{run_sheet_row}",
        [[
            run_id,
            project_id,
            "RUNNING",
            len(pending),
            0,
            0,
            0,
            0,
            0,
            0,
            started_at,
            started_at,
            "",
            f"Analysis started. Checkpoint size={checkpoint_size}.",
        ]],
    )

    try:
        if not pending:
            update_analysis_run(
                hub,
                run_sheet_row,
                started_at,
                stats,
                "DONE",
                "No pending URLs for this project.",
                finished=True,
            )
            print("DONE: no pending URLs.", flush=True)
            return 0

        configured_rows: List[QueueRow] = []
        skipped_updates: List[dict] = []

        for row in pending:
            if row.source_id not in source_map:
                stats.skipped += 1
                stats.handled += 1
                skipped_updates.append(
                    {
                        "range": (
                            f"{hub.q(QUEUE_SHEET)}!"
                            f"K{row.sheet_row}:L{row.sheet_row}"
                        ),
                        "values": [["SKIPPED", run_id]],
                    }
                )
            else:
                configured_rows.append(row)

        if skipped_updates:
            checkpoint_batch(
                hub=hub,
                run_id=run_id,
                run_sheet_row=run_sheet_row,
                started_at=started_at,
                stats=stats,
                successful_results=[],
                failed_results=[],
                queue_updates_extra=skipped_updates,
                message_prefix="Skipped rows without current source config",
            )

        own_rows = [
            row for row in configured_rows
            if source_map[row.source_id].role == "our"
        ]
        competitor_rows = [
            row for row in configured_rows
            if source_map[row.source_id].role != "our"
        ]

        # Reuse own successful cache from earlier completed checkpoints/runs.
        own_brands, own_categories = load_existing_cache(hub, project_id)

        # Shared brand lexicon is built from reliable own/competitor brand pages.
        # Config-selected promo-tail extractors can use it to recover a clean
        # brand from long promotion/news slugs without any domain branch here.
        brand_lexicon: Dict[str, dict] = {}
        for cached_brand in own_brands.values():
            if cached_brand.brand:
                add_brand_to_lexicon(brand_lexicon, cached_brand.brand)

        # 1) OUR pages first, because competitor matching depends on them.
        for batch_no, batch in enumerate(
            iter_chunks(own_rows, checkpoint_size),
            start=1,
        ):
            results = run_parallel(
                batch,
                source_map,
                fetcher,
                max_workers,
                enrich_missing_brand=False,
            )

            successful: List[AnalysisResult] = []
            failed: List[AnalysisResult] = []

            for result in results:
                stats.handled += 1

                if result.error:
                    stats.errors += 1
                    failed.append(result)
                    continue

                successful.append(result)

                if result.detected_type == "BRAND":
                    stats.brands += 1
                    if result.brand_key:
                        own_brands.setdefault(result.brand_key, result)
                    if result.brand:
                        add_brand_to_lexicon(brand_lexicon, result.brand)

                elif result.detected_type == "CATEGORY":
                    stats.categories += 1
                    for key in (
                        result.category_key,
                        result.h1_key,
                        result.url_key,
                    ):
                        if key:
                            own_categories.setdefault(key, result)

            checkpoint_batch(
                hub=hub,
                run_id=run_id,
                run_sheet_row=run_sheet_row,
                started_at=started_at,
                stats=stats,
                successful_results=successful,
                failed_results=failed,
                message_prefix=f"OUR batch {batch_no} committed",
            )

        # Load existing visible rows. This protects re-runs after a crash that
        # happened after Control writes but before queue checkpoint.
        output_keys = load_output_keys(control, names)

        # Optional enrichment is deliberately isolated from classification.
        # A host that returns 50 consecutive HTTP 403 responses for Bonus/ref_link
        # is skipped for enrichment for the rest of this run, while BRAND/CATEGORY
        # processing continues normally.
        enrichment_403_streaks: Dict[str, int] = {}
        enrichment_disabled_hosts: Set[str] = set()

        # 2) Competitor pages in restart-safe checkpoints.
        # Sources using the promo-tail profile run after ordinary sources so
        # their extractor can use brands already discovered elsewhere.
        regular_competitor_rows = [
            row for row in competitor_rows
            if "profile:promo-tail" not in source_map[row.source_id].brand_extraction_rule.lower()
        ]
        dependent_competitor_rows = [
            row for row in competitor_rows
            if "profile:promo-tail" in source_map[row.source_id].brand_extraction_rule.lower()
        ]

        for group_label, group_rows in (
            ("regular", regular_competitor_rows),
            ("promo-tail", dependent_competitor_rows),
        ):
            for batch_no, batch in enumerate(
                iter_chunks(group_rows, checkpoint_size),
                start=1,
            ):
                results = run_parallel(
                    batch,
                    source_map,
                    fetcher,
                    max_workers,
                    enrich_missing_brand=False,
                    brand_lexicon=brand_lexicon,
                )

                successful: List[AnalysisResult] = []
                failed: List[AnalysisResult] = []

                main_brand_rows: List[List[object]] = []
                missing_brand_rows: List[List[object]] = []
                category_rows: List[List[object]] = []
                missing_category_rows: List[List[object]] = []

                for result in results:
                    stats.handled += 1

                    if result.error:
                        stats.errors += 1
                        failed.append(result)
                        continue

                    successful.append(result)

                    if result.detected_type == "BRAND":
                        stats.brands += 1
                        if result.brand:
                            add_brand_to_lexicon(brand_lexicon, result.brand)
                        matched = own_brands.get(result.brand_key)
                        status = "MATCH" if matched else "MISSING"

                        # Only missing brands need bonus/ref enrichment.
                        if not matched:
                            enrichment_host = host_of(result.queue.url)

                            if enrichment_host not in enrichment_disabled_hosts:
                                ctx = PageContext(result.queue, fetcher)
                                result.bonus = extract_bonus(ctx, result.source)
                                result.ref_link = extract_ref_link(ctx, result.source)

                                # Classification itself succeeded. An enrichment-only
                                # fetch failure should not make us lose the discovered brand.
                                if ctx.fetch_error and not result.bonus and not result.ref_link:
                                    if enrichment_host and is_http_403_error(ctx.fetch_error):
                                        streak = enrichment_403_streaks.get(enrichment_host, 0) + 1
                                        enrichment_403_streaks[enrichment_host] = streak

                                        if streak >= ENRICHMENT_403_DISABLE_THRESHOLD:
                                            enrichment_disabled_hosts.add(enrichment_host)
                                            print(
                                                f"[enrichment-disabled] host={enrichment_host} "
                                                f"after {streak} consecutive HTTP 403 "
                                                f"enrichment failures; Bonus/ref_link will be "
                                                f"skipped for this host until the run ends.",
                                                flush=True,
                                            )
                                        else:
                                            print(
                                                f"[enrichment-warning] {result.queue.url}: "
                                                f"{ctx.fetch_error}",
                                                flush=True,
                                            )
                                    else:
                                        if enrichment_host:
                                            enrichment_403_streaks[enrichment_host] = 0
                                        print(
                                            f"[enrichment-warning] {result.queue.url}: "
                                            f"{ctx.fetch_error}",
                                            flush=True,
                                        )
                                elif enrichment_host:
                                    # Any successful enrichment fetch breaks the 403 streak.
                                    enrichment_403_streaks[enrichment_host] = 0

                        comp_url_key = result.queue.url.lower()
                        brand_site_key = (
                            host_of(result.queue.site_url or result.queue.url)
                            + "|"
                            + result.brand_key
                        )

                        # Match the old parser behavior: one row per brand per
                        # competitor site, even if a site exposes several URLs
                        # for the same brand.
                        if (
                            brand_site_key not in output_keys["brand_site"]
                            and comp_url_key not in output_keys["main_brands"]
                        ):
                            main_brand_rows.append([
                                matched.queue.url if matched else "",
                                matched.queue.last_modified if matched else "",
                                matched.analyzed_at if matched else "",
                                matched.brand if matched else "",
                                "BRAND" if matched else "",
                                result.queue.site_url,
                                result.queue.url,
                                result.queue.last_modified,
                                result.analyzed_at,
                                "BRAND",
                                status,
                                result.brand,
                                result.bonus,
                                "",
                            ])
                            output_keys["main_brands"].add(comp_url_key)
                            output_keys["brand_site"].add(brand_site_key)

                        # Keep the compact missing list to one row per normalized
                        # brand. Later competitors do not create duplicates.
                        if (
                            not matched
                            and result.brand_key not in output_keys["missing_brand_keys"]
                            and comp_url_key not in output_keys["missing_brands"]
                        ):
                            missing_brand_rows.append([
                                result.queue.url,
                                result.brand,
                                result.bonus,
                                result.ref_link,
                                "",
                                result.source.affiliate_network,
                                "",
                                "",
                            ])
                            output_keys["missing_brands"].add(comp_url_key)
                            output_keys["missing_brand_keys"].add(result.brand_key)
                            stats.missing_brands += 1

                    elif result.detected_type == "CATEGORY":
                        stats.categories += 1
                        matched = find_our_category(own_categories, result)
                        status = "MATCH" if matched else "MISSING"
                        comp_url_key = result.queue.url.lower()

                        if comp_url_key not in output_keys["categories"]:
                            category_rows.append([
                                matched.queue.url if matched else "",
                                "CATEGORY",
                                result.queue.url,
                                result.queue.site_url,
                                status,
                                result.analyzed_at,
                                "H1: " + result.h1
                                + " | Key: " + result.category_key,
                            ])
                            output_keys["categories"].add(comp_url_key)

                        if (
                            not matched
                            and comp_url_key
                            not in output_keys["missing_categories"]
                        ):
                            missing_category_rows.append([
                                result.analyzed_at,
                                result.queue.url,
                                result.h1,
                                "",
                                "Key: " + result.category_key,
                                result.queue.site_url,
                                "CATEGORY",
                            ])
                            output_keys["missing_categories"].add(comp_url_key)
                            stats.missing_categories += 1

                # Visible result writes are committed per batch.
                control.append_values_idempotent(
                    f"{control.q(names['main_brands'])}!A:N",
                    main_brand_rows,
                    chunk_size=200,
                )
                control.append_values_idempotent(
                    f"{control.q(names['missing_brands'])}!A:H",
                    missing_brand_rows,
                    chunk_size=200,
                )
                control.append_values_idempotent(
                    f"{control.q(names['categories'])}!A:G",
                    category_rows,
                    chunk_size=200,
                )
                control.append_values_idempotent(
                    f"{control.q(names['missing_categories'])}!A:G",
                    missing_category_rows,
                    chunk_size=200,
                )

                checkpoint_batch(
                    hub=hub,
                    run_id=run_id,
                    run_sheet_row=run_sheet_row,
                    started_at=started_at,
                    stats=stats,
                    successful_results=successful,
                    failed_results=failed,
                    message_prefix=f"Competitor {group_label} batch {batch_no} committed",
                )

        phase = "DONE" if stats.errors == 0 else "PARTIAL"
        message = (
            f"Handled={stats.handled}/{stats.pending_total}; "
            f"errors={stats.errors}; skipped={stats.skipped}; "
            f"brands={stats.brands}; categories={stats.categories}; "
            f"missing_brands={stats.missing_brands}; "
            f"missing_categories={stats.missing_categories}."
        )

        update_analysis_run(
            hub,
            run_sheet_row,
            started_at,
            stats,
            phase,
            message,
            finished=True,
        )

        print(f"{phase}: {message}", flush=True)
        return 0

    except Exception as exc:
        # Best-effort terminal status. Google API itself may be the failing
        # dependency, but our retry wrapper gives this several chances too.
        failure_message = (
            f"FAILED after {stats.handled}/{stats.pending_total}. "
            f"Last error: {safe_text(exc)[:500]}"
        )

        try:
            update_analysis_run(
                hub,
                run_sheet_row,
                started_at,
                stats,
                "FAILED",
                failure_message,
                finished=True,
            )
        except Exception as status_exc:
            print(
                f"[status-write-failed] Could not mark run FAILED: {status_exc}",
                file=sys.stderr,
                flush=True,
            )

        raise


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except SystemExit:
        raise
    except Exception as exc:
        print(f"FATAL: {exc}", file=sys.stderr, flush=True)
        traceback.print_exc()
        raise SystemExit(1)
