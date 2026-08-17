#!/usr/bin/env python3
"""
UNIVERSAL SITEMAP EXPORT ENGINE
===============================

This GitHub-side program has NO GEO-, domain-, competitor-, or language-specific
configuration. Every project setting arrives in the workflow payload produced
by the corresponding GEO Google Sheet / Apps Script.

GitHub responsibility:
  1. Receive one normalized JSON payload.
  2. Fetch sitemap XML only (never ordinary page HTML).
  3. Recursively support:
       - a root <urlset>
       - a root <sitemapindex>
       - sitemap indexes nested inside sitemap indexes
       - .xml.gz / gzip sitemap responses
  4. Append only newly discovered page URLs into one central Hub spreadsheet.
  5. Persist per-leaf-sitemap checkpoints in the Hub.
  6. On later runs, use checkpoint comparison rather than lastmod dates.
  7. If a sitemap was reordered/rewritten, automatically fall back to a safe
     URL-history diff for that source so inserted URLs are not missed.

Required repository secret:
  GOOGLE_SERVICE_ACCOUNT_JSON

Workflow payload contract (schema_version = 1):
{
  "schema_version": 1,
  "run_id": "FR_20260816_...",
  "project_id": "FR",
  "geo": "FR",
  "hub_spreadsheet_id": "...",
  "sources": [
    {
      "source_id": "jeux_ca",
      "site_url": "https://jeux.ca",
      "sitemap_url": "https://jeux.ca/sitemap_index.xml",
      "role": "competitor",
      "enabled": true,
      "url_include_regex": "^https://(?:www\\.)?jeux\\.ca/",
      "url_exclude_regex": "/en/|/author/|/tag/|/feed(?:/|$)",
      "sitemap_include_regex": "",
      "sitemap_exclude_regex": ""
    }
  ],
  "engine": {
    "timeout_seconds": 30,
    "retries": 3,
    "retry_backoff_seconds": 2,
    "max_sitemap_depth": 8,
    "user_agent": "Mozilla/5.0 ...",
    "request_headers": {}
  }
}

The Hub workbook is created/maintained automatically:
  _GP_RUNS
  _GP_STATE
  URLS__<PROJECT_ID>

The per-project URL sheet is append-only. The GEO Apps Script can later read
only rows whose Processed column is blank, analyze them, and mark them done.
"""

from __future__ import annotations

import base64
import gzip
import hashlib
import io
import json
import os
import re
import sys
import time
import traceback
from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple
from urllib.parse import urlsplit

import requests
from playwright.sync_api import sync_playwright
from google.oauth2 import service_account
from googleapiclient.discovery import build


SCHEMA_VERSION = 1

RUNS_SHEET = "_GP_RUNS"
STATE_SHEET = "_GP_STATE"

RUN_HEADERS = [
    "Run ID", "Project ID", "GEO", "Phase", "Current Source",
    "Sources Done", "Sources Total", "New URLs", "Sitemap Files",
    "Errors", "Started At", "Updated At", "Finished At", "Message",
]

STATE_HEADERS = [
    "Project ID", "Source ID", "Site URL", "Root Sitemap", "Leaf Sitemap",
    "URL Count", "Last URL", "Ordered Hash", "Config Hash",
    "Last Run ID", "Updated At", "Last Error",
]

URL_HEADERS = [
    "Run ID", "Exported At", "Project ID", "GEO", "Source ID",
    "Site URL", "Role", "URL", "Last Modified", "Source Sitemap",
    "Processed", "Analysis Run ID",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def ordered_url_hash(urls: Sequence[str]) -> str:
    # Length-prefixing avoids ambiguous concatenation.
    h = hashlib.sha256()
    for url in urls:
        b = url.encode("utf-8")
        h.update(str(len(b)).encode("ascii"))
        h.update(b":")
        h.update(b)
        h.update(b"\n")
    return h.hexdigest()


def safe_project_slug(project_id: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9_-]+", "_", project_id.strip())
    slug = slug.strip("_") or "PROJECT"
    return slug[:75]


def quote_sheet(title: str) -> str:
    return "'" + title.replace("'", "''") + "'"


def decode_payload(encoded: str) -> dict:
    if not encoded:
        raise ValueError("PARSER_PAYLOAD_GZIP_B64 is empty.")
    padded = encoded + "=" * (-len(encoded) % 4)
    raw = base64.urlsafe_b64decode(padded.encode("ascii"))
    payload_bytes = gzip.decompress(raw)
    return json.loads(payload_bytes.decode("utf-8"))


def compile_optional_regex(value: object, field_name: str) -> Optional[re.Pattern]:
    text = str(value or "").strip()
    if not text:
        return None
    try:
        return re.compile(text, re.IGNORECASE)
    except re.error as exc:
        raise ValueError(f"Invalid {field_name}: {text!r}: {exc}") from exc


def regex_allows(
    value: str,
    include_re: Optional[re.Pattern],
    exclude_re: Optional[re.Pattern],
) -> bool:
    if include_re and not include_re.search(value):
        return False
    if exclude_re and exclude_re.search(value):
        return False
    return True


def split_sitemap_urls(value: object) -> List[str]:
    """Accept one sitemap URL or several URLs separated by newlines/commas/semicolons."""
    text = str(value or "").strip()
    if not text:
        return []
    parts = re.split(r"[\r\n;,]+", text)
    urls: List[str] = []
    seen: Set[str] = set()
    for part in parts:
        url = part.strip()
        if not url:
            continue
        if not re.match(r"^https?://", url, re.IGNORECASE):
            raise ValueError(f"Invalid sitemap URL: {url!r}")
        if url not in seen:
            seen.add(url)
            urls.append(url)
    return urls


@dataclass(frozen=True)
class SitemapEntry:
    url: str
    lastmod: str = ""


@dataclass
class LeafSitemap:
    url: str
    entries: List[SitemapEntry]


@dataclass
class SourceConfig:
    source_id: str
    site_url: str
    sitemap_url: str
    role: str
    enabled: bool
    url_include_text: str
    url_exclude_text: str
    sitemap_include_text: str
    sitemap_exclude_text: str

    url_include_re: Optional[re.Pattern] = None
    url_exclude_re: Optional[re.Pattern] = None
    sitemap_include_re: Optional[re.Pattern] = None
    sitemap_exclude_re: Optional[re.Pattern] = None

    @classmethod
    def from_dict(cls, data: dict) -> "SourceConfig":
        source_id = str(data.get("source_id") or "").strip()
        sitemap_url = str(data.get("sitemap_url") or "").strip()
        site_url = str(data.get("site_url") or "").strip()
        role = str(data.get("role") or "").strip().lower() or "competitor"
        enabled_raw = data.get("enabled", True)
        enabled = enabled_raw if isinstance(enabled_raw, bool) else str(enabled_raw).strip().lower() not in {
            "0", "false", "no", "off", ""
        }

        if not source_id:
            raise ValueError("Every source requires a stable source_id.")
        if not split_sitemap_urls(sitemap_url):
            raise ValueError(f"Source {source_id!r} has no sitemap_url.")
        if not site_url:
            raise ValueError(f"Source {source_id!r} has no site_url.")

        url_include_text = str(data.get("url_include_regex") or "").strip()
        url_exclude_text = str(data.get("url_exclude_regex") or "").strip()
        sitemap_include_text = str(data.get("sitemap_include_regex") or "").strip()
        sitemap_exclude_text = str(data.get("sitemap_exclude_regex") or "").strip()

        return cls(
            source_id=source_id,
            site_url=site_url,
            sitemap_url=sitemap_url,
            role=role,
            enabled=enabled,
            url_include_text=url_include_text,
            url_exclude_text=url_exclude_text,
            sitemap_include_text=sitemap_include_text,
            sitemap_exclude_text=sitemap_exclude_text,
            url_include_re=compile_optional_regex(url_include_text, f"{source_id}.url_include_regex"),
            url_exclude_re=compile_optional_regex(url_exclude_text, f"{source_id}.url_exclude_regex"),
            sitemap_include_re=compile_optional_regex(sitemap_include_text, f"{source_id}.sitemap_include_regex"),
            sitemap_exclude_re=compile_optional_regex(sitemap_exclude_text, f"{source_id}.sitemap_exclude_regex"),
        )

    def config_hash(self) -> str:
        normalized = json.dumps(
            {
                "site_url": self.site_url,
                "sitemap_url": self.sitemap_url,
                "url_include_regex": self.url_include_text,
                "url_exclude_regex": self.url_exclude_text,
                "sitemap_include_regex": self.sitemap_include_text,
                "sitemap_exclude_regex": self.sitemap_exclude_text,
            },
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        return sha256_text(normalized)


@dataclass
class EngineConfig:
    timeout_seconds: int
    retries: int
    retry_backoff_seconds: float
    max_sitemap_depth: int
    user_agent: str
    request_headers: Dict[str, str]

    @classmethod
    def from_dict(cls, data: dict) -> "EngineConfig":
        headers = data.get("request_headers") or {}
        if not isinstance(headers, dict):
            raise ValueError("engine.request_headers must be an object.")
        return cls(
            timeout_seconds=max(5, int(data.get("timeout_seconds", 30))),
            retries=max(1, int(data.get("retries", 3))),
            retry_backoff_seconds=max(0.0, float(data.get("retry_backoff_seconds", 2))),
            max_sitemap_depth=max(1, int(data.get("max_sitemap_depth", 8))),
            user_agent=str(data.get("user_agent") or "UniversalSitemapParser/1.0"),
            request_headers={str(k): str(v) for k, v in headers.items()},
        )


class SitemapFetcher:
    def __init__(self, cfg: EngineConfig):
        self.cfg = cfg
        self.session = requests.Session()
        default_headers = {
            "User-Agent": cfg.user_agent,
            "Accept": "application/xml,text/xml,text/plain,text/html,*/*;q=0.8",
            "Accept-Language": "es-ES,es;q=0.9,en;q=0.8",
            "Cache-Control": "no-cache",
        }
        default_headers.update(cfg.request_headers)
        self.session.headers.update(default_headers)

    @staticmethod
    def _decode_gzip(data: bytes) -> bytes:
        if data[:2] == b"\x1f\x8b":
            return gzip.decompress(data)
        return data

    @staticmethod
    def _looks_like_sitemap(data: bytes) -> bool:
        head = data[:10000].lstrip().lower()
        return b"<urlset" in head or b"<sitemapindex" in head

    def _fetch_browser(self, url: str) -> bytes:
        """Browser fallback for sites that reject GitHub requests with HTTP 403/429/503."""
        timeout_ms = max(5000, int(self.cfg.timeout_seconds * 1000))
        with sync_playwright() as pw:
            browser = pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage"],
            )
            context = browser.new_context(
                user_agent=self.session.headers.get("User-Agent", self.cfg.user_agent),
                locale="es-ES",
                extra_http_headers={
                    "Accept": self.session.headers.get("Accept", "application/xml,text/xml,*/*"),
                    "Accept-Language": self.session.headers.get("Accept-Language", "es-ES,es;q=0.9,en;q=0.8"),
                    "Cache-Control": "no-cache",
                },
            )
            page = context.new_page()
            try:
                response = page.goto(url, wait_until="domcontentloaded", timeout=timeout_ms)
                if response is None:
                    raise RuntimeError("Playwright navigation returned no response")
                status = response.status
                body = response.body()
                body = self._decode_gzip(body)
                if 200 <= status < 300 and self._looks_like_sitemap(body):
                    return body

                # Some anti-bot pages resolve automatically after Chromium has loaded.
                page.wait_for_timeout(5000)
                response = page.goto(url, wait_until="domcontentloaded", timeout=timeout_ms)
                if response is not None:
                    status = response.status
                    body = self._decode_gzip(response.body())
                    if 200 <= status < 300 and self._looks_like_sitemap(body):
                        return body

                raise RuntimeError(f"Playwright HTTP {status}; response is not sitemap XML")
            finally:
                context.close()
                browser.close()

    def fetch_bytes(self, url: str) -> bytes:
        last_exc: Optional[Exception] = None
        browser_worthy = False
        for attempt in range(1, self.cfg.retries + 1):
            try:
                response = self.session.get(
                    url,
                    timeout=self.cfg.timeout_seconds,
                    allow_redirects=True,
                )
                if response.status_code in {403, 429, 503}:
                    browser_worthy = True
                response.raise_for_status()
                data = self._decode_gzip(response.content)
                if not self._looks_like_sitemap(data):
                    browser_worthy = True
                    raise RuntimeError(
                        f"HTTP {response.status_code} returned non-sitemap content "
                        f"({response.headers.get('content-type', '')})"
                    )
                return data
            except Exception as exc:
                last_exc = exc
                if attempt < self.cfg.retries:
                    time.sleep(self.cfg.retry_backoff_seconds * attempt)

        # The old ES pipeline used Chromium for blocked sitemap sources. Keep
        # requests as the fast path, but use a real browser when the server
        # rejects the GitHub runner or returns an anti-bot HTML page.
        if browser_worthy:
            try:
                print(f"HTTP sitemap fetch failed; trying Chromium: {url}", flush=True)
                return self._fetch_browser(url)
            except Exception as exc:
                last_exc = exc

        raise RuntimeError(f"Failed to fetch sitemap {url}: {last_exc}") from last_exc


def local_name(tag: str) -> str:
    return tag.rsplit("}", 1)[-1].lower()


def child_text(element, child_name: str) -> str:
    for child in list(element):
        if local_name(child.tag) == child_name:
            return (child.text or "").strip()
    return ""


def parse_sitemap_xml(data: bytes) -> Tuple[str, List[SitemapEntry]]:
    # Standard sitemap documents are small enough to parse as a tree, but using
    # iterparse keeps memory use predictable on large urlsets.
    import xml.etree.ElementTree as ET

    stream = io.BytesIO(data)
    context = ET.iterparse(stream, events=("start", "end"))
    root_kind = ""
    items: List[SitemapEntry] = []

    for event, elem in context:
        name = local_name(elem.tag)
        if event == "start" and not root_kind:
            if name not in {"urlset", "sitemapindex"}:
                raise ValueError(f"Unsupported XML root: {name}")
            root_kind = name
            continue

        if event != "end":
            continue

        if root_kind == "urlset" and name == "url":
            loc = child_text(elem, "loc")
            if loc:
                items.append(SitemapEntry(loc, child_text(elem, "lastmod")))
            elem.clear()
        elif root_kind == "sitemapindex" and name == "sitemap":
            loc = child_text(elem, "loc")
            if loc:
                items.append(SitemapEntry(loc, child_text(elem, "lastmod")))
            elem.clear()

    if not root_kind:
        raise ValueError("Empty sitemap XML.")
    return root_kind, items


def discover_leaf_sitemaps(
    root_url: str,
    source: SourceConfig,
    fetcher: SitemapFetcher,
    max_depth: int,
) -> Tuple[List[LeafSitemap], List[str]]:
    leaves: List[LeafSitemap] = []
    errors: List[str] = []
    visited: Set[str] = set()

    def walk(url: str, depth: int, is_root: bool) -> None:
        if url in visited:
            return
        visited.add(url)

        if depth > max_depth:
            errors.append(f"Max sitemap depth exceeded at {url}")
            return

        try:
            data = fetcher.fetch_bytes(url)
            kind, entries = parse_sitemap_xml(data)
        except Exception as exc:
            errors.append(f"{url}: {exc}")
            return

        if kind == "urlset":
            leaves.append(LeafSitemap(url=url, entries=entries))
            return

        for item in entries:
            child_url = item.url.strip()
            if not child_url:
                continue

            # The root is always fetched. Optional sitemap filters apply only
            # to discovered child sitemap URLs.
            if not regex_allows(
                child_url,
                source.sitemap_include_re,
                source.sitemap_exclude_re,
            ):
                continue
            walk(child_url, depth + 1, False)

    walk(root_url, 0, True)
    return leaves, errors


class SheetsHub:
    def __init__(self, spreadsheet_id: str, service_account_json: str):
        info = json.loads(service_account_json)
        creds = service_account.Credentials.from_service_account_info(
            info,
            scopes=["https://www.googleapis.com/auth/spreadsheets"],
        )
        self.service = build("sheets", "v4", credentials=creds, cache_discovery=False)
        self.spreadsheet_id = spreadsheet_id
        self._titles: Optional[Set[str]] = None

    def _sheet_titles(self) -> Set[str]:
        if self._titles is None:
            data = self.service.spreadsheets().get(
                spreadsheetId=self.spreadsheet_id,
                fields="sheets.properties.title",
            ).execute()
            self._titles = {
                sheet["properties"]["title"] for sheet in data.get("sheets", [])
            }
        return self._titles

    def ensure_sheet(self, title: str, headers: Sequence[str]) -> None:
        if title not in self._sheet_titles():
            self.service.spreadsheets().batchUpdate(
                spreadsheetId=self.spreadsheet_id,
                body={"requests": [{"addSheet": {"properties": {"title": title}}}]},
            ).execute()
            self._titles.add(title)

        values = self.get_values(f"{quote_sheet(title)}!1:1")
        if not values or not any(str(v).strip() for v in values[0]):
            self.update_values(
                f"{quote_sheet(title)}!A1",
                [list(headers)],
            )

    def get_values(self, a1_range: str) -> List[List[str]]:
        result = self.service.spreadsheets().values().get(
            spreadsheetId=self.spreadsheet_id,
            range=a1_range,
            valueRenderOption="UNFORMATTED_VALUE",
        ).execute()
        return result.get("values", [])

    def update_values(self, a1_range: str, rows: Sequence[Sequence[object]]) -> None:
        self.service.spreadsheets().values().update(
            spreadsheetId=self.spreadsheet_id,
            range=a1_range,
            valueInputOption="RAW",
            body={"majorDimension": "ROWS", "values": [list(r) for r in rows]},
        ).execute()

    def batch_update_values(self, updates: Sequence[Tuple[str, Sequence[object]]]) -> None:
        if not updates:
            return
        data = [
            {
                "range": a1,
                "majorDimension": "ROWS",
                "values": [list(row)],
            }
            for a1, row in updates
        ]
        self.service.spreadsheets().values().batchUpdate(
            spreadsheetId=self.spreadsheet_id,
            body={"valueInputOption": "RAW", "data": data},
        ).execute()

    def append_rows(
        self,
        title: str,
        rows: Sequence[Sequence[object]],
        chunk_size: int = 1000,
    ) -> None:
        if not rows:
            return
        for start in range(0, len(rows), chunk_size):
            chunk = [list(r) for r in rows[start : start + chunk_size]]
            self.service.spreadsheets().values().append(
                spreadsheetId=self.spreadsheet_id,
                range=f"{quote_sheet(title)}!A:A",
                valueInputOption="RAW",
                insertDataOption="INSERT_ROWS",
                body={"majorDimension": "ROWS", "values": chunk},
            ).execute()

    def find_run_row(self, run_id: str) -> Tuple[Optional[int], Optional[List[object]]]:
        rows = self.get_values(f"{quote_sheet(RUNS_SHEET)}!A:N")
        for idx, row in enumerate(rows[1:], start=2):
            if row and str(row[0]) == run_id:
                return idx, row
        return None, None

    def upsert_run(self, row: Sequence[object]) -> None:
        run_id = str(row[0])
        row_num, _ = self.find_run_row(run_id)
        if row_num:
            self.update_values(
                f"{quote_sheet(RUNS_SHEET)}!A{row_num}:N{row_num}",
                [row],
            )
        else:
            self.append_rows(RUNS_SHEET, [row])

    def load_state(
        self,
        project_id: str,
    ) -> Dict[Tuple[str, str], Tuple[int, List[object]]]:
        rows = self.get_values(f"{quote_sheet(STATE_SHEET)}!A:L")
        result: Dict[Tuple[str, str], Tuple[int, List[object]]] = {}
        for idx, row in enumerate(rows[1:], start=2):
            if len(row) < 5:
                continue
            if str(row[0]) != project_id:
                continue
            source_id = str(row[1])
            leaf_url = str(row[4])
            if source_id and leaf_url:
                result[(source_id, leaf_url)] = (idx, row)
        return result

    def upsert_states(
        self,
        state_map: Dict[Tuple[str, str], Tuple[int, List[object]]],
        new_rows: Sequence[List[object]],
    ) -> None:
        updates: List[Tuple[str, Sequence[object]]] = []
        appends: List[List[object]] = []

        for row in new_rows:
            key = (str(row[1]), str(row[4]))
            found = state_map.get(key)
            if found:
                row_num = found[0]
                updates.append(
                    (f"{quote_sheet(STATE_SHEET)}!A{row_num}:L{row_num}", row)
                )
            else:
                appends.append(row)

        self.batch_update_values(updates)
        self.append_rows(STATE_SHEET, appends)

    def load_project_history(
        self,
        project_sheet: str,
        source_id: Optional[str] = None,
        run_id: Optional[str] = None,
    ) -> Set[str]:
        # Called only on fallback/recovery paths, not during the normal
        # append-only monthly path.
        rows = self.get_values(f"{quote_sheet(project_sheet)}!A:L")
        urls: Set[str] = set()
        for row in rows[1:]:
            if len(row) < 10:
                continue
            if source_id is not None and str(row[4]) != source_id:
                continue
            if run_id is not None and str(row[0]) != run_id:
                continue
            url = str(row[7]).strip()
            if url:
                urls.add(url)
        return urls


def normalize_payload(payload: dict, env_run_id: str) -> Tuple[str, str, str, str, List[SourceConfig], EngineConfig]:
    if int(payload.get("schema_version", 0)) != SCHEMA_VERSION:
        raise ValueError(
            f"Unsupported schema_version={payload.get('schema_version')!r}; "
            f"expected {SCHEMA_VERSION}."
        )

    run_id = str(payload.get("run_id") or env_run_id or "").strip()
    project_id = str(payload.get("project_id") or "").strip()
    geo = str(payload.get("geo") or project_id).strip()
    hub_id = str(payload.get("hub_spreadsheet_id") or "").strip()

    if not run_id:
        raise ValueError("run_id is required.")
    if env_run_id and run_id != env_run_id:
        raise ValueError("run_id in payload does not match workflow input.")
    if not project_id:
        raise ValueError("project_id is required.")
    if not hub_id:
        raise ValueError("hub_spreadsheet_id is required.")

    sources_raw = payload.get("sources")
    if not isinstance(sources_raw, list) or not sources_raw:
        raise ValueError("sources must be a non-empty array.")

    sources = [SourceConfig.from_dict(item) for item in sources_raw]
    source_ids = [s.source_id for s in sources]
    if len(source_ids) != len(set(source_ids)):
        raise ValueError("source_id values must be unique within a project.")

    engine = EngineConfig.from_dict(payload.get("engine") or {})
    return run_id, project_id, geo, hub_id, sources, engine


def state_value(row: Sequence[object], index: int, default: str = "") -> str:
    return str(row[index]) if len(row) > index and row[index] is not None else default


def state_int(row: Sequence[object], index: int, default: int = 0) -> int:
    try:
        return int(float(row[index])) if len(row) > index and row[index] != "" else default
    except Exception:
        return default


def select_new_entries(
    entries: Sequence[SitemapEntry],
    previous_state: Optional[Sequence[object]],
    config_hash: str,
) -> Tuple[List[SitemapEntry], str]:
    """
    Returns candidate entries and mode.

    APPEND_SAFE:
      The previous full ordered URL list is exactly the current prefix ending
      at the previous last URL. Therefore only entries after that anchor can be
      new.

    FIRST:
      No checkpoint exists.

    FALLBACK:
      Reorder, insertion, deletion, filter/config change, or missing anchor.
      Caller must diff current relevant URLs against Hub history.
    """
    if previous_state is None:
        return list(entries), "FIRST"

    prev_count = state_int(previous_state, 5, 0)
    prev_last_url = state_value(previous_state, 6)
    prev_hash = state_value(previous_state, 7)
    prev_config_hash = state_value(previous_state, 8)

    if prev_config_hash != config_hash:
        return list(entries), "FALLBACK"

    if not prev_last_url or prev_count < 0 or not prev_hash:
        return list(entries), "FALLBACK"

    urls = [e.url for e in entries]
    try:
        anchor_index = len(urls) - 1 - urls[::-1].index(prev_last_url)
    except ValueError:
        return list(entries), "FALLBACK"

    prefix = urls[: anchor_index + 1]
    if len(prefix) != prev_count:
        return list(entries), "FALLBACK"

    if ordered_url_hash(prefix) != prev_hash:
        return list(entries), "FALLBACK"

    return list(entries[anchor_index + 1 :]), "APPEND_SAFE"


def build_state_row(
    project_id: str,
    source: SourceConfig,
    leaf: LeafSitemap,
    run_id: str,
    error: str = "",
) -> List[object]:
    urls = [entry.url for entry in leaf.entries]
    return [
        project_id,
        source.source_id,
        source.site_url,
        source.sitemap_url,
        leaf.url,
        len(urls),
        urls[-1] if urls else "",
        ordered_url_hash(urls),
        source.config_hash(),
        run_id,
        utc_now(),
        error[:4000],
    ]


def main() -> int:
    env_run_id = os.environ.get("PARSER_RUN_ID", "").strip()
    encoded = os.environ.get("PARSER_PAYLOAD_GZIP_B64", "").strip()
    service_account_json = os.environ.get("GOOGLE_SERVICE_ACCOUNT_JSON", "").strip()

    if not service_account_json:
        print("ERROR: GOOGLE_SERVICE_ACCOUNT_JSON secret is missing.", file=sys.stderr)
        return 2

    payload = decode_payload(encoded)
    run_id, project_id, geo, hub_id, sources, engine = normalize_payload(
        payload, env_run_id
    )

    project_sheet = "URLS__" + safe_project_slug(project_id)
    hub = SheetsHub(hub_id, service_account_json)
    hub.ensure_sheet(RUNS_SHEET, RUN_HEADERS)
    hub.ensure_sheet(STATE_SHEET, STATE_HEADERS)
    hub.ensure_sheet(project_sheet, URL_HEADERS)

    started_at = utc_now()
    enabled_sources = [s for s in sources if s.enabled]

    existing_run_row_num, existing_run_row = hub.find_run_row(run_id)
    existing_run_urls: Set[str] = set()
    if existing_run_row_num:
        # Makes GitHub "Re-run jobs" idempotent for a partially completed run.
        existing_run_urls = hub.load_project_history(project_sheet, run_id=run_id)

    def update_run(
        phase: str,
        current_source: str,
        sources_done: int,
        new_urls: int,
        sitemap_files: int,
        errors: int,
        message: str,
        finished: bool = False,
    ) -> None:
        hub.upsert_run([
            run_id,
            project_id,
            geo,
            phase,
            current_source,
            sources_done,
            len(enabled_sources),
            new_urls,
            sitemap_files,
            errors,
            started_at,
            utc_now(),
            utc_now() if finished else "",
            message[:45000],
        ])

    update_run("STARTING", "", 0, 0, 0, 0, "Payload accepted.")

    state_map = hub.load_state(project_id)
    fetcher = SitemapFetcher(engine)

    total_new = 0
    total_leaf_files = 0
    all_errors: List[str] = []
    emitted_this_run: Set[str] = set(existing_run_urls)
    history_cache: Dict[str, Set[str]] = {}

    for source_index, source in enumerate(enabled_sources, start=1):
        update_run(
            "FETCHING_SITEMAPS",
            source.source_id,
            source_index - 1,
            total_new,
            total_leaf_files,
            len(all_errors),
            f"Reading sitemap tree for {source.source_id}.",
        )

        leaves: List[LeafSitemap] = []
        source_errors: List[str] = []
        for root_sitemap_url in split_sitemap_urls(source.sitemap_url):
            root_leaves, root_errors = discover_leaf_sitemaps(
                root_sitemap_url,
                source,
                fetcher,
                engine.max_sitemap_depth,
            )
            leaves.extend(root_leaves)
            source_errors.extend(root_errors)
        total_leaf_files += len(leaves)
        all_errors.extend(f"{source.source_id}: {err}" for err in source_errors)

        source_has_prior_state = any(
            key[0] == source.source_id for key in state_map.keys()
        )
        source_rows: List[List[object]] = []
        source_state_rows: List[List[object]] = []
        source_new = 0

        for leaf in leaves:
            prev = state_map.get((source.source_id, leaf.url))
            previous_state = prev[1] if prev else None
            candidates, mode = select_new_entries(
                leaf.entries,
                previous_state,
                source.config_hash(),
            )

            relevant_current = [
                entry
                for entry in leaf.entries
                if regex_allows(
                    entry.url,
                    source.url_include_re,
                    source.url_exclude_re,
                )
            ]

            if mode == "APPEND_SAFE":
                candidate_entries = [
                    entry
                    for entry in candidates
                    if regex_allows(
                        entry.url,
                        source.url_include_re,
                        source.url_exclude_re,
                    )
                ]
            elif mode == "FIRST" and not source_has_prior_state:
                # True first run of this source: no history read is necessary.
                candidate_entries = relevant_current
            else:
                # Safe recovery path. This is intentionally NOT the normal
                # monthly path. It is used when sitemap ordering/structure or
                # relevant config changed, or a new leaf appeared later.
                if source.source_id not in history_cache:
                    history_cache[source.source_id] = hub.load_project_history(
                        project_sheet,
                        source_id=source.source_id,
                    )
                seen = history_cache[source.source_id]
                candidate_entries = [
                    entry for entry in relevant_current if entry.url not in seen
                ]

            for entry in candidate_entries:
                if entry.url in emitted_this_run:
                    continue
                emitted_this_run.add(entry.url)
                source_rows.append([
                    run_id,
                    utc_now(),
                    project_id,
                    geo,
                    source.source_id,
                    source.site_url,
                    source.role,
                    entry.url,
                    entry.lastmod,
                    leaf.url,
                    "",
                    "",
                ])
                source_new += 1

            source_state_rows.append(
                build_state_row(project_id, source, leaf, run_id)
            )

        update_run(
            "WRITING_URLS",
            source.source_id,
            source_index - 1,
            total_new,
            total_leaf_files,
            len(all_errors),
            f"Writing {source_new} new URL(s) for {source.source_id}.",
        )

        # Append URL rows before advancing checkpoints. If a runner is killed
        # between these operations, a GitHub rerun with the same run_id is
        # de-duplicated by existing_run_urls.
        hub.append_rows(project_sheet, source_rows)
        hub.upsert_states(state_map, source_state_rows)

        # Keep in-memory state map current for any repeated leaf URL later.
        for row in source_state_rows:
            state_map[(str(row[1]), str(row[4]))] = (-1, row)

        if source.source_id in history_cache:
            history_cache[source.source_id].update(
                str(row[7]) for row in source_rows
            )

        total_new += source_new
        update_run(
            "SOURCE_DONE",
            source.source_id,
            source_index,
            total_new,
            total_leaf_files,
            len(all_errors),
            f"{source.source_id}: {source_new} new URL(s).",
        )

    phase = "PARTIAL" if all_errors else "DONE"
    if all_errors:
        preview = " | ".join(all_errors[:10])
        if len(all_errors) > 10:
            preview += f" | ... and {len(all_errors) - 10} more"
        message = (
            f"Completed with {len(all_errors)} sitemap error(s). "
            f"New URLs={total_new}. {preview}"
        )
    else:
        message = f"Completed successfully. New URLs={total_new}."

    update_run(
        phase,
        "",
        len(enabled_sources),
        total_new,
        total_leaf_files,
        len(all_errors),
        message,
        finished=True,
    )

    print(message)
    # PARTIAL is a completed engine run; details are recorded in the Hub.
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except SystemExit:
        raise
    except Exception as exc:
        print(f"FATAL: {exc}", file=sys.stderr)
        traceback.print_exc()
        raise SystemExit(1)
