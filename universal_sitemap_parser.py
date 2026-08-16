#!/usr/bin/env python3
"""
Universal Sitemap Engine V2

GitHub contains ZERO GEO/domain/competitor-specific rules.
Everything operational is supplied by the Google Sheet as a compressed JSON payload.

The engine:
- supports one GEO or multiple GEOs/projects in one run;
- supports direct <urlset>;
- supports <sitemapindex> recursively, including nested indexes;
- supports raw .xml.gz/gzip sitemap responses;
- applies only generic regex filters supplied by the Sheet;
- writes all GEOs/projects into one central Parser Hub;
- stores per-leaf-sitemap checkpoints;
- uses no lastmod dates to decide freshness;
- on normal monthly runs reads only the tail after the previous checkpoint;
- if sitemap order/structure/config changed, falls back to a safe URL-history diff
  for that affected source, so inserted URLs are not lost.

Required GitHub repository secret:
    GOOGLE_SERVICE_ACCOUNT_JSON

Payload schema_version = 2:

{
  "schema_version": 2,
  "run_id": "RUN_...",
  "hub_spreadsheet_id": "...",
  "sources": [
    {
      "project_id": "FR",
      "geo": "FR",
      "source_id": "FR__JEUX_CA",
      "site_url": "https://jeux.ca",
      "sitemap_url": "https://jeux.ca/sitemap_index.xml",
      "role": "competitor",
      "enabled": true,
      "url_include_regex": "^https://(?:www\\.)?jeux\\.ca/",
      "url_exclude_regex": "/en/|/author/|/tag/|/feed(?:/|$)",
      "leaf_sitemap_include_regex": "",
      "sitemap_exclude_regex": ""
    }
  ],
  "engine": {
    "timeout_seconds": 30,
    "retries": 3,
    "retry_backoff_seconds": 2,
    "max_sitemap_depth": 10,
    "user_agent": "Mozilla/5.0 ...",
    "request_headers": {}
  }
}

The Hub workbook is created/maintained automatically:
    _GP_RUNS
    _GP_STATE
    _GP_URL_QUEUE

Important:
leaf_sitemap_include_regex is applied only to an actual <urlset> sitemap,
not to intermediate <sitemapindex> URLs. This allows a global root sitemap
to lead through several generic indexes before reaching /es/, /fr/, etc.
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
from typing import Dict, List, Optional, Sequence, Set, Tuple

import requests
from google.oauth2 import service_account
from googleapiclient.discovery import build


SCHEMA_VERSION = 2

RUNS_SHEET = "_GP_RUNS"
STATE_SHEET = "_GP_STATE"
QUEUE_SHEET = "_GP_URL_QUEUE"

RUN_HEADERS = [
    "Run ID", "Phase", "Current Project", "Current GEO", "Current Source",
    "Sources Done", "Sources Total", "New URLs", "Sitemap Files",
    "Errors", "Started At", "Updated At", "Finished At", "Message",
]

STATE_HEADERS = [
    "Project ID", "GEO", "Source ID", "Site URL", "Root Sitemap",
    "Leaf Sitemap", "URL Count", "Last URL", "Ordered Hash", "Config Hash",
    "Last Run ID", "Updated At", "Last Error",
]

QUEUE_HEADERS = [
    "Run ID", "Exported At", "Project ID", "GEO", "Source ID",
    "Site URL", "Role", "URL", "Last Modified", "Source Sitemap",
    "Processed", "Analysis Run ID",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def ordered_url_hash(urls: Sequence[str]) -> str:
    h = hashlib.sha256()
    for url in urls:
        raw = url.encode("utf-8")
        h.update(str(len(raw)).encode("ascii"))
        h.update(b":")
        h.update(raw)
        h.update(b"\n")
    return h.hexdigest()


def decode_payload(encoded: str) -> dict:
    if not encoded:
        raise ValueError("PARSER_PAYLOAD_GZIP_B64 is empty.")
    padded = encoded + "=" * (-len(encoded) % 4)
    compressed = base64.urlsafe_b64decode(padded.encode("ascii"))
    return json.loads(gzip.decompress(compressed).decode("utf-8"))


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
    project_id: str
    geo: str
    source_id: str
    site_url: str
    sitemap_url: str
    role: str
    enabled: bool

    url_include_text: str
    url_exclude_text: str
    leaf_sitemap_include_text: str
    sitemap_exclude_text: str

    url_include_re: Optional[re.Pattern] = None
    url_exclude_re: Optional[re.Pattern] = None
    leaf_sitemap_include_re: Optional[re.Pattern] = None
    sitemap_exclude_re: Optional[re.Pattern] = None

    @classmethod
    def from_dict(cls, data: dict) -> "SourceConfig":
        project_id = str(data.get("project_id") or "").strip()
        geo = str(data.get("geo") or project_id).strip()
        source_id = str(data.get("source_id") or "").strip()
        site_url = str(data.get("site_url") or "").strip()
        sitemap_url = str(data.get("sitemap_url") or "").strip()
        role = str(data.get("role") or "competitor").strip().lower()

        raw_enabled = data.get("enabled", True)
        enabled = (
            raw_enabled
            if isinstance(raw_enabled, bool)
            else str(raw_enabled).strip().lower() not in {"0", "false", "no", "off", ""}
        )

        missing = []
        if not project_id:
            missing.append("project_id")
        if not geo:
            missing.append("geo")
        if not source_id:
            missing.append("source_id")
        if not site_url:
            missing.append("site_url")
        if not sitemap_url:
            missing.append("sitemap_url")
        if missing:
            raise ValueError(
                f"Source is missing required field(s): {', '.join(missing)}. Source={data!r}"
            )

        ui = str(data.get("url_include_regex") or "").strip()
        ue = str(data.get("url_exclude_regex") or "").strip()
        li = str(data.get("leaf_sitemap_include_regex") or "").strip()
        se = str(data.get("sitemap_exclude_regex") or "").strip()

        return cls(
            project_id=project_id,
            geo=geo,
            source_id=source_id,
            site_url=site_url,
            sitemap_url=sitemap_url,
            role=role,
            enabled=enabled,
            url_include_text=ui,
            url_exclude_text=ue,
            leaf_sitemap_include_text=li,
            sitemap_exclude_text=se,
            url_include_re=compile_optional_regex(ui, f"{source_id}.url_include_regex"),
            url_exclude_re=compile_optional_regex(ue, f"{source_id}.url_exclude_regex"),
            leaf_sitemap_include_re=compile_optional_regex(
                li, f"{source_id}.leaf_sitemap_include_regex"
            ),
            sitemap_exclude_re=compile_optional_regex(
                se, f"{source_id}.sitemap_exclude_regex"
            ),
        )

    def config_hash(self) -> str:
        normalized = json.dumps(
            {
                "project_id": self.project_id,
                "geo": self.geo,
                "site_url": self.site_url,
                "sitemap_url": self.sitemap_url,
                "url_include_regex": self.url_include_text,
                "url_exclude_regex": self.url_exclude_text,
                "leaf_sitemap_include_regex": self.leaf_sitemap_include_text,
                "sitemap_exclude_regex": self.sitemap_exclude_text,
            },
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


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
            retry_backoff_seconds=max(
                0.0, float(data.get("retry_backoff_seconds", 2))
            ),
            max_sitemap_depth=max(1, int(data.get("max_sitemap_depth", 10))),
            user_agent=str(
                data.get("user_agent")
                or "Mozilla/5.0 (compatible; UniversalSitemapEngine/2.0)"
            ),
            request_headers={str(k): str(v) for k, v in headers.items()},
        )


class SitemapFetcher:
    def __init__(self, cfg: EngineConfig):
        self.cfg = cfg
        self.session = requests.Session()
        self.session.headers.update(
            {"User-Agent": cfg.user_agent, **cfg.request_headers}
        )

    def fetch_bytes(self, url: str) -> bytes:
        last_exc: Optional[Exception] = None

        for attempt in range(1, self.cfg.retries + 1):
            try:
                response = self.session.get(
                    url,
                    timeout=self.cfg.timeout_seconds,
                    allow_redirects=True,
                )
                response.raise_for_status()

                data = response.content
                if data[:2] == b"\x1f\x8b":
                    data = gzip.decompress(data)

                return data

            except Exception as exc:
                last_exc = exc
                if attempt >= self.cfg.retries:
                    break
                time.sleep(self.cfg.retry_backoff_seconds * attempt)

        raise RuntimeError(f"Failed to fetch sitemap {url}: {last_exc}") from last_exc


def local_name(tag: str) -> str:
    return tag.rsplit("}", 1)[-1].lower()


def child_text(element, name: str) -> str:
    for child in list(element):
        if local_name(child.tag) == name:
            return (child.text or "").strip()
    return ""


def parse_sitemap_xml(data: bytes) -> Tuple[str, List[SitemapEntry]]:
    import xml.etree.ElementTree as ET

    stream = io.BytesIO(data)
    context = ET.iterparse(stream, events=("start", "end"))

    root_kind = ""
    items: List[SitemapEntry] = []

    for event, elem in context:
        name = local_name(elem.tag)

        if event == "start" and not root_kind:
            if name not in {"urlset", "sitemapindex"}:
                raise ValueError(f"Unsupported sitemap XML root: {name}")
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

        if (
            not is_root
            and source.sitemap_exclude_re
            and source.sitemap_exclude_re.search(url)
        ):
            return

        try:
            data = fetcher.fetch_bytes(url)
            kind, entries = parse_sitemap_xml(data)
        except Exception as exc:
            errors.append(f"{url}: {exc}")
            return

        if kind == "urlset":
            if (
                source.leaf_sitemap_include_re
                and not source.leaf_sitemap_include_re.search(url)
            ):
                return

            leaves.append(LeafSitemap(url=url, entries=entries))
            return

        for entry in entries:
            child_url = entry.url.strip()
            if child_url:
                walk(child_url, depth + 1, False)

    walk(source.sitemap_url, 0, True)
    return leaves, errors


class SheetsHub:
    def __init__(self, spreadsheet_id: str, service_account_json: str):
        info = json.loads(service_account_json)

        credentials = service_account.Credentials.from_service_account_info(
            info,
            scopes=["https://www.googleapis.com/auth/spreadsheets"],
        )

        self.service = build(
            "sheets",
            "v4",
            credentials=credentials,
            cache_discovery=False,
        )
        self.spreadsheet_id = spreadsheet_id
        self._titles: Optional[Set[str]] = None

    @staticmethod
    def q(title: str) -> str:
        return "'" + title.replace("'", "''") + "'"

    def sheet_titles(self) -> Set[str]:
        if self._titles is None:
            result = self.service.spreadsheets().get(
                spreadsheetId=self.spreadsheet_id,
                fields="sheets.properties.title",
            ).execute()

            self._titles = {
                x["properties"]["title"]
                for x in result.get("sheets", [])
            }

        return self._titles

    def ensure_sheet(self, title: str, headers: Sequence[str]) -> None:
        if title not in self.sheet_titles():
            self.service.spreadsheets().batchUpdate(
                spreadsheetId=self.spreadsheet_id,
                body={
                    "requests": [
                        {
                            "addSheet": {
                                "properties": {
                                    "title": title
                                }
                            }
                        }
                    ]
                },
            ).execute()

            self._titles.add(title)

        first_row = self.get_values(f"{self.q(title)}!1:1")

        if not first_row or not any(str(x).strip() for x in first_row[0]):
            self.update_values(
                f"{self.q(title)}!A1",
                [list(headers)],
            )

    def get_values(self, a1_range: str) -> List[List[object]]:
        result = self.service.spreadsheets().values().get(
            spreadsheetId=self.spreadsheet_id,
            range=a1_range,
            valueRenderOption="UNFORMATTED_VALUE",
        ).execute()

        return result.get("values", [])

    def update_values(
        self,
        a1_range: str,
        rows: Sequence[Sequence[object]],
    ) -> None:
        self.service.spreadsheets().values().update(
            spreadsheetId=self.spreadsheet_id,
            range=a1_range,
            valueInputOption="RAW",
            body={
                "majorDimension": "ROWS",
                "values": [list(x) for x in rows],
            },
        ).execute()

    def append_rows(
        self,
        sheet: str,
        rows: Sequence[Sequence[object]],
        chunk_size: int = 1000,
    ) -> None:
        if not rows:
            return

        for start in range(0, len(rows), chunk_size):
            chunk = [
                list(x)
                for x in rows[start:start + chunk_size]
            ]

            self.service.spreadsheets().values().append(
                spreadsheetId=self.spreadsheet_id,
                range=f"{self.q(sheet)}!A:A",
                valueInputOption="RAW",
                insertDataOption="INSERT_ROWS",
                body={
                    "majorDimension": "ROWS",
                    "values": chunk,
                },
            ).execute()

    def batch_update_rows(
        self,
        sheet: str,
        rows: Sequence[Tuple[int, Sequence[object]]],
        last_col: str,
    ) -> None:
        if not rows:
            return

        data = []

        for row_number, row in rows:
            data.append(
                {
                    "range": (
                        f"{self.q(sheet)}!"
                        f"A{row_number}:{last_col}{row_number}"
                    ),
                    "majorDimension": "ROWS",
                    "values": [list(row)],
                }
            )

        self.service.spreadsheets().values().batchUpdate(
            spreadsheetId=self.spreadsheet_id,
            body={
                "valueInputOption": "RAW",
                "data": data,
            },
        ).execute()

    def find_run(
        self,
        run_id: str,
    ) -> Tuple[Optional[int], Optional[List[object]]]:
        rows = self.get_values(
            f"{self.q(RUNS_SHEET)}!A:N"
        )

        for idx, row in enumerate(rows[1:], start=2):
            if row and str(row[0]) == run_id:
                return idx, row

        return None, None

    def upsert_run(self, row: Sequence[object]) -> None:
        row_number, _ = self.find_run(str(row[0]))

        if row_number:
            self.update_values(
                f"{self.q(RUNS_SHEET)}!A{row_number}:N{row_number}",
                [row],
            )
        else:
            self.append_rows(
                RUNS_SHEET,
                [row],
            )

    def load_state(
        self,
    ) -> Dict[Tuple[str, str, str], Tuple[int, List[object]]]:
        rows = self.get_values(
            f"{self.q(STATE_SHEET)}!A:M"
        )

        result: Dict[
            Tuple[str, str, str],
            Tuple[int, List[object]]
        ] = {}

        for idx, row in enumerate(rows[1:], start=2):
            if len(row) < 6:
                continue

            project_id = str(row[0])
            source_id = str(row[2])
            leaf_sitemap = str(row[5])

            if project_id and source_id and leaf_sitemap:
                result[
                    (
                        project_id,
                        source_id,
                        leaf_sitemap,
                    )
                ] = (idx, row)

        return result

    def upsert_state_rows(
        self,
        state_map: Dict[
            Tuple[str, str, str],
            Tuple[int, List[object]]
        ],
        rows: Sequence[List[object]],
    ) -> None:
        updates: List[
            Tuple[int, Sequence[object]]
        ] = []
        appends: List[List[object]] = []

        for row in rows:
            key = (
                str(row[0]),
                str(row[2]),
                str(row[5]),
            )

            old = state_map.get(key)

            if old and old[0] > 0:
                updates.append(
                    (
                        old[0],
                        row,
                    )
                )
            else:
                appends.append(row)

        self.batch_update_rows(
            STATE_SHEET,
            updates,
            "M",
        )

        self.append_rows(
            STATE_SHEET,
            appends,
        )

    def load_queue_history(
        self,
        project_id: Optional[str] = None,
        source_id: Optional[str] = None,
        run_id: Optional[str] = None,
    ) -> Set[Tuple[str, str, str]]:
        rows = self.get_values(
            f"{self.q(QUEUE_SHEET)}!A:L"
        )

        result: Set[
            Tuple[str, str, str]
        ] = set()

        for row in rows[1:]:
            if len(row) < 10:
                continue

            row_run_id = str(row[0])
            row_project_id = str(row[2])
            row_source_id = str(row[4])
            row_url = str(row[7]).strip()

            if run_id is not None and row_run_id != run_id:
                continue

            if (
                project_id is not None
                and row_project_id != project_id
            ):
                continue

            if (
                source_id is not None
                and row_source_id != source_id
            ):
                continue

            if (
                row_project_id
                and row_source_id
                and row_url
            ):
                result.add(
                    (
                        row_project_id,
                        row_source_id,
                        row_url,
                    )
                )

        return result


def normalize_payload(
    payload: dict,
    env_run_id: str,
) -> Tuple[str, str, List[SourceConfig], EngineConfig]:
    if int(payload.get("schema_version", 0)) != SCHEMA_VERSION:
        raise ValueError(
            f"Unsupported schema_version="
            f"{payload.get('schema_version')!r}; "
            f"expected {SCHEMA_VERSION}."
        )

    run_id = str(
        payload.get("run_id")
        or env_run_id
        or ""
    ).strip()

    hub_spreadsheet_id = str(
        payload.get("hub_spreadsheet_id")
        or ""
    ).strip()

    if not run_id:
        raise ValueError("run_id is required.")

    if env_run_id and env_run_id != run_id:
        raise ValueError(
            "run_id in payload does not match workflow input."
        )

    if not hub_spreadsheet_id:
        raise ValueError(
            "hub_spreadsheet_id is required."
        )

    raw_sources = payload.get("sources")

    if (
        not isinstance(raw_sources, list)
        or not raw_sources
    ):
        raise ValueError(
            "sources must be a non-empty array."
        )

    sources = [
        SourceConfig.from_dict(x)
        for x in raw_sources
    ]

    stable_keys = [
        (
            x.project_id,
            x.source_id,
        )
        for x in sources
    ]

    if len(stable_keys) != len(set(stable_keys)):
        raise ValueError(
            "Within one payload, "
            "(project_id, source_id) pairs must be unique."
        )

    engine = EngineConfig.from_dict(
        payload.get("engine") or {}
    )

    return (
        run_id,
        hub_spreadsheet_id,
        sources,
        engine,
    )


def state_text(
    row: Sequence[object],
    idx: int,
) -> str:
    if (
        len(row) <= idx
        or row[idx] is None
    ):
        return ""

    return str(row[idx])


def state_int(
    row: Sequence[object],
    idx: int,
) -> int:
    try:
        if (
            len(row) <= idx
            or row[idx] == ""
        ):
            return 0

        return int(
            float(row[idx])
        )

    except Exception:
        return 0


def choose_increment(
    entries: Sequence[SitemapEntry],
    old_state: Optional[Sequence[object]],
    current_config_hash: str,
) -> Tuple[List[SitemapEntry], str]:
    """
    STATE columns:
      6 URL Count
      7 Last URL
      8 Ordered Hash
      9 Config Hash

    FIRST:
      No checkpoint for this leaf.

    APPEND_SAFE:
      The old ordered URL sequence is still exactly the current prefix.
      Only the tail after the previous Last URL can be new.

    FALLBACK:
      Reorder/insertion/deletion/rewrite/config change/missing anchor.
      Caller performs a source-scoped history diff.
    """

    if old_state is None:
        return list(entries), "FIRST"

    old_count = state_int(
        old_state,
        6,
    )

    old_last_url = state_text(
        old_state,
        7,
    )

    old_ordered_hash = state_text(
        old_state,
        8,
    )

    old_config_hash = state_text(
        old_state,
        9,
    )

    if old_config_hash != current_config_hash:
        return list(entries), "FALLBACK"

    if (
        not old_last_url
        or old_count < 0
        or not old_ordered_hash
    ):
        return list(entries), "FALLBACK"

    current_urls = [
        x.url
        for x in entries
    ]

    try:
        reverse_index = (
            current_urls[::-1]
            .index(old_last_url)
        )

        anchor_index = (
            len(current_urls)
            - 1
            - reverse_index
        )

    except ValueError:
        return list(entries), "FALLBACK"

    prefix = current_urls[
        :anchor_index + 1
    ]

    if len(prefix) != old_count:
        return list(entries), "FALLBACK"

    if (
        ordered_url_hash(prefix)
        != old_ordered_hash
    ):
        return list(entries), "FALLBACK"

    return (
        list(
            entries[
                anchor_index + 1:
            ]
        ),
        "APPEND_SAFE",
    )


def make_state_row(
    source: SourceConfig,
    leaf: LeafSitemap,
    run_id: str,
    error: str = "",
) -> List[object]:
    urls = [
        x.url
        for x in leaf.entries
    ]

    return [
        source.project_id,
        source.geo,
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
    env_run_id = os.environ.get(
        "PARSER_RUN_ID",
        "",
    ).strip()

    encoded_payload = os.environ.get(
        "PARSER_PAYLOAD_GZIP_B64",
        "",
    ).strip()

    service_account_json = os.environ.get(
        "GOOGLE_SERVICE_ACCOUNT_JSON",
        "",
    ).strip()

    if not service_account_json:
        print(
            "ERROR: GOOGLE_SERVICE_ACCOUNT_JSON "
            "repository secret is missing.",
            file=sys.stderr,
        )
        return 2

    payload = decode_payload(
        encoded_payload
    )

    (
        run_id,
        hub_spreadsheet_id,
        sources,
        engine,
    ) = normalize_payload(
        payload,
        env_run_id,
    )

    enabled_sources = [
        x
        for x in sources
        if x.enabled
    ]

    if not enabled_sources:
        raise ValueError(
            "Payload contains no enabled sources."
        )

    hub = SheetsHub(
        hub_spreadsheet_id,
        service_account_json,
    )

    hub.ensure_sheet(
        RUNS_SHEET,
        RUN_HEADERS,
    )

    hub.ensure_sheet(
        STATE_SHEET,
        STATE_HEADERS,
    )

    hub.ensure_sheet(
        QUEUE_SHEET,
        QUEUE_HEADERS,
    )

    started_at = utc_now()

    existing_run_row, _ = hub.find_run(
        run_id
    )

    emitted: Set[
        Tuple[str, str, str]
    ] = set()

    if existing_run_row:
        emitted.update(
            hub.load_queue_history(
                run_id=run_id
            )
        )

    state_map = hub.load_state()

    fetcher = SitemapFetcher(
        engine
    )

    total_new_urls = 0
    total_leaf_files = 0
    errors: List[str] = []

    history_cache: Dict[
        Tuple[str, str],
        Set[Tuple[str, str, str]]
    ] = {}

    def update_run(
        phase: str,
        source: Optional[SourceConfig],
        sources_done: int,
        message: str,
        finished: bool = False,
    ) -> None:
        hub.upsert_run(
            [
                run_id,
                phase,
                source.project_id
                if source else "",
                source.geo
                if source else "",
                source.source_id
                if source else "",
                sources_done,
                len(enabled_sources),
                total_new_urls,
                total_leaf_files,
                len(errors),
                started_at,
                utc_now(),
                utc_now()
                if finished else "",
                message[:45000],
            ]
        )

    update_run(
        "STARTING",
        None,
        0,
        "Payload accepted.",
    )

    try:
        for source_index, source in enumerate(
            enabled_sources,
            start=1,
        ):
            update_run(
                "FETCHING_SITEMAPS",
                source,
                source_index - 1,
                (
                    "Reading sitemap tree for "
                    f"{source.project_id}/"
                    f"{source.source_id}."
                ),
            )

            (
                leaves,
                source_errors,
            ) = discover_leaf_sitemaps(
                source,
                fetcher,
                engine.max_sitemap_depth,
            )

            total_leaf_files += len(
                leaves
            )

            errors.extend(
                (
                    f"{source.project_id}/"
                    f"{source.source_id}: "
                    f"{error}"
                )
                for error in source_errors
            )

            source_has_state = any(
                (
                    key[0]
                    == source.project_id
                    and key[1]
                    == source.source_id
                )
                for key in state_map
            )

            output_rows: List[
                List[object]
            ] = []

            state_rows: List[
                List[object]
            ] = []

            source_new_urls = 0

            current_config_hash = (
                source.config_hash()
            )

            for leaf in leaves:
                state_key = (
                    source.project_id,
                    source.source_id,
                    leaf.url,
                )

                old_state_item = (
                    state_map.get(
                        state_key
                    )
                )

                old_state_row = (
                    old_state_item[1]
                    if old_state_item
                    else None
                )

                (
                    candidates,
                    increment_mode,
                ) = choose_increment(
                    leaf.entries,
                    old_state_row,
                    current_config_hash,
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

                if (
                    increment_mode
                    == "APPEND_SAFE"
                ):
                    candidate_entries = [
                        entry
                        for entry in candidates
                        if regex_allows(
                            entry.url,
                            source.url_include_re,
                            source.url_exclude_re,
                        )
                    ]

                elif (
                    increment_mode
                    == "FIRST"
                    and not source_has_state
                ):
                    candidate_entries = (
                        relevant_current
                    )

                else:
                    cache_key = (
                        source.project_id,
                        source.source_id,
                    )

                    if (
                        cache_key
                        not in history_cache
                    ):
                        history_cache[
                            cache_key
                        ] = hub.load_queue_history(
                            project_id=source.project_id,
                            source_id=source.source_id,
                        )

                    seen = history_cache[
                        cache_key
                    ]

                    candidate_entries = [
                        entry
                        for entry
                        in relevant_current
                        if (
                            source.project_id,
                            source.source_id,
                            entry.url,
                        )
                        not in seen
                    ]

                for entry in candidate_entries:
                    url_key = (
                        source.project_id,
                        source.source_id,
                        entry.url,
                    )

                    if url_key in emitted:
                        continue

                    emitted.add(
                        url_key
                    )

                    output_rows.append(
                        [
                            run_id,
                            utc_now(),
                            source.project_id,
                            source.geo,
                            source.source_id,
                            source.site_url,
                            source.role,
                            entry.url,
                            entry.lastmod,
                            leaf.url,
                            "",
                            "",
                        ]
                    )

                    source_new_urls += 1

                state_rows.append(
                    make_state_row(
                        source,
                        leaf,
                        run_id,
                    )
                )

            update_run(
                "WRITING_URLS",
                source,
                source_index - 1,
                (
                    f"Writing "
                    f"{source_new_urls} "
                    f"new URL(s)."
                ),
            )

            hub.append_rows(
                QUEUE_SHEET,
                output_rows,
            )

            hub.upsert_state_rows(
                state_map,
                state_rows,
            )

            for row in state_rows:
                state_map[
                    (
                        str(row[0]),
                        str(row[2]),
                        str(row[5]),
                    )
                ] = (-1, row)

            cache_key = (
                source.project_id,
                source.source_id,
            )

            if (
                cache_key
                in history_cache
            ):
                history_cache[
                    cache_key
                ].update(
                    (
                        str(row[2]),
                        str(row[4]),
                        str(row[7]),
                    )
                    for row
                    in output_rows
                )

            total_new_urls += (
                source_new_urls
            )

            update_run(
                "SOURCE_DONE",
                source,
                source_index,
                (
                    f"{source.project_id}/"
                    f"{source.source_id}: "
                    f"{source_new_urls} "
                    f"new URL(s)."
                ),
            )

    except Exception as exc:
        message = (
            f"Fatal processing error: "
            f"{exc}"
        )

        try:
            update_run(
                "ERROR",
                None,
                0,
                message,
                finished=True,
            )
        except Exception:
            pass

        raise

    final_phase = (
        "PARTIAL"
        if errors
        else "DONE"
    )

    if errors:
        preview = " | ".join(
            errors[:10]
        )

        if len(errors) > 10:
            preview += (
                f" | ... and "
                f"{len(errors) - 10} more"
            )

        final_message = (
            f"Completed with "
            f"{len(errors)} sitemap "
            f"error(s). "
            f"New URLs="
            f"{total_new_urls}. "
            f"{preview}"
        )

    else:
        final_message = (
            f"Completed successfully. "
            f"New URLs="
            f"{total_new_urls}. "
            f"Sources="
            f"{len(enabled_sources)}."
        )

    update_run(
        final_phase,
        None,
        len(enabled_sources),
        final_message,
        finished=True,
    )

    print(
        final_message
    )

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(
            main()
        )

    except SystemExit:
        raise

    except Exception as exc:
        print(
            f"FATAL: {exc}",
            file=sys.stderr,
        )

        traceback.print_exc()

        raise SystemExit(1)
