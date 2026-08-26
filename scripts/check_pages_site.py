#!/usr/bin/env python3
"""Check the staged GitHub Pages tree and landing-page links."""

from __future__ import annotations

import argparse
import struct
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit


class PageParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.hrefs: list[str] = []
        self.anchors: set[str] = set()

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = dict(attrs)
        if tag == "a" and values.get("href"):
            self.hrefs.append(values["href"] or "")
        for key in ("id", "name"):
            if values.get(key):
                self.anchors.add(values[key] or "")


def parse_page(path: Path) -> PageParser:
    parser = PageParser()
    parser.feed(path.read_text(encoding="utf-8"))
    return parser


def png_size(path: Path) -> tuple[int, int]:
    data = path.read_bytes()[:24]
    if len(data) != 24 or data[:8] != b"\x89PNG\r\n\x1a\n":
        raise ValueError(f"not a PNG: {path}")
    return struct.unpack(">II", data[16:24])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("site", nargs="?", default="site", type=Path)
    args = parser.parse_args()
    site = args.site.resolve()

    required = [
        "index.html",
        "styles.css",
        "og.png",
        "blueprint/index.html",
        "blueprint/dep_graph_document.html",
        "blueprint/ch-main.html",
        "docs/index.html",
        "docs/Anderson4D.html",
        "docs/find/index.html",
    ]
    missing = [name for name in required if not (site / name).is_file()]
    if missing:
        raise SystemExit("missing staged Pages files: " + ", ".join(missing))

    if png_size(site / "og.png") != (1200, 630):
        raise SystemExit("og.png must be exactly 1200x630")

    landing = site / "index.html"
    landing_text = landing.read_text(encoding="utf-8")
    required_text = [
        "Conditional scope complete",
        "Prop36Family M rho",
        "MainLawStatement M rho",
        "blueprint/dep_graph_document.html",
        "Anderson4D.main_conditional_law",
    ]
    absent_text = [value for value in required_text if value not in landing_text]
    if absent_text:
        raise SystemExit("landing page is missing: " + ", ".join(absent_text))

    landing_parser = parse_page(landing)
    errors: list[str] = []
    for href in landing_parser.hrefs:
        parts = urlsplit(href)
        if parts.scheme or parts.netloc:
            continue
        if not parts.path:
            target = landing
        else:
            path_text = unquote(parts.path)
            target = (site / path_text).resolve()
            if site not in target.parents and target != site:
                errors.append(f"link escapes staged site: {href}")
                continue
            if path_text.endswith("/") or target.is_dir():
                target /= "index.html"
        if not target.is_file():
            errors.append(f"missing local target: {href} -> {target.relative_to(site)}")
            continue
        if parts.fragment and target.suffix == ".html" and not parts.fragment.startswith("doc/"):
            target_parser = parse_page(target)
            if unquote(parts.fragment) not in target_parser.anchors:
                errors.append(f"missing anchor: {href}")

    if errors:
        raise SystemExit("Pages link check failed:\n- " + "\n- ".join(errors))

    print(f"Pages site check PASS: {len(required)} required files, {len(landing_parser.hrefs)} landing links")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
