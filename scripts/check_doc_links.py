#!/usr/bin/env python3
"""Check repository Markdown links and PAPER_TO_LEAN declaration deep links.

This is intentionally a documentation-only check: it reads source files but
does not invoke Lean. It verifies:

* relative Markdown/HTML link targets exist;
* Markdown and HTML fragments resolve;
* GitHub-style ``#L`` fragments are within the target file;
* a link labelled ``Anderson4D.<name>`` in the audited paper/blueprint indexes
  points to the exact public Lean declaration line bearing that fully
  qualified name.
"""
from __future__ import annotations

import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
DOCS = [
    *sorted(ROOT.glob("*.md")),
    *sorted((ROOT / ".github").rglob("*.md")),
    *sorted((ROOT / "docs").rglob("*.md")),
    *sorted((ROOT / "Anderson4D").rglob("README.md")),
]
PAPER_TO_LEAN = ROOT / "docs" / "PAPER_TO_LEAN.md"
EXACT_DECLARATION_INDEXES = {
    ROOT / "README.md",
    ROOT / "BLUEPRINT.md",
    PAPER_TO_LEAN,
}

INLINE_LINK = re.compile(r"!?\[([^\]]*)\]\(([^)]+)\)")
REFERENCE_LINK = re.compile(r"^\s*\[[^\]]+\]:\s*(\S+)")
HTML_HREF = re.compile(r"\bhref=[\"']([^\"']+)[\"']", re.IGNORECASE)
EXPLICIT_ANCHOR = re.compile(r"<(?:a\s+[^>]*\b(?:id|name)|[^>]+\bid)=[\"']([^\"']+)[\"']", re.IGNORECASE)
HTML_ID = re.compile(r"\b(?:id|name)=[\"']([^\"']+)[\"']", re.IGNORECASE)
HEADING = re.compile(r"^\s{0,3}#{1,6}\s+(.+?)\s*#*\s*$")
LINE_FRAGMENT = re.compile(r"^L(\d+)(?:-L?(\d+))?$")
DECL_LABEL = re.compile(r"^Anderson4D(?:\.[A-Za-z_][A-Za-z0-9_']*)+$")
NODE_LABEL = re.compile(r"^[A-Za-z]+-[A-Za-z0-9.-]+$")
DECL = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:def|abbrev|structure|class|theorem|lemma|inductive|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)


@dataclass(frozen=True)
class Link:
    source: Path
    line: int
    label: str
    target: str


def visible_markdown_lines(path: Path) -> list[tuple[int, str]]:
    """Return lines outside fenced blocks, with inline code spans removed."""
    result: list[tuple[int, str]] = []
    fenced = False
    fence = ""
    for line_no, raw in enumerate(path.read_text().splitlines(), 1):
        stripped = raw.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            marker = stripped[:3]
            if not fenced:
                fenced, fence = True, marker
            elif marker == fence:
                fenced, fence = False, ""
            continue
        if fenced:
            continue
        result.append((line_no, re.sub(r"`[^`\n]*`", "", raw)))
    return result


def links_in(path: Path) -> list[Link]:
    links: list[Link] = []
    for line_no, line in visible_markdown_lines(path):
        for match in INLINE_LINK.finditer(line):
            target = match.group(2).strip()
            if target.startswith("<") and ">" in target:
                target = target[1 : target.index(">")]
            else:
                target = target.split()[0]
            links.append(Link(path, line_no, match.group(1).strip(), target))
        match = REFERENCE_LINK.match(line)
        if match:
            links.append(Link(path, line_no, "reference", match.group(1)))
        for match in HTML_HREF.finditer(line):
            links.append(Link(path, line_no, "href", match.group(1)))
    return links


def github_slug(text: str) -> str:
    text = re.sub(r"<[^>]+>", "", text).strip().lower()
    text = re.sub(r"[^\w\- ]", "", text, flags=re.UNICODE)
    return re.sub(r"\s+", "-", text)


def markdown_anchors(path: Path) -> set[str]:
    anchors: set[str] = set()
    counts: Counter[str] = Counter()
    for _line_no, line in visible_markdown_lines(path):
        anchors.update(EXPLICIT_ANCHOR.findall(line))
        match = HEADING.match(line)
        if not match:
            continue
        base = github_slug(match.group(1))
        if not base:
            continue
        suffix = counts[base]
        counts[base] += 1
        anchors.add(base if suffix == 0 else f"{base}-{suffix}")
    return anchors


def lean_declarations(path: Path) -> dict[str, int]:
    """Collect public declaration names using Lean namespace/section syntax."""
    declarations: dict[str, int] = {}
    stack: list[tuple[str, str | None]] = []
    pending_declaration = False
    for line_no, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.strip()
        namespace = re.match(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$", line)
        if namespace:
            stack.append(("namespace", namespace.group(1)))
            continue
        section = re.match(
            r"^(?:noncomputable\s+)?section(?:\s+([A-Za-z_][A-Za-z0-9_']*))?\s*$",
            line,
        )
        if section:
            stack.append(("section", section.group(1)))
            continue
        if line == "mutual":
            stack.append(("block", None))
            continue
        end = re.match(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$", line)
        if end:
            name = end.group(1)
            if not stack:
                continue
            if name is None:
                stack.pop()
            else:
                for index in range(len(stack) - 1, -1, -1):
                    entry_name = stack[index][1]
                    if entry_name and entry_name.split(".")[-1] == name.split(".")[-1]:
                        del stack[index:]
                        break
            continue
        match = DECL.match(raw)
        if match is None and re.fullmatch(
            r"(?:(?:protected|noncomputable)\s+)*(?:def|abbrev|structure|class|theorem|lemma|inductive|opaque)",
            line,
        ):
            pending_declaration = True
            continue
        if match is None and pending_declaration:
            continued = re.match(
                r"^\s*([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b",
                raw,
            )
            if continued:
                match = continued
            pending_declaration = False
        if not match or raw.lstrip().startswith("private "):
            continue
        prefix: list[str] = []
        for kind, name in stack:
            if kind == "namespace" and name:
                prefix.extend(name.split("."))
        declared = match.group(1).split(".")
        full = ".".join([*prefix, *declared])
        declarations.setdefault(full, line_no)
    return declarations


def check() -> tuple[list[str], int, int]:
    errors: list[str] = []
    relative_count = 0
    declaration_count = 0
    anchor_cache: dict[Path, set[str]] = {}
    declaration_cache: dict[Path, dict[str, int]] = {}

    for source in DOCS:
        for link in links_in(source):
            parsed = urlsplit(link.target)
            if parsed.scheme or link.target.startswith("//"):
                continue
            relative_count += 1
            raw_path = unquote(parsed.path)
            target_path = source if not raw_path else (source.parent / raw_path).resolve()
            try:
                target_path.relative_to(ROOT)
            except ValueError:
                errors.append(
                    f"{source.relative_to(ROOT)}:{link.line}: target escapes repository: {link.target}"
                )
                continue
            if not target_path.exists():
                errors.append(
                    f"{source.relative_to(ROOT)}:{link.line}: missing target: {link.target}"
                )
                continue

            fragment = unquote(parsed.fragment)
            if fragment:
                line_match = LINE_FRAGMENT.fullmatch(fragment)
                if line_match:
                    if not target_path.is_file():
                        errors.append(
                            f"{source.relative_to(ROOT)}:{link.line}: line fragment on non-file: {link.target}"
                        )
                        continue
                    line_total = len(target_path.read_text().splitlines())
                    start = int(line_match.group(1))
                    end = int(line_match.group(2) or start)
                    if start < 1 or end < start or end > line_total:
                        errors.append(
                            f"{source.relative_to(ROOT)}:{link.line}: out-of-range line fragment "
                            f"{fragment} (target has {line_total} lines)"
                        )
                        continue
                elif target_path.suffix.lower() == ".md":
                    anchors = anchor_cache.setdefault(target_path, markdown_anchors(target_path))
                    if fragment not in anchors:
                        errors.append(
                            f"{source.relative_to(ROOT)}:{link.line}: missing Markdown anchor "
                            f"#{fragment} in {target_path.relative_to(ROOT)}"
                        )
                        continue
                elif target_path.suffix.lower() in {".html", ".htm"}:
                    anchors = anchor_cache.setdefault(
                        target_path, set(HTML_ID.findall(target_path.read_text()))
                    )
                    if fragment not in anchors:
                        errors.append(
                            f"{source.relative_to(ROOT)}:{link.line}: missing HTML anchor "
                            f"#{fragment} in {target_path.relative_to(ROOT)}"
                        )
                        continue

            if (
                source in EXACT_DECLARATION_INDEXES
                and target_path.suffix == ".lean"
                and DECL_LABEL.fullmatch(link.label)
            ):
                declaration_count += 1
                declarations = declaration_cache.setdefault(target_path, lean_declarations(target_path))
                actual_line = declarations.get(link.label)
                if actual_line is None:
                    errors.append(
                        f"{source.relative_to(ROOT)}:{link.line}: declaration not found in "
                        f"{target_path.relative_to(ROOT)}: {link.label}"
                    )
                    continue
                line_match = LINE_FRAGMENT.fullmatch(fragment)
                linked_line = int(line_match.group(1)) if line_match else None
                if linked_line != actual_line:
                    errors.append(
                        f"{source.relative_to(ROOT)}:{link.line}: {link.label} is at L{actual_line}, "
                        f"not {fragment or 'an unnumbered target'}"
                    )

            if source == PAPER_TO_LEAN and target_path.suffix == ".tex" and NODE_LABEL.fullmatch(link.label):
                line_match = LINE_FRAGMENT.fullmatch(fragment)
                linked_line = int(line_match.group(1)) if line_match else None
                target_lines = target_path.read_text().splitlines()
                if linked_line is None or f"\\label{{{link.label}}}" not in target_lines[linked_line - 1]:
                    errors.append(
                        f"{source.relative_to(ROOT)}:{link.line}: blueprint node {link.label} "
                        f"does not occur at {fragment or 'an unnumbered target'} in "
                        f"{target_path.relative_to(ROOT)}"
                    )

    return errors, relative_count, declaration_count


def main() -> int:
    errors, relative_count, declaration_count = check()
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        print(f"doc links: FAIL ({len(errors)} errors)")
        return 1
    print(
        f"doc links: PASS ({len(DOCS)} Markdown files, {relative_count} relative links, "
        f"{declaration_count} exact Lean declaration links)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
