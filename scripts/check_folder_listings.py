#!/usr/bin/env python3
"""Fail if a page or subfolder is not listed on its folder page (docs/BLUEPRINT.md, "Placing pages").

A page's folder page is its nearest ancestor `README.md`, as Autoform finds it. A page is listed by
the first link of a list item or a heading (a part's), read with Autoform's own reader, outside a
closing section such as "Related topics"; a link in prose, code or a comment does not list it.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit

from autoform_cli.markdown import content_lines, markdown_links

sys.path.insert(0, str(Path(__file__).resolve().parent))
from sync_wiki import CLOSING  # noqa: E402

ENTRY = re.compile(r"\s*(?:[-*+]|\d{1,9}[.)])\s|\s{0,3}#{2,6}\s")
HEADING = re.compile(r"\s{0,3}(#{1,6})\s+(.*?)\s*$")

ROADMAP = Path(__file__).resolve().parent.parent / "blueprint" / "roadmap"


def entries(text: str) -> list[str]:
    """The first link of each list item and heading, outside closing sections."""
    first: dict[int, str] = {}
    for number, target, _ in markdown_links(text):
        first.setdefault(number, target)
    found, closing = [], 0  # the level of the closing section's heading; its subsections are in it too
    for number, line in enumerate(content_lines(text), 1):
        if (heading := HEADING.match(line)) and (not closing or len(heading.group(1)) <= closing):
            closing = len(heading.group(1)) if heading.group(2).strip("*_` ").casefold() in CLOSING else 0
        if not closing and number in first and ENTRY.match(line):
            found.append(first[number])
    return found


def unlisted(roadmap: Path) -> list[str]:
    roadmap = roadmap.resolve()
    links: dict[Path, set[Path]] = {}
    found = []
    for page in sorted(roadmap.rglob("*.md")):
        if page == roadmap / "README.md" or any(p.startswith(".") for p in page.relative_to(roadmap).parts):
            continue
        folder = page.parent.parent if page.name == "README.md" else page.parent
        while folder != roadmap and not (folder / "README.md").is_file():
            folder = folder.parent
        readme = folder / "README.md"
        if readme not in links:
            targets = (urlsplit(target) for target in entries(readme.read_text(encoding="utf-8")))
            paths = {Path(folder, unquote(t.path)).resolve() for t in targets if t.path and not t.scheme}
            links[readme] = {path / "README.md" if path.is_dir() else path for path in paths}
        if page not in links[readme]:
            found.append(f"{page.relative_to(roadmap)}: not listed on {readme.relative_to(roadmap)}")
    return found


if __name__ == "__main__":
    found = unlisted(ROADMAP)
    print("\n".join(f"error: {line}" for line in found) or "OK: every page is listed on its folder page")
    sys.exit(1 if found else 0)
