#!/usr/bin/env python3
"""Fail if a page or subfolder is not listed on its folder page (docs/BLUEPRINT.md, "Placing pages").

A page's folder page is its nearest ancestor `README.md`, as Autoform finds it. Any link to the page
counts, read with Autoform's own reader, so a link in code or a comment does not.
"""

from __future__ import annotations

import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit

from autoform_cli.markdown import markdown_links

ROADMAP = Path(__file__).resolve().parent.parent / "blueprint" / "roadmap"


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
            targets = (urlsplit(target) for _, target, _ in markdown_links(readme.read_text(encoding="utf-8")))
            paths = {Path(folder, unquote(t.path)).resolve() for t in targets if t.path and not t.scheme}
            links[readme] = {path / "README.md" if path.is_dir() else path for path in paths}
        if page not in links[readme]:
            found.append(f"{page.relative_to(roadmap)}: not listed on {readme.relative_to(roadmap)}")
    return found


if __name__ == "__main__":
    found = unlisted(ROADMAP)
    print("\n".join(f"error: {line}" for line in found) or "OK: every page is listed on its folder page")
    sys.exit(1 if found else 0)
