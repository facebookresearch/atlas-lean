"""List planned wiki work from the authored annotations, without a Lean build.

This is an inventory, not a readiness or claim service. Autoform's
formalization queue remains the published tasks.json and next_task.py.
"""

from __future__ import annotations

import argparse
import json
import os
from collections.abc import Iterator
from pathlib import Path

from . import sync_wiki as sync


def extension(row: dict, namespace: str) -> dict:
    extensions = row.get("extensions")
    value = extensions.get(namespace) if isinstance(extensions, dict) else None
    return value if isinstance(value, dict) else {}


def annotation_lines() -> Iterator[tuple[Path, str, dict]]:
    """Each row of the links files with its file and its line as written, read as sync_wiki.read_annotations reads
    them (read_rows)."""
    for links in sorted(sync.LINKS.glob("*.jsonl")):
        text = links.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")
        for line in text.split("\n"):
            if line.strip():
                yield links, line, json.loads(line)


def shown(page: Path | None, links: Path, problem: str | None) -> str:
    """An annotation as an error names it: its page, from the repository's root, or its file and why it has none."""
    if page is not None:
        return page.relative_to(sync.wiki.ROOT).as_posix()
    return f"an annotation in {links.relative_to(sync.wiki.ROOT).as_posix()} ({problem})"


def inventory() -> list[dict]:
    from literature_links import companion

    if not sync.LINKS.is_dir() or sync.links_template() is None:
        raise ValueError("cannot read the wiki annotation folder and its defaults")
    items: dict[str, dict] = {}
    listed: dict[str, str] = {}  # each listed path's page, as the keys of `annotations` name it
    annotations: dict[str, int] = {}  # how many annotations are about each page
    with_id: dict[str, list[tuple[Path | None, Path, str | None]]] = {}  # the annotations that have each id
    for links, line, row in annotation_lines():
        effective = sync.effective(row)
        if effective is None:
            raise ValueError("cannot read an annotation with the wiki's defaults")
        page, problem = sync.subject_of(effective)
        if page is not None:
            key = os.fspath(page)
            annotations[key] = annotations.get(key, 0) + 1
        if isinstance(row.get("id"), str):
            with_id.setdefault(row["id"], []).append((page, links, problem))
        if extension(effective, "org.autoform").get("not_ready") is not True:
            continue
        own = extension(effective, "org.atlas-wiki")
        if "held" in own or sync.legacy_pair(row) or sync.owner_of(row, effective)[0] != "none":
            continue
        if page is None or not page.is_file():
            raise ValueError(f"cannot read a marked article: {problem or page}")
        if page.name == "README.md":
            continue
        path = page.relative_to(sync.wiki.ROOT).as_posix()
        # Autoform reads each row strictly: it leaves out one with a key twice, say, which json.loads reads.
        try:
            companion.loads(line)
        except (companion.LoadError, RecursionError) as error:
            raise ValueError(f"{path}: Autoform leaves its annotation out: {error}") from None
        article_id = row.get("id")
        if not isinstance(article_id, str) or not sync.ARTICLE_ID.fullmatch(article_id):
            raise ValueError(f"{path}: expected an article ID of the form af_ followed by 24 lowercase hex digits")
        pending = own.get("pending", [])
        if not isinstance(pending, list):
            raise ValueError(f"{path}: pending prerequisites must be a list")
        items[path] = {
            "path": path,
            "article_id": article_id,
            "kind": "review-pending-prerequisites" if pending else "expand",
            "pending": pending,
        }
        listed[path] = key
    # Each listed id names one article: Autoform keeps the first of a page's annotations' ids, and no other
    # annotation, marked or not, may have it.
    for path in sorted(items):
        if (count := annotations[listed[path]]) > 1:
            raise ValueError(f"{path}: expected one annotation of this page, found {count}; Autoform keeps the first "
                             "one's ID and marks")
        article_id = items[path]["article_id"]
        if len(entries := with_id[article_id]) > 1:
            others = sorted(shown(*entry) for entry in entries)
            others.remove(path)
            raise ValueError(f"{path}: its article ID {article_id} is also the ID of {', '.join(others)}")
    return [items[path] for path in sorted(items)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    try:
        items = inventory()
    except (OSError, ValueError) as error:
        parser.exit(1, f"error: {error}\n")
    print(json.dumps(items, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
