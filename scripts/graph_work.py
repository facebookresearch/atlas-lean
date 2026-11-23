"""List planned wiki work from the authored annotations, without a Lean build.

This is an inventory, not a readiness or claim service. Autoform's
formalization queue remains the published tasks.json and next_task.py.
"""

from __future__ import annotations

import argparse
import json

from . import sync_wiki as sync


def extension(row: dict, namespace: str) -> dict:
    extensions = row.get("extensions")
    value = extensions.get(namespace) if isinstance(extensions, dict) else None
    return value if isinstance(value, dict) else {}


def inventory() -> list[dict]:
    if not sync.LINKS.is_dir() or sync.links_template() is None:
        raise ValueError("cannot read the wiki annotation folder and its defaults")
    items: dict[str, dict] = {}
    for rows in sync.read_annotations().values():
        for row in rows:
            effective = sync.effective(row)
            if effective is None:
                raise ValueError("cannot read an annotation with the wiki's defaults")
            if extension(effective, "org.autoform").get("not_ready") is not True:
                continue
            own = extension(effective, "org.atlas-wiki")
            if "held" in own or sync.legacy_pair(row) or sync.owner_of(row, effective)[0] != "none":
                continue
            page, problem = sync.subject_of(effective)
            if page is None or not page.is_file():
                raise ValueError(f"cannot read a marked article: {problem or page}")
            if page.name == "README.md":
                continue
            path = page.relative_to(sync.wiki.ROOT).as_posix()
            if path in items:
                raise ValueError(f"more than one marked annotation for {path}")
            pending = own.get("pending", [])
            if not isinstance(pending, list):
                raise ValueError(f"{path}: pending prerequisites must be a list")
            items[path] = {
                "path": path,
                "article_id": effective.get("id"),
                "kind": "review-pending-prerequisites" if pending else "expand",
                "pending": pending,
            }
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
