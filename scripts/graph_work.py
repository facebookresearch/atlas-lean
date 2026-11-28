"""List planned wiki work from the authored annotations, without a Lean build.

This is an inventory, not a readiness or claim service. Autoform's
formalization queue remains the published tasks.json and next_task.py.
"""

from __future__ import annotations

import argparse
import functools
import json
import os
from collections.abc import Iterator
from pathlib import Path

from . import sync_wiki as sync


def extension(row: dict, namespace: str) -> dict:
    extensions = row.get("extensions")
    value = extensions.get(namespace) if isinstance(extensions, dict) else None
    return value if isinstance(value, dict) else {}


def annotation_lines() -> Iterator[tuple[str, dict]]:
    """Each row of the links files with where it is (`file:line` from the repository's root), read as
    sync_wiki.read_annotations reads them (read_rows), its lines numbered as Autoform numbers them."""
    for links in sorted(sync.LINKS.glob("*.jsonl")):
        name = links.relative_to(sync.wiki.ROOT).as_posix()
        try:
            text = links.read_text(encoding="utf-8")
        except UnicodeDecodeError as error:
            raise ValueError(f"{name}: it is not UTF-8: {error}") from None
        for number, line in enumerate(text.replace("\r\n", "\n").replace("\r", "\n").split("\n"), 1):
            if not line.strip():
                continue
            # As sync_wiki.location names a row, with the file's name worked out once.
            where = f"{name}:{number}"
            try:
                row = json.loads(line)
            except json.JSONDecodeError as error:
                raise ValueError(f"{where}: the row is not JSON: {error.msg} at column {error.colno}") from None
            yield where, row


def shown(page: Path | None, where: str, problem: str | None) -> str:
    """An annotation as an error names it: its page, from the repository's root, or where it is and why it has none."""
    if page is not None:
        return page.relative_to(sync.wiki.ROOT).as_posix()
    return f"the annotation at {where} ({problem})"


@functools.cache
def import_validator():
    """The importer's own check of the shape of an imported page's record: the seed and the pending list its manifest
    row gives and its annotation keeps (docs/mathgraph-import.md, Annotations), with the manifest's schema and
    validator."""
    from . import import_mathgraph as imports

    schema = imports.MANIFEST_SCHEMA
    return imports.WHOLE_STRING_VALIDATOR({
        "$defs": schema["$defs"],
        "type": "object",
        "required": ["seed", "pending"],
        "properties": {name: schema["properties"][name] for name in ("seed", "pending")},
    })


def import_problem(own: dict, article_id: str) -> str | None:
    """Why a page's pending prerequisites are not an import's record, or None, by the importer's own checks of what its
    annotation keeps: the manifest's schema (import_validator: a seed of mathgraph, and pending entries of a key, a kind
    and a public reason), the article ID that seed gives, and no prerequisite listed twice. The record's consistency,
    not that an import took place."""
    from . import import_mathgraph as imports

    errors = sorted(import_validator().iter_errors(own), key=lambda error: [str(part) for part in error.absolute_path])
    if errors:
        at = "/".join(str(part) for part in errors[0].absolute_path)
        return f"{at}: {errors[0].message}" if at else errors[0].message
    if article_id != (seeded := imports.article_id(own["seed"])):
        return f"its article ID is not {seeded}, the one its seed gives"
    # The importer also refuses the result's own key, which the import map keeps and the annotation does not. No
    # entry's key is empty (the schema's `key`), so the empty key checks for keys listed twice alone.
    if twice := imports.pending_problems("", own["pending"]):
        number, problem = twice[0]
        return f"pending/{number}: {problem}"
    return None


def inventory() -> list[dict]:
    # Autoform reads blueprint/links only as a folder of that name that is no symbolic link, and none of it when it
    # cannot use its defaults.
    if not sync.reader().links_exist(sync.LINKS.parent) or sync.links_template() is None:
        raise ValueError(f"Autoform reads no annotations: {sync.LINKS.relative_to(sync.wiki.ROOT).as_posix()} is "
                         "missing, is a symbolic link, or has defaults it cannot use")
    # The checks the sync makes of the folder: files and lines that Autoform and the sync would read differently, such
    # as an annotation file in a subfolder, or a line Autoform's reader leaves out (a key given twice, say).
    if problems := sync.links_problems():
        more = f" (and {len(problems) - 1} more)" if problems[1:] else ""
        raise ValueError(f"{problems[0]}{more}")
    items: dict[str, dict] = {}
    listed: dict[str, str] = {}  # each listed path's page, as the keys of `annotations` name it
    annotations: dict[str, int] = {}  # how many annotations are about each page
    with_id: dict[str, list[tuple[Path | None, str, str | None]]] = {}  # the annotations that have each id
    for where, row in annotation_lines():
        effective = sync.effective(row)
        if effective is None:
            raise ValueError(f"{where}: cannot read the annotation with the wiki's defaults")
        page, problem = sync.subject_of(effective)
        if page is not None:
            key = os.fspath(page)
            annotations[key] = annotations.get(key, 0) + 1
        # Autoform takes a row's id, as the rest of its facts, from the row merged over the folder's defaults.
        if isinstance(effective.get("id"), str):
            with_id.setdefault(effective["id"], []).append((page, where, problem))
        if extension(effective, "org.autoform").get("not_ready") is not True:
            continue
        own = extension(effective, "org.atlas-wiki")
        if "held" in own or sync.legacy_pair(row) or sync.owner_of(row, effective)[0] != "none":
            continue
        if page is None or not page.is_file():
            raise ValueError(f"{where}: cannot read a marked article: {problem or page}")
        if page.name == "README.md":
            continue
        path = page.relative_to(sync.wiki.ROOT).as_posix()
        article_id = row.get("id")
        if not isinstance(article_id, str) or not sync.ARTICLE_ID.fullmatch(article_id):
            raise ValueError(f"{path}: expected an article ID of the form af_ followed by 24 lowercase hex digits")
        # Only an import lists pending prerequisites, beside the seed of the result it imported.
        if "pending" in own and (invalid := import_problem(own, article_id)):
            raise ValueError(f"{path}: its pending prerequisites are not an import's: {invalid}")
        pending = own.get("pending", [])
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
