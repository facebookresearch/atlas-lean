#!/usr/bin/env python3
"""Apply a reviewed mathgraph manifest to the ATLAS wiki: planned pages, and pages credited to Mathlib declarations.

    python scripts/import_mathgraph.py --check --manifest MANIFEST.jsonl --manifest-sha256 SHA256
    python scripts/import_mathgraph.py --apply --manifest MANIFEST.jsonl --manifest-sha256 SHA256
    python scripts/import_mathgraph.py --identity blueprint/roadmap/PAGE.md
    python scripts/import_mathgraph.py --check-map [--base REV]

The manifest is an allowlist: each JSON line authorises one page, planned or credited to one Mathlib declaration
(docs/BLUEPRINT.md, "Mathlib-credited pages"), its annotation and its row of scripts/mathgraph-map.jsonl. Nothing else
of mathgraph is read. The file must have the SHA-256 given, which the review approved, every row must match
MANIFEST_SCHEMA and pass the checks docs/mathgraph-import.md lists, and the whole change is laid out and checked before
anything is written: a check that fails stops the run, writes nothing, names the problems found and exits 1. --check
prints the change, each folder, file and line with the rule that puts it there, and writes nothing. --apply writes it as
one transaction (see apply): an exception while writing is rolled back, or what cannot be restored is named; a crash or
a power loss is not covered, so it runs on a clean worktree, which `git checkout -- . && git clean -fd` restores. It
assumes an exclusive worktree that nothing else changes while it runs: it detects some concurrent changes and then
refuses or reports an incomplete rollback, but it does not promise immunity to concurrent mutation. Existing statement
pages are never changed, the planned pages an earlier import wrote among them, nor a line of the map: an existing file
changes only by the items a folder page gains (sync_wiki.add_to_listing, or after the page's own list where the sync
would only append, each checked as the sync checks its edits), by rows added to a links file where the sync adds them
(sync_wiki.inserted: each right after the row whose page's path comes last before its own, wherever that row stands)
and by rows appended to the map.
Symbolic links are refused on every repository path the importer writes or removes, and on the files whose content it
reads, each checked on the path then opened (see symlink_on): a manifest in the repository, the links files,
scripts/taxonomy.json, the card move ledger, the map, the folder pages it edits or whose part copies it refreshes, the
pages a dependency names and the pages its cycle check reads. A manifest that is itself a symbolic link is refused (see
read_manifest). Folder listings, used to place pages and check names, and any other file sync_wiki, generate_wiki and
Autoform read, lake-manifest.json among them, are read as those tools read them. Where the importer itself decides
whether a path is there, it does so without following links, so a dangling link is there. --identity prints what a
dependency on an existing page is bound to (see page_identity), and writes nothing. --check-map checks the map's lines
(see map_problems) and, with --base, that the map only grows from its state at REV (see growth_problems) and that each
line appended since records a page the change adds (see appended_problems), and writes nothing.

Run it with a Python that has Autoform installed (see blueprint-pages.yml).
"""

from __future__ import annotations

import argparse
import difflib
import errno
import hashlib
import html.parser
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import unquote, urlsplit

import jsonschema
from autoform_cli.markdown import article_parts, link_definitions, link_targets, render_html
from autoform_cli.ui.publishable import publishable_article

if __package__:
    from . import check_public_references as gate
    from . import generate_wiki as wiki
    from . import sync_wiki as sync
else:
    import check_public_references as gate
    import generate_wiki as wiki
    import sync_wiki as sync

MAP = wiki.ROOT / "scripts" / "mathgraph-map.jsonl"
# Manifest paths are relative to the repository, under this folder.
PREFIX = "blueprint/roadmap/"
SKETCH = "Proof sketch"
# CONTRIBUTING.md, Graph PRs: under 3,000 changed files, the most GitHub shows in one diff.
MAX_CHANGED_FILES = 2999
# Autoform's audit (overfull-container) reports an article above 24 direct children, and a `navigation: module` page
# above wiki.MAX_MODULE_CHILDREN; generate_wiki splits a listing into parts of wiki.MAX_CHILDREN.
MAX_DIRECT_CHILDREN = 24
DEPENDENCY_SECTIONS = {"depends on", "proof depends on", "informally uses"}
# Fields of a row that become prose on a page, and fields that name files or folders: the Public references check
# reads the latter as literal values, as it reads file names.
TEXT_FIELDS = {"title", "statement", "sketch", "prose_missing", "sources"}
PATH_FIELDS = {"key", "stem", "page_dir", "target"}
# The fields whose prose may run over several lines, and the lines that would end the section such prose is written in
# (CommonMark): a setext heading's underline, below a line of text, and a thematic break, which ends the paragraph and
# draws a rule.
PROSE_FIELDS = {"statement", "sketch", "prose_missing"}
SETEXT_UNDERLINE = re.compile(r" {0,3}(?:=+|-+)[ \t]*")
THEMATIC_BREAK = re.compile(r" {0,3}([-*_])(?:[ \t]*\1){2,}[ \t]*")

MANIFEST_SCHEMA = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "title": "A row of a mathgraph import manifest",
    "type": "object",
    "additionalProperties": False,
    "required": ["key", "kind", "mg_kind", "title", "statement", "sketch", "sources", "page_dir", "stem", "seed",
                 "depends", "pending", "not_ready", "prose_missing", "statement_sha256", "sketch_sha256",
                 "mg_statement_sha256", "mg_sketch_sha256", "reference_sha256", "edges_sha256"],
    "properties": {
        "key": {"$ref": "#/$defs/key"},
        "kind": {"enum": ["planned", "mathlib"]},
        "mg_kind": {"enum": ["theorem", "definition"]},
        "title": {"$ref": "#/$defs/line"},
        "statement": {"$ref": "#/$defs/text"},
        "sketch": {"anyOf": [{"$ref": "#/$defs/text"}, {"type": "null"}]},
        "sources": {"type": "array", "minItems": 1, "uniqueItems": True, "items": {"$ref": "#/$defs/line"}},
        "page_dir": {"type": "string", "pattern": "^blueprint/roadmap/[A-Z][A-Za-z]*(?:/[a-z0-9]+(?:-[a-z0-9]+)*)+$"},
        "stem": {"$ref": "#/$defs/key"},
        "seed": {
            "type": "object",
            "additionalProperties": False,
            "required": ["source", "node", "revision"],
            "properties": {
                "source": {"const": "mathgraph"},
                "node": {"type": "string", "pattern": "^mg_[0-9a-f]{24}$"},
                "revision": {"type": "string", "pattern": "^[0-9a-f]{40}$"},
            },
        },
        "depends": {"type": "array", "items": {"$ref": "#/$defs/dependency"}},
        "pending": {"type": "array", "items": {
            "type": "object",
            "additionalProperties": False,
            "required": ["key", "kind", "reason"],
            "properties": {
                "key": {"$ref": "#/$defs/key"},
                "kind": {"enum": ["statement", "proof"]},
                "reason": {"enum": ["not-imported", "under-review", "source-unverified", "covered-by-generalization"]},
            },
        }},
        "not_ready": {"type": "boolean"},
        "prose_missing": {"anyOf": [{"$ref": "#/$defs/text"}, {"type": "null"}]},
        "statement_sha256": {"$ref": "#/$defs/sha256"},
        "sketch_sha256": {"$ref": "#/$defs/sha256"},
        "mg_statement_sha256": {"$ref": "#/$defs/sha256"},
        "mg_sketch_sha256": {"$ref": "#/$defs/sha256"},
        "reference_sha256": {"$ref": "#/$defs/sha256"},
        "edges_sha256": {"$ref": "#/$defs/sha256"},
        "mathlib": {
            "type": "object",
            "additionalProperties": False,
            "required": ["declaration", "module"],
            "properties": {"declaration": {"$ref": "#/$defs/declaration"}, "module": {"$ref": "#/$defs/module"}},
        },
    },
    # A Mathlib-credited row states what its declaration states, with no sketch and no prerequisite of its own: the
    # build derives its edges (docs/BLUEPRINT.md, "Mathlib-credited pages"). Only such a row names a declaration.
    "if": {"required": ["kind"], "properties": {"kind": {"const": "mathlib"}}},
    "then": {
        "required": ["mathlib"],
        "properties": {"sketch": {"type": "null"}, "depends": {"maxItems": 0}, "pending": {"maxItems": 0},
                       "not_ready": {"const": False}, "prose_missing": {"type": "null"}},
    },
    "else": {"properties": {"mathlib": {"not": {}}}},
    "$defs": {
        "key": {"type": "string", "pattern": "^[a-z0-9]+(?:-[a-z0-9]+)*$", "maxLength": 96},
        "declaration": {"type": "string", "pattern": "^\\S+$"},
        "module": {"type": "string", "pattern": "^Mathlib(?:\\.[A-Za-z0-9_']+)+$"},
        "line": {"type": "string", "pattern": "^\\S(?:[^\\n\\r]*\\S)?$"},
        "text": {"type": "string", "pattern": "^\\S(?:[^\\r]*\\S)?$"},
        "sha256": {"type": "string", "pattern": "^[0-9a-f]{64}$"},
        "page": {
            "type": "string",
            "pattern": ("^blueprint/roadmap/[A-Z][A-Za-z]*(?:/[a-z0-9]+(?:-[a-z0-9]+)*)*/"
                        "(?:[a-z0-9]+(?:-[a-z0-9]+)*|README)\\.md$"),
        },
        "dependency": {
            "type": "object",
            "additionalProperties": False,
            "required": ["target", "kind"],
            "properties": {
                "target": {"anyOf": [{"$ref": "#/$defs/key"}, {"$ref": "#/$defs/page"}]},
                "kind": {"enum": ["statement", "proof"]},
                "target_statement_sha256": {"$ref": "#/$defs/sha256"},
                "target_annotation_sha256": {"$ref": "#/$defs/sha256"},
            },
            "if": {"required": ["target"], "properties": {"target": {"$ref": "#/$defs/page"}}},
            "then": {"required": ["target_statement_sha256", "target_annotation_sha256"]},
            "else": {"properties": {"target_statement_sha256": {"not": {}}, "target_annotation_sha256": {"not": {}}}},
        },
    },
}


def whole_pattern(validator, pattern: str, instance, schema):
    """The `pattern` keyword as the importer applies it: the whole string must match (re.fullmatch). A JSON Schema
    validator searches for the pattern (re.search), and `$` also matches before a final line break, so that "foo\\n"
    would match `^[a-z]+$`."""
    if validator.is_type(instance, "string") and not re.fullmatch(pattern, instance):
        yield jsonschema.ValidationError(f"{instance!r} does not match {pattern!r} as a whole string")


# The validator of MANIFEST_SCHEMA and MAP_SCHEMA: Draft 2020-12, each `pattern` of the schema, in `anyOf` and `if`
# too, matched against the whole string (see whole_pattern), so that the patterns checked are the schema's own.
WHOLE_STRING_VALIDATOR = jsonschema.validators.extend(jsonschema.Draft202012Validator, {"pattern": whole_pattern})


def shown(text: str) -> str:
    """*text* as a message shows it: as it is, or as a JSON string when it holds a line break or another control
    character."""
    return text if text.isprintable() else json.dumps(text, ensure_ascii=False)


# A line of scripts/mathgraph-map.jsonl: its fields, in the order the importer writes them (see map_line), a Mathlib
# credit last when the line has one, and their schema, whose pending list, key, digests, id, revision and credit are the
# manifest's.
MAP_FIELDS = ("key", "node", "revision", "page", "statement_sha256", "sketch_sha256", "mg_statement_sha256",
              "mg_sketch_sha256", "reference_sha256", "edges_sha256", "pending")
MAP_SCHEMA = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "title": "A line of the mathgraph import map",
    "type": "object",
    "additionalProperties": False,
    "required": list(MAP_FIELDS),
    "properties": {
        "key": {"$ref": "#/$defs/key"},
        "node": MANIFEST_SCHEMA["properties"]["seed"]["properties"]["node"],
        "revision": MANIFEST_SCHEMA["properties"]["seed"]["properties"]["revision"],
        "page": {"type": "string", "pattern": ("^blueprint/roadmap/[A-Z][A-Za-z]*(?:/[a-z0-9]+(?:-[a-z0-9]+)*)*/"
                                               "[a-z0-9]+(?:-[a-z0-9]+)*\\.md$")},
        **{name: {"$ref": "#/$defs/sha256"} for name in MAP_FIELDS if name.endswith("_sha256")},
        "pending": MANIFEST_SCHEMA["properties"]["pending"],
        "mathlib": {
            "type": "object",
            "additionalProperties": False,
            "required": ["declaration", "module", "rev"],
            "properties": {"declaration": {"$ref": "#/$defs/declaration"}, "module": {"$ref": "#/$defs/module"},
                           "rev": MANIFEST_SCHEMA["properties"]["seed"]["properties"]["revision"]},
        },
    },
    # A line with a Mathlib credit records a row with no sketch and no pending prerequisite, as MANIFEST_SCHEMA
    # requires.
    "if": {"required": ["mathlib"]},
    "then": {"properties": {"pending": {"maxItems": 0},
                            "sketch_sha256": {"const": hashlib.sha256(b"").hexdigest()}}},
    "$defs": {name: MANIFEST_SCHEMA["$defs"][name] for name in ("key", "sha256", "declaration", "module")},
}


class Refused(Exception):
    """The manifest, or the change it asks for, fails a check, and *outcome* says what that leaves: nothing written,
    unless a failed write could not be undone in full (see apply)."""

    def __init__(self, problems: list[str], outcome: str = "nothing written") -> None:
        super().__init__(f"{len(problems)} problems")
        self.problems = problems
        self.outcome = outcome


@dataclass
class Row:
    line: int
    data: dict

    @property
    def key(self) -> str:
        return self.data["key"]

    def where(self) -> str:
        return f"manifest line {self.line} ({self.key})"


@dataclass(eq=False)
class Page(wiki.Target):
    """A page the manifest writes. To generate_wiki it is an article, as a declaration's page is: a Target with no Lean
    declaration, which its functions order, split and list as they would one (see generator_order and
    generate_wiki.listed). Its depends and proof_depends are the other pages of the manifest it names."""

    row: Row | None = None
    why: str = ""

    @classmethod
    def of(cls, row: Row, why: str) -> Page:
        return cls(book="", idx=0, title=row.data["title"], slug="", location="", description="", declaration="",
                   lean=None, statement=False, proof=False, names=[], row=row, why=why)


@dataclass
class Wiki:
    """What the checks read of the wiki: each page's annotation and the pages that have more than one, the annotation
    ids, the card folders (docs/cards.md), the addresses the card move ledger records and the keys the map holds, each
    with its line of the map and the page it was imported at."""

    owners: dict[Path, dict]
    doubled: set[Path]
    ids: set[str]
    cards: set[Path]
    retired: set[str]
    mapped: dict[str, tuple[int, str]]


@dataclass
class Plan:
    manifest: Path
    digest: str
    rows: list[Row]
    creates: dict[Path, str]
    edits: dict[Path, tuple[bytes, bytes]]
    report: list[tuple[str, str, str]]


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def repo_path(path: Path) -> str:
    try:
        return path.relative_to(wiki.ROOT).as_posix()
    except ValueError:
        return str(path)


def symlink_on(path: Path) -> Path | None:
    """The first component of *path*, a path in the repository, from the repository root down, that is a symbolic
    link; None when none is. A component that is not there ends the search, as nothing can be below it."""
    current = wiki.ROOT
    for part in path.relative_to(wiki.ROOT).parts:
        current = current / part
        if current.is_symlink():
            return current
        if not os.path.lexists(current):
            return None
    return None


def symlink_problem(path: Path) -> str | None:
    """What refuses *path* when it is, or lies below, a symbolic link (see symlink_on), naming the link; None if not."""
    found = symlink_on(path)
    if found is None:
        return None
    where = repo_path(path) if found == path else f"{repo_path(path)}: its folder {repo_path(found)}"
    return f"{where} is a symbolic link; the importer reads and writes no path through one"


def input_problems() -> list[str]:
    """Symbolic links on what the checks read before any page: the roadmap and links folders, every links file, the
    taxonomy, the card move ledger and the map."""
    paths = [wiki.ROADMAP, sync.LINKS, wiki.TAXONOMY, wiki.ROOT / "scripts" / "card-moves.jsonl", MAP]
    if symlink_on(sync.LINKS) is None and sync.LINKS.is_dir():
        paths += sorted(sync.LINKS.glob("*.jsonl"))
    return [problem for path in paths if (problem := symlink_problem(path))]


def roadmap_path(manifest_path: str) -> Path:
    """The file or folder a manifest path names."""
    return wiki.ROADMAP / manifest_path.removeprefix(PREFIX)


def mathgraph_id(key: str) -> str:
    """mathgraph's id of the result with *key*: `mg_` and the first 24 hex digits of the SHA-256 of `result:<key>`."""
    return "mg_" + sha256(f"result:{key}")[:24]


def article_id(seed: dict) -> str:
    """A page's annotation id, from its seed alone: `af_` and the first 24 hex digits of the SHA-256 of the compact
    JSON array `["<source>","<node>","<revision>"]`."""
    return "af_" + sha256(json.dumps([seed["source"], seed["node"], seed["revision"]], separators=(",", ":")))[:24]


def folder_id(folder: Path, digest: str) -> str:
    """A new folder page's annotation id: the same digest over `["folder","<folder path>","<manifest SHA-256>"]`."""
    return "af_" + sha256(json.dumps(["folder", repo_path(folder), digest], separators=(",", ":")))[:24]


def statement_sha256(page: Path) -> str:
    """The SHA-256 of a page's statement as Autoform reads it: its body before the first `##` section, without its
    title (autoform_cli.markdown.article_parts)."""
    return sha256(article_parts(page.read_text(encoding="utf-8")).statement)


def sketch_sha256(page: Path) -> str | None:
    """The SHA-256 of a planned page's sketch as Autoform reads it (autoform_cli.markdown.article_parts): the body of
    its `## Proof sketch` section, or the empty string when it has none, as check_planned digests a row's sketch; None
    when the page has more than one such section."""
    sketches = [section.body for section in article_parts(page.read_text(encoding="utf-8")).sections
                if section.title == SKETCH]
    return None if len(sketches) > 1 else sha256(sketches[0] if sketches else "")


def annotation_sha256(annotation: dict) -> str:
    """The SHA-256 of an annotation row as canonical JSON: json.dumps with sorted keys, the separators `,` and `:` and
    non-ASCII characters as they are, in UTF-8. The row is the one its links file holds, the links folder's defaults
    not merged in, as the sync reads it (sync_wiki.read_annotations)."""
    return sha256(json.dumps(annotation, sort_keys=True, separators=(",", ":"), ensure_ascii=False))


def read_manifest(manifest: Path, digest: str) -> bytes:
    """The manifest's bytes, once they are there and have the reviewed SHA-256. The manifest is named by one path, the
    argument made absolute without resolving links (os.path.abspath), which is the path checked and the path opened.
    It is opened with O_NOFOLLOW, so a manifest that is itself a symbolic link is refused before any byte of it is
    read; a manifest in the repository is refused too when a folder on its way from the repository root is a link (see
    symlink_on). The folders above a manifest outside the repository are not checked: its digest binds its content."""
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise Refused([f"--manifest-sha256 must be 64 lowercase hex digits, not {digest!r}"])
    path = Path(os.path.abspath(manifest))
    unsafe = symlink_problem(path) if path.is_relative_to(wiki.ROOT) else None
    if unsafe:
        raise Refused([unsafe])
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError as error:
        if path.is_symlink():
            raise Refused([f"{path} is a symbolic link; a manifest that is itself one is refused"]) from None
        if isinstance(error, FileNotFoundError):
            raise Refused([f"{path}: there is no such manifest"]) from None
        raise Refused([f"{path}: the manifest cannot be read: {error.strerror}"]) from None
    with os.fdopen(descriptor, "rb") as handle:
        if not stat.S_ISREG(os.fstat(handle.fileno()).st_mode):
            raise Refused([f"{path}: the manifest is not a file"])
        data = handle.read()
    if not data.strip():
        raise Refused([f"{path}: the manifest is empty"])
    if hashlib.sha256(data).hexdigest() != digest:
        raise Refused([f"{path}: its SHA-256 is {hashlib.sha256(data).hexdigest()}, not the reviewed {digest}"])
    return data


def strict_object(pairs: list[tuple[str, object]]) -> dict:
    names = [name for name, _ in pairs]
    if len(set(names)) != len(names):
        raise ValueError(f"member {next(name for name in names if names.count(name) > 1)!r} appears twice")
    return dict(pairs)


def not_json(name: str):
    raise ValueError(f"{name} is not JSON")


def parse_rows(data: bytes, problems: list[str]) -> tuple[list[Row], dict[str, dict]]:
    """The rows that match MANIFEST_SCHEMA, each pattern a full-string match (see WHOLE_STRING_VALIDATOR), and every
    row that has a key, valid or not, by key."""
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        problems.append(f"the manifest is not UTF-8: {error}")
        return [], {}
    lines = text.split("\n")
    if lines[-1] == "":
        lines.pop()
    validator = WHOLE_STRING_VALIDATOR(MANIFEST_SCHEMA)
    rows: list[Row] = []
    raw: dict[str, dict] = {}
    numbers: dict[str, list[int]] = defaultdict(list)
    for number, line in enumerate(lines, 1):
        try:
            value = json.loads(line, object_pairs_hook=strict_object, parse_constant=not_json)
        except ValueError as error:
            problems.append(f"manifest line {number}: not a JSON object: {error}")
            continue
        if not isinstance(value, dict):
            problems.append(f"manifest line {number}: not a JSON object")
            continue
        key = value.get("key") if isinstance(value.get("key"), str) else None
        if key is not None:
            numbers[key].append(number)
            raw.setdefault(key, value)
        errors = sorted(validator.iter_errors(value), key=lambda error: [str(part) for part in error.absolute_path])
        for error in errors:
            at = "/".join(str(part) for part in error.absolute_path)
            label = f"manifest line {number} ({shown(key)})" if key else f"manifest line {number}"
            if error.validator == "not" and error.validator_value == {} and at == "mathlib":
                # The schema's `{"not": {}}` on a row's credit, which only a Mathlib-credited row has.
                problems.append(f"{label}: mathlib is allowed only on a row of kind mathlib")
            elif error.validator == "not" and error.validator_value == {}:
                # Its `{"not": {}}` on a target's identity, which only an existing page has.
                problems.append(f"{label}: {at} is allowed only for a target that is an existing page")
            elif error.validator == "anyOf" and error.context:
                # What each alternative finds wrong: a pattern the value does not match, or a type it does not have.
                reasons = "; ".join(sorted({reason.message for reason in error.context}))
                problems.append(f"{label}: {at}: {error.message} ({reasons})")
            else:
                problems.append(f"{label}: {at}: {error.message}" if at else f"{label}: {error.message}")
        if not errors:
            rows.append(Row(number, value))
    for key, found in numbers.items():
        if len(found) > 1:
            problems.append(f"manifest lines {', '.join(map(str, found))}: the key {shown(key)} appears more than "
                            "once")
    return rows, raw


def pending_problems(key: str, pending: list[dict]) -> list[tuple[int, str]]:
    """What is wrong with a row's pending list on its own, whatever else the wiki holds, each with the entry's
    position: an entry that names the row's own result, and an entry whose key an earlier entry has. check_rows applies
    it to each row of a manifest and map_problems to each line of the map, which the importer writes from such a row."""
    found, listed = [], set()
    for number, entry in enumerate(pending):
        if entry["key"] == key:
            found.append((number, f"{entry['key']} is the row itself"))
        elif entry["key"] in listed:
            found.append((number, f"{entry['key']} is pending twice"))
        listed.add(entry["key"])
    return found


def stem_problem(stem: str) -> str | None:
    """What keeps *stem* from being a new page's file name, whatever its folder: a name reserved for folder pages and
    parts (generate_wiki.RESERVED_SLUGS, sync_wiki.PART), or one longer than a stem may be (MANIFEST_SCHEMA). name_page
    applies it to each new page, and map_problems to the page of each line of the map."""
    if stem in wiki.RESERVED_SLUGS or sync.PART.fullmatch(stem):
        return "a name reserved for folder pages and parts"
    if len(stem) > MANIFEST_SCHEMA["$defs"]["key"]["maxLength"]:
        return f"longer than a stem may be ({MANIFEST_SCHEMA['$defs']['key']['maxLength']} characters)"
    return None


def map_page_problem(page: str) -> str | None:
    """What keeps *page*, a line's page, from being a path the importer writes, whatever the wiki holds: every page it
    writes lies in a folder a manifest's page_dir can name (MANIFEST_SCHEMA), at least one folder below its subject,
    under a stem a new page may take (see stem_problem)."""
    folder, _, name = page.rpartition("/")
    if not re.fullmatch(MANIFEST_SCHEMA["properties"]["page_dir"]["pattern"], folder):
        return f"its folder {folder} is no folder a manifest's page_dir can name, as every page the importer writes is"
    reserved = stem_problem(name.removesuffix(".md"))
    return f"its file name {name} is {reserved}" if reserved else None


def map_line(row: dict) -> str:
    """A line of the map as the importer writes it for *row*, without its line break: its fields in MAP_FIELDS' order,
    a pending entry's as key, kind, reason, and then its Mathlib credit, if it has one, as declaration, module, rev, as
    json.dumps writes them, with its default separators (`, ` and `: `) and non-ASCII characters as they are."""
    ordered = {name: row[name] for name in MAP_FIELDS}
    ordered["pending"] = [{name: entry[name] for name in ("key", "kind", "reason")} for entry in row["pending"]]
    if "mathlib" in row:
        ordered["mathlib"] = {name: row["mathlib"][name] for name in ("declaration", "module", "rev")}
    return json.dumps(ordered, ensure_ascii=False)


def map_problems(data: bytes, label: str) -> tuple[list[tuple[int, dict]], list[str]]:
    """The rows of a map, from its bytes, each with its line number, and what is wrong with them, each named by *label*
    and its line: every line must be a JSON object that matches MAP_SCHEMA, each pattern a full-string match (see
    WHOLE_STRING_VALIDATOR), in the form the importer writes (see map_line), with a key and a page no other line has;
    and the map, unless it is empty, ends in a line break. A line is held to the rules of a manifest row that need
    nothing but the line: its node is mathgraph's id of its key, its pending list passes pending_problems, and its page
    map_page_problem. Across lines, it looks strictly backwards: no pending key of a line is an earlier line's key, as
    the importer would have refused that row. A line is never judged by a later one, nor against the pages: it keeps its
    row's pending list as it was imported when one of those prerequisites is imported later, below it."""
    if not data:
        return [], []
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        return [], [f"{label} is not UTF-8: {error}"]
    lines = text.split("\n")
    problems = []
    if lines[-1]:
        problems.append(f"{label} line {len(lines)}: the map does not end in a line break, as the importer writes it")
    else:
        lines.pop()
    validator = WHOLE_STRING_VALIDATOR(MAP_SCHEMA)
    rows: list[tuple[int, dict]] = []
    seen: dict[str, dict[str, int]] = {"key": {}, "page": {}}
    for number, line in enumerate(lines, 1):
        where = f"{label} line {number}"
        try:
            row = json.loads(line, object_pairs_hook=strict_object, parse_constant=not_json)
        except ValueError as error:
            problems.append(f"{where}: not a JSON object: {error}")
            continue
        if not isinstance(row, dict):
            problems.append(f"{where}: not a JSON object")
            continue
        errors = sorted(validator.iter_errors(row), key=lambda error: [str(part) for part in error.absolute_path])
        for error in errors:
            at = "/".join(str(part) for part in error.absolute_path)
            problems.append(f"{where}: {at}: {error.message}" if at else f"{where}: {error.message}")
        if errors:
            continue
        if row["node"] != mathgraph_id(row["key"]):
            problems.append(f"{where}: node {row['node']} is not mathgraph's id of the result {row['key']}, "
                            f"{mathgraph_id(row['key'])}")
        # The rules of a manifest row that a line can be held to on its own (see pending_problems, map_page_problem).
        own = dict(pending_problems(row["key"], row["pending"]))
        problems += [f"{where}: pending/{index}: {problem}" for index, problem in own.items()]
        unwritten = map_page_problem(row["page"])
        if unwritten:
            problems.append(f"{where}: page: {unwritten}")
        # Strictly backwards: a pending key may not be the key of an earlier line, as the importer refuses a pending
        # key the map holds. An earlier line is never judged by a later one: its pending list is its row's as it was
        # imported, and a prerequisite imported after it is appended below it.
        problems += [f"{where} ({row['key']}): pending/{index}: {entry['key']} is the key of line "
                     f"{seen['key'][entry['key']]}, an earlier line, and a row may not list as pending a key the map "
                     "holds" for index, entry in enumerate(row["pending"])
                     if index not in own and entry["key"] in seen["key"]]
        if line != map_line(row):
            problems.append(f"{where}: it is not written as the importer writes its row: the fields in the map's "
                            "order, json.dumps's separators `, ` and `: `, non-ASCII characters as they are")
        for field, lines_of in seen.items():
            if row[field] in lines_of:
                problems.append(f"{where}: its {field} {row[field]} is line {lines_of[row[field]]}'s too")
            else:
                lines_of[row[field]] = number
        rows.append((number, row))
    return rows, problems


def read_wiki(problems: list[str]) -> Wiki:
    # The map first: a map with a line that is not valid refuses the run (see map_problems).
    mapped: dict[str, tuple[int, str]] = {}
    if os.path.lexists(MAP) and not MAP.is_file():
        problems.append(f"{repo_path(MAP)} is not a file")
    elif os.path.lexists(MAP):
        rows, found = map_problems(MAP.read_bytes(), repo_path(MAP))
        problems += found
        for number, row in rows:
            mapped.setdefault(row["key"], (number, row["page"]))
    owners, doubled, ids, cards = annotation_owners()
    try:
        retired = sync.retired_addresses()
    except (ValueError, AttributeError):
        problems.append("scripts/card-moves.jsonl is not a JSON object per line")
        retired = set()
    return Wiki(owners, doubled, ids, cards, retired, mapped)


def annotation_owners() -> tuple[dict[Path, dict], set[Path], set[str], set[Path]]:
    """Each page's annotation, as the sync reads the rows (sync_wiki.read_annotations), by the page's resolved path; the
    pages with more than one; the annotation ids; and the card folders (docs/cards.md)."""
    owners: dict[Path, dict] = {}
    doubled: set[Path] = set()
    ids: set[str] = set()
    cards: set[Path] = set()
    for rows in sync.read_annotations().values():
        for annotation in rows:
            path = sync.subject_path(annotation)
            if path in owners:
                doubled.add(path)
            owners[path] = annotation
            if isinstance(annotation.get("id"), str):
                ids.add(annotation["id"])
            # A card is a folder whose folder page's annotation carries a card record, as the sync finds it.
            own = annotation.get("extensions", {}).get(sync.OWN)
            if path.name == "README.md" and isinstance(own, dict) and "card" in own:
                cards.add(path.parent)
    return owners, doubled, ids, cards


def strings(value, at: str = ""):
    """Each string in a row, with where it sits: `statement`, `sources/0`, `depends/2/target`."""
    if isinstance(value, str):
        yield at, value
    elif isinstance(value, dict):
        for name, item in value.items():
            yield from strings(item, f"{at}/{name}" if at else name)
    elif isinstance(value, list):
        for number, item in enumerate(value):
            yield from strings(item, f"{at}/{number}")


def heading_or_rule(text: str) -> bool:
    """Whether a line of *text* is a thematic break, or a setext heading's underline below a line of text (see
    THEMATIC_BREAK and SETEXT_UNDERLINE)."""
    lines = text.split("\n")
    return any(THEMATIC_BREAK.fullmatch(line) or number > 0 and lines[number - 1].strip() != ""
               and SETEXT_UNDERLINE.fullmatch(line) for number, line in enumerate(lines))


class Addresses(html.parser.HTMLParser):
    """The address of each link and image of rendered HTML: each `href` and `src`, in order."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.found: list[tuple[str, str]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self.found += [(name, value or "") for name, value in attrs if name in ("href", "src")]


def addresses(text: str) -> list[tuple[str, str]]:
    """Each address *text* links or shows, with how: its links and images as the site renders the text alone
    (autoform_cli.markdown.render_html), and the targets of its reference definitions, which on a page also serve
    references in its other sections (autoform_cli.markdown.link_definitions)."""
    parser = Addresses()
    parser.feed(render_html(text))
    parser.close()
    shown = [("shows an image from" if name == "src" else "links to", value) for name, value in parser.found]
    return shown + [("defines a link to", target) for target in link_definitions(text.split("\n")).values()]


def text_problems(row: Row) -> list[str]:
    """What is wrong with a row's text: a reference the Public references check reports, in its text or, read as a
    literal value, in a field that names a file or folder; a heading line, in prose a line that would make a heading or
    a rule (see heading_or_rule), which would end the page's section, and a source that would make a rule in its list;
    a title ending in a backslash, which would escape the bracket that closes every link to its page; and a link, an
    image or a reference definition to anything but an https:// address (see addresses), as the importer writes every
    link to a page itself."""
    problems = []
    for at, value in strings(row.data):
        field = next(part for part in reversed(at.split("/")) if not part.isdigit())
        found = {(finding["rule"], finding["line"]) for finding in gate.scan(value, at, citation_start=0)}
        if field in PATH_FIELDS:
            found |= {(finding["rule"], finding["line"]) for finding in gate.scan(value, at, rules=gate.LITERAL_RULES)}
        problems += [f"{row.where()}: {at} holds a reference the Public references check reports ({rule}, line {line})"
                     for rule, line in sorted(found)]
        if field not in TEXT_FIELDS:
            continue
        if re.search(r"(?m)^ {0,3}#{1,6}(?:[ \t]|$)", value):
            problems.append(f"{row.where()}: {at} has a line that is a Markdown heading, which would end its section")
        if field in PROSE_FIELDS and heading_or_rule(value):
            problems.append(f"{row.where()}: {at} has a line that would make a Markdown heading or a rule, which would "
                            "end its section")
        if field == "sources" and (heading_or_rule(value) or heading_or_rule(f"- {value}")):
            problems.append(f"{row.where()}: {at} would make a rule, not a source, in the page's list of sources")
        if field == "title" and value.endswith("\\"):
            problems.append(f"{row.where()}: {at} ends in a backslash, which would escape the bracket that closes "
                            "every link to its page")
        problems += [f"{row.where()}: {at} {how} {address!r}; text may link only https:// addresses, as the "
                     "importer writes every link to a page" for how, address in addresses(value)
                     if not address.startswith("https://")]
    return problems


def pinned_mathlib() -> tuple[str | None, str | None]:
    """The Mathlib revision lake-manifest.json pins, as sync_wiki reads it (sync_wiki.mathlib_revision), and None with
    why when it pins none, as when the file is missing or cannot be read, is no JSON object or names no Mathlib
    commit."""
    try:
        revision = sync.mathlib_revision()
    except (OSError, ValueError, AttributeError, TypeError) as error:
        return None, f"lake-manifest.json cannot be read as sync_wiki reads it: {error}"
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        return None, "lake-manifest.json pins no Mathlib commit"
    return revision, None


def claimants(files: dict[Path, list[dict]], names: set[str]) -> dict[str, list[tuple[Path, str]]]:
    """The pages that credit each of *names*, as sync_wiki reads credit (page_owner), to Mathlib or as a declaration of
    this project, each with the kind of its owner (`mathlib` or `atlas`): the one rule the importer applies to a
    Mathlib-credited row and --check-map to an appended line with a Mathlib credit, as a declaration has one page. A row
    whose credit sync_wiki cannot read one way (CreditError) is no claimant here, as sync_wiki's own checks refuse it;
    nor is a row an earlier sync wrote with a module and a name only, which credits the declaration the Lean index gives
    it, as the build resolves; nor a row whose only link to the declaration is a Mathlib link without the `mathlib`
    flag, a reference that credits nothing."""
    found: dict[str, list[tuple[Path, str]]] = {name: [] for name in names}
    for file_rows in files.values():
        for annotation in file_rows:
            page = sync.subject_path(annotation)
            if page is None:
                continue  # about no one page, which sync_wiki's own checks refuse
            try:
                owner, name, _module = sync.page_owner(annotation)
            except sync.CreditError:
                continue
            if owner != "none" and name in found:
                found[name].append((page, owner))
    return found


def claim_problems(name: str, claims: list[tuple[Path, str]], own: Path | None = None) -> list[str]:
    """Each page that credits the Mathlib declaration *name* (see claimants) other than *own*, the page of an appended
    line of the map; a declaration has one page."""
    how = {"mathlib": "to Mathlib", "atlas": "as a declaration of this project"}
    return [f"{repo_path(page)} credits {name} {how[owner]} too; a declaration has one page" for page, owner in claims
            if own is None or page.resolve() != own.resolve()]


def mathlib_problems(rows: list[Row]) -> list[str]:
    """What keeps the manifest's Mathlib-credited rows from crediting their declarations as sync_wiki reads credit
    (docs/BLUEPRINT.md, "Mathlib-credited pages"): the links folder's credits are ambiguous, which `sync_wiki.py
    mathlib-names` refuses too (credited_mathlib); a declaration two rows name, or that a page already credits, to
    Mathlib or as a declaration of this project (claimants), while a declaration has one page; or lake-manifest.json
    pins no Mathlib revision, which the map records (pinned_mathlib). A row an earlier sync wrote with a module and a
    name only credits a declaration of this project that the Lean index gives it, which the build resolves and the
    importer does not. Whether the declaration is Mathlib's at that revision, in the module the row names, is not
    checked here (docs/mathgraph-import.md, "The manifest")."""
    credits = [row for row in rows if row.data["kind"] == "mathlib"]
    if not credits:
        return []
    problems = []
    _, unpinned = pinned_mathlib()
    if unpinned:
        problems.append(f"{unpinned}; the map records the Mathlib revision for a Mathlib-credited row")
    files = sync.read_annotations()
    _, ambiguous = sync.credited_mathlib(files)
    problems += [f"the links folder's credits are ambiguous, as sync_wiki.py mathlib-names reads them: {problem}"
                 for problem in ambiguous]
    claims = claimants(files, {row.data["mathlib"]["declaration"] for row in credits})
    first: dict[str, Row] = {}
    for row in credits:
        name = row.data["mathlib"]["declaration"]
        if name in first:
            problems.append(f"{row.where()}: mathlib/declaration {name} is also that of {first[name].where()}; a "
                            "declaration has one page")
        else:
            problems += [f"{row.where()}: mathlib/declaration: {problem}"
                         for problem in claim_problems(name, claims[name])]
        first.setdefault(name, row)
    return problems


def written_credit_problems(rows: list[Row], pages: dict, annotations: dict[Path, list[dict]]) -> list[str]:
    """What sync_wiki's credit check finds in the links folder as the change would leave it, its current rows and the
    rows the change adds (credit_problems), and each new page whose row would credit otherwise than its manifest row
    says (page_owner): its Mathlib declaration and module for a Mathlib-credited row, nothing for a planned one."""
    files = sync.read_annotations()
    after = {path: [*files.get(path, []), *annotations.get(path, [])] for path in {*files, *annotations}}
    problems = [f"the links folder as the change would leave it: {problem}" for problem in sync.credit_problems(after)]
    for row in rows:
        data = row.data
        expected = (("mathlib", data["mathlib"]["declaration"], data["mathlib"]["module"])
                    if data["kind"] == "mathlib" else ("none", None, None))
        try:
            found = sync.page_owner(page_annotation(row, pages[row.key].path))
        except sync.CreditError as error:
            problems.append(f"{row.where()}: {error}")
            continue
        if found != expected:
            problems.append(f"{row.where()}: sync_wiki would read its page's annotation as crediting "
                            f"{credit_text(found)}, not {credit_text(expected)}")
    return problems


def credit_text(owner: tuple[str, str | None, str | None]) -> str:
    """What sync_wiki.page_owner's reading of a row says it credits, in words."""
    kind, name, module = owner
    if kind == "mathlib":
        return f"the Mathlib declaration {name}" + (f" in {module}" if module else "")
    return f"the declaration {name} of this project" if kind == "atlas" else "no declaration"


def page_identity(target: str, known: Wiki) -> tuple[dict | None, list[str]]:
    """An existing page's identity, `{path, statement_sha256, annotation_sha256}` (see statement_sha256 and
    annotation_sha256), and what keeps the page from being a dependency: it is, or lies below, a symbolic link, it is
    no page of the wiki or a folder page, which states no result, it has no annotation or more than one, or its
    annotation holds its declaration back."""
    page = roadmap_path(target)
    unsafe = symlink_problem(page)
    if unsafe:
        return None, [unsafe]
    if not page.is_file():
        return None, [f"{target} is no page of the wiki"]
    if page.name == "README.md":
        return None, [f"{target} is a folder page, which states no result; a dependency is a statement page"]
    annotation = known.owners.get(page.resolve())
    if annotation is None:
        return None, [f"{target} has no annotation, so no identity to bind"]
    problems = []
    if page.resolve() in known.doubled:
        problems.append(f"{target} has more than one annotation row, so no one identity to bind")
    own = annotation.get("extensions", {}).get(sync.OWN)
    if isinstance(own, dict) and "held" in own:
        problems.append(f"{target} is held back, and unlinked until its declaration is fixed (docs/BLUEPRINT.md, "
                        "Maintaining articles); a held page is no dependency of an imported page")
    identity = {"path": target, "statement_sha256": statement_sha256(page),
                "annotation_sha256": annotation_sha256(annotation)}
    return identity, problems


def endpoint(entry: dict, row: Row, raw: dict[str, dict], passed: set[str], known: Wiki):
    """What a dependency's target names, ("row", key) for another planned row of the manifest or ("page", path) for an
    existing page, and the problems with it. A target is an exact identity only: a row that passes its own checks, or
    an existing page that may be a dependency (see page_identity) and whose statement and annotation have the reviewed
    digests, `target_statement_sha256` and `target_annotation_sha256`. Anything else is refused."""
    target = entry["target"]
    if target == row.key:
        return None, [f"{target} is the row itself"]
    if target in passed:
        return ("row", target), []
    if target in raw:
        return None, [f"{target} is a row of this manifest that fails its checks"]
    if not target.startswith(PREFIX):
        return None, [f"{target} is no row of this manifest"]
    identity, problems = page_identity(target, known)
    if identity is None:
        return None, problems
    for field, what in (("statement_sha256", "its statement as Autoform reads it"),
                        ("annotation_sha256", "its annotation row as canonical JSON")):
        if identity[field] != entry[f"target_{field}"]:
            problems.append(f"{target}: the SHA-256 of {what} is {identity[field]}, not the reviewed target_{field} "
                            f"{entry[f'target_{field}']}")
    return (None if problems else ("page", roadmap_path(target))), problems


def check_rows(rows: list[Row], raw: dict[str, dict], known: Wiki, problems: list[str]) -> dict[str, list]:
    """Check each row on its own and against the wiki, then each row's dependencies against the rows that passed (see
    endpoint), and its pending prerequisites on their own (see pending_problems) and against the rows of the manifest
    and the keys the map holds, which an incoming row may not list as pending; return what each row's dependencies name,
    with their kinds, by key."""
    seeds: dict[str, str] = {}
    passed: set[str] = set()
    for row in rows:
        data, where = row.data, row.where()
        found = text_problems(row)
        seed = data["seed"]
        if seed["node"] != mathgraph_id(row.key):
            found.append(f"{where}: seed node {seed['node']} is not mathgraph's id of the result {row.key}, "
                         f"{mathgraph_id(row.key)}")
        identifier = article_id(seed)
        if identifier in known.ids:
            found.append(f"{where}: the id its seed gives, {identifier}, is already an annotation's")
        elif identifier in seeds:
            found.append(f"{where}: the id its seed gives, {identifier}, is also that of {seeds[identifier]}")
        seeds.setdefault(identifier, row.key)
        if row.key in known.mapped:
            found.append(f"{where}: {repo_path(MAP)} already maps {row.key}; a result is imported once")
        check_planned(row, found)
        problems += found
        if not found:
            passed.add(row.key)
    resolved: dict[str, list] = {}
    for row in rows:
        data, where = row.data, row.where()
        resolved[row.key], seen = [], {}
        for number, entry in enumerate(data["depends"]):
            ref, found = endpoint(entry, row, raw, passed, known)
            problems += [f"{where}: depends/{number}: {problem}" for problem in found]
            if ref in seen:
                problems.append(f"{where}: depends/{number} names the page depends/{seen[ref]} names")
            elif ref is not None:
                seen[ref] = number
                resolved[row.key].append((entry["kind"], ref))
        own = dict(pending_problems(row.key, data["pending"]))
        for number, entry in enumerate(data["pending"]):
            if number in own:
                problems.append(f"{where}: pending/{number}: {own[number]}")
            elif entry["key"] in raw:
                problems.append(f"{where}: pending/{number}: {entry['key']} is a row of this manifest, an active "
                                "endpoint, so it belongs in depends, not in pending")
            elif entry["key"] in known.mapped:
                # Imported already: a dependency on its page, which the manifest names by the identity its review
                # confirmed; the importer never links it on its own. The map says where it was imported, which the
                # page may have left since. A line of the map keeps its own pending list (see map_problems).
                line, page = known.mapped[entry["key"]]
                problems.append(f"{where}: pending/{number}: pending key {entry['key']} was imported already (map line "
                                f"{line}, imported at {page}); name its page, at its current path, under depends with "
                                "its reviewed identity (`--identity <page>`)")
    return resolved


def check_planned(row: Row, problems: list[str]) -> None:
    """The rules of a row that its schema does not state: digests, readiness and a definition's sections."""
    data, where = row.data, row.where()
    if sha256(data["statement"]) != data["statement_sha256"]:
        problems.append(f"{where}: statement_sha256 is not the SHA-256 of its statement")
    if sha256(data["sketch"] or "") != data["sketch_sha256"]:
        problems.append(f"{where}: sketch_sha256 is not the SHA-256 of its sketch"
                        + (" (of the empty string, as it has none)" if data["sketch"] is None else ""))
    pending = bool(data["pending"])
    if data["not_ready"] is not pending:
        problems.append(f"{where}: not_ready is {json.dumps(data['not_ready'])} but its pending list is "
                        f"{'not ' * pending}empty: a page is not ready exactly when a prerequisite is pending")
    if (data["prose_missing"] is not None) is not pending:
        problems.append(f"{where}: prose_missing is {'null' if pending else 'given'} but its pending list is "
                        f"{'not ' * pending}empty: it names the pending prerequisites, so it is given exactly then")
    if data["mg_kind"] == "definition":
        if data["sketch"] is not None:
            problems.append(f"{where}: a definition has no proof, so no sketch")
        if any(entry["kind"] == "proof" for entry in data["depends"] + data["pending"]):
            problems.append(f"{where}: a definition has no proof, so no proof prerequisite")


def field_folders(taxonomy: dict) -> dict[str, dict]:
    """Each field and subfield of the taxonomy, by its folder below blueprint/roadmap."""
    folders = {}
    for subject, entry in taxonomy["subjects"].items():
        for spec in entry["fields"]:
            folders[f"{subject}/{spec['slug']}"] = spec
            for sub in spec["subfields"]:
                folders[f"{subject}/{spec['slug']}/{sub['slug']}"] = sub
    return folders


def field_kind(folder: str) -> str:
    return "subfield" if folder.count("/") == 2 else "field"


def topic_folders(taxonomy: dict) -> dict[str, tuple[str, str, str]]:
    """Each folder a placement defines, `<to>/<slugify(title)>` below blueprint/roadmap: its field, title and the
    first placement that defines it."""
    folders: dict[str, tuple[str, str, str]] = {}
    for key, spot in sorted(taxonomy["placements"].items()):
        folders.setdefault(f"{spot['to']}/{wiki.slugify(spot['title'])}", (spot["to"], spot["title"], key))
    return folders


def home(row: Row, fields: dict, topics: dict, count: Counter, problems: list[str]) -> tuple[str, str] | None:
    """A page row's folder below blueprint/roadmap, and why; see docs/mathgraph-import.md, "Placing pages"."""
    folder = row.data["page_dir"].removeprefix(PREFIX)
    subject = folder.split("/")[0]
    # Compared with its case, which a case-insensitive filesystem would ignore.
    if subject not in os.listdir(wiki.ROADMAP) or not os.path.lexists(wiki.ROADMAP / subject / "README.md"):
        problems.append(f"{row.where()}: page_dir {row.data['page_dir']} is in no subject folder of the wiki")
        return None
    if os.path.lexists(wiki.ROADMAP / folder / "README.md"):
        return folder, f"the existing folder {PREFIX}{folder}"
    if folder in fields:
        return folder, f"the folder of the {field_kind(folder)} {folder} of scripts/taxonomy.json"
    if folder in topics:
        to, title, key = topics[folder]
        slug = folder.rsplit("/", 1)[1]
        holders = sync.parts(wiki.ROADMAP / to) if os.path.lexists(wiki.ROADMAP / to / "README.md") else []
        kept = next((holder / slug for holder in holders if os.path.lexists(holder / slug / "README.md")), None)
        beside = next((holder for holder in holders if os.path.lexists(holder / f"{slug}.md")), None)
        if kept is not None:
            return kept.relative_to(wiki.ROADMAP).as_posix(), f"the folder of topic {title!r} ({key}), in a part"
        if beside is not None:
            return (beside.relative_to(wiki.ROADMAP).as_posix(),
                    f"{repo_path(beside)}, beside {repo_path(beside / slug)}.md, the page at the folder path of "
                    f"topic {title!r} ({key})")
        if to not in fields:
            problems.append(f"{row.where()}: the placement {key} puts topic {title!r} in {to}, which is no field of "
                            "scripts/taxonomy.json")
            return None
        if count[folder] == 1:
            return to, f"the folder of the {field_kind(to)} {to}, as topic {title!r} ({key}) would hold this page alone"
        return folder, f"the new folder of topic {title!r} ({key})"
    problems.append(f"{row.where()}: page_dir {row.data['page_dir']} is no existing folder, no field or subfield of "
                    "scripts/taxonomy.json and no topic folder a placement defines (<to>/<slugify(title)>); no "
                    "topic folder is made that no placement defines")
    return None


def generator_order(folder: str, title: str, kids: list, fields: dict) -> list:
    """The children of a folder the importer makes, in the order generate_wiki.subject_tree gives a folder's: a field's
    subfields first, in the taxonomy's order; then its other children, as a subfield's and a topic's children, each
    after the siblings whose pages its pages use (generate_wiki.dependency_order), the rest by title, titles equal up
    to case by file name; and a child folder
    titled like the folder is flattened into it, its pages leading (generate_wiki.namesake_first). The child folders
    hold their own children already (see make_plan's build), as subject_tree's do, so that the order sees them."""
    field = folder in fields and field_kind(folder) == "field"
    order = [sub["slug"] for sub in fields[folder]["subfields"]] if field else []
    subfields = sorted((kid for kid in kids if isinstance(kid, wiki.Container) and kid.slug in order
                        and f"{folder}/{kid.slug}" in fields), key=lambda kid: order.index(kid.slug))
    rest = [kid for kid in kids if all(kid is not subfield for subfield in subfields)]
    # By title up to case, as subject_tree sorts; a tie by file name, so that the manifest's order never decides.
    topics = wiki.dependency_order(sorted(rest, key=lambda node: (node.title.casefold(), node.row.data["stem"]
                                                                  if isinstance(node, Page) else node.slug)))
    return wiki.namesake_first(title, subfields + topics)


def card_holding(folder: Path, cards: set[Path]) -> Path | None:
    """The card a folder is or lies in (docs/cards.md), found as sync_wiki.apply_declarations finds it; None if none."""
    roadmap = wiki.ROADMAP.resolve()
    for up in (folder.resolve(), *folder.resolve().parents):
        if up in cards:
            return up
        if up == roadmap:
            break
    return None


def logical_folder(directory: Path) -> Path:
    """The folder whose list a folder's own list belongs to: the folder itself, or, for a transparent part
    (`part-NN`, as the sync reads one), the nearest folder above it that is no part."""
    while sync.PART.fullmatch(directory.name):
        directory = directory.parent
    return directory


def existing_names(logical: Path) -> dict[str, str]:
    """The names the pages and subfolders of a folder's list take, folded to lower case, with what takes each: those
    of the folder and of all its transparent parts, which read as one list with it (see logical_folder). Every entry
    takes its name, and a page its stem too, whatever it is: a symbolic link, dangling or not, takes them as well."""
    names: dict[str, str] = {}
    for folder in sync.parts(logical):
        for entry in folder.iterdir():
            if entry.is_symlink():
                taker = f"the symbolic link {repo_path(entry)}"
            elif entry.is_dir():
                taker = f"the existing folder {repo_path(entry)}/"
            elif entry.suffix == ".md":
                taker = f"the existing page {repo_path(entry)}"
            else:
                taker = f"the existing file {repo_path(entry)}"
            names.setdefault(entry.name.casefold(), taker)
            if entry.suffix == ".md" and entry.name != "README.md":
                names.setdefault(entry.stem.casefold(), taker)
    return names


def direct_children(directory: Path) -> list[Path]:
    """A folder's pages and subfolders, as Autoform counts its direct children."""
    return [entry for entry in directory.iterdir() if (entry / "README.md").is_file()
            or entry.is_file() and entry.suffix == ".md" and entry.name != "README.md"]


def grouped(folder: str, kids: list, known: Wiki, why: dict[int, str], problems: list[str]) -> list:
    """The new children of an existing folder, grouped into transparent parts when the folder would otherwise go above
    the limit Autoform's audit sets for it, so that none of its children moves: in groups of wiki.MAX_CHILDREN, in the
    order given, each numbered after the folder's own parts and titled `Part N` by its number. A subject folder holds
    its fields only, which generate_wiki never splits."""
    if "/" not in folder:
        return kids
    directory = wiki.ROADMAP / folder
    present = direct_children(directory)
    annotation = known.owners.get((directory / "README.md").resolve(), {})
    module = annotation.get("extensions", {}).get(sync.NAMESPACE, {}).get("navigation") == "module"
    limit = wiki.MAX_MODULE_CHILDREN if module else MAX_DIRECT_CHILDREN
    if len(present) + len(kids) <= limit:
        return kids
    first = max((int(entry.name[5:]) for entry in present if sync.PART.fullmatch(entry.name)), default=0) + 1
    groups = [kids[start:start + wiki.MAX_CHILDREN] for start in range(0, len(kids), wiki.MAX_CHILDREN)]
    parts = []
    for number, group in enumerate(groups, first):
        # Titled by its number, as its folder is named: the new children are in the manifest's order, which a range of
        # titles would misread as an order of titles.
        part = wiki.Container(f"Part {number}", f"part-{number:02d}", group, navigation="transparent")
        for kid in group:
            if isinstance(kid, Page):
                kid.why = f"{kid.why}, in its new transparent part part-{number:02d}"
        why[id(part)] = (f"a transparent part: {PREFIX}{folder} has {len(present)} direct children and would get "
                         f"{len(kids)} more, above the {limit} Autoform's audit allows")
        parts.append(part)
    if len(present) + len(parts) > limit:
        problems.append(f"{PREFIX}{folder} has {len(present)} direct children: its {len(kids)} new ones take it above "
                        f"the {limit} Autoform's audit allows, even grouped into transparent parts ({len(parts)})")
    return parts


def lay_out(directory: Path, kids: list, taken: dict[str, str], retired: set[str], problems: list[str],
            pages: list[tuple[Page, Path, dict[str, str]]]) -> None:
    """Name the new folders among a folder's new children, and below them, and collect its new pages, each with the
    folder it goes in and the names of that folder's list, *taken*, which a folder and its transparent parts share:
    the names their pages and subfolders have, existing and new (see existing_names). A new part (`part-NN`) is
    numbered after the parts its folder has, by generate_wiki.chunk or grouped, and is refused if its path is taken;
    any other new folder takes the name the taxonomy gives it, which may not have a part's form, and is refused if its
    folder's list has that name. A folder whose address the card move ledger records (docs/cards.md) is refused
    too."""
    here = directory.relative_to(wiki.ROADMAP).as_posix()
    for kid in kids:
        if isinstance(kid, Page):
            pages.append((kid, directory, taken))
            continue
        path, part = directory / kid.slug, kid.navigation == "transparent"
        if part:
            clash = next((f"{repo_path(other)}, which is there" for other in (path, path.with_suffix(".md"))
                          if os.path.lexists(other)), None)
        elif kid.slug in wiki.RESERVED_SLUGS or sync.PART.fullmatch(kid.slug):
            clash = "a name reserved for folder pages and the generator's parts"
        else:
            clash = taken.get(kid.slug.casefold())
        if clash is None and f"{here}/{kid.slug}" in retired:
            clash = f"the address {PREFIX}{here}/{kid.slug}, which scripts/card-moves.jsonl records"
        if clash:
            problems.append(f"{repo_path(path)}/ cannot be made a folder: it collides with {clash}")
            continue
        if not part:
            taken[kid.slug.casefold()] = f"the new folder {repo_path(path)}/"
        kid.path = path / "README.md"
        lay_out(path, kid.children, taken if part else {}, retired, problems, pages)


def name_page(page: Page, directory: Path, taken: dict[str, str], retired: set[str], problems: list[str]) -> None:
    """A new page's path, from its stem, in *directory*: refused, never numbered, when its folder's list already has the
    name (*taken*, existing or given to an earlier row; see lay_out), when the name is reserved, or when the card move
    ledger records the address. A numbered name could hide a duplicate, and no existing file is ever written over."""
    here = directory.relative_to(wiki.ROADMAP).as_posix()
    stem = page.row.data["stem"]
    clash = taken.get(stem.casefold())
    reserved = stem_problem(stem)
    if reserved:
        clash = reserved
    elif f"{here}/{stem}" in retired:
        clash = f"the address {PREFIX}{here}/{stem}, which scripts/card-moves.jsonl records"
    if clash:
        problems.append(f"{page.row.where()}: its stem {stem} collides with {clash}, in {repo_path(directory)}; a stem "
                        "is never numbered, as a numbered name could hide a duplicate")
        return
    page.slug, page.path = stem, directory / f"{stem}.md"
    taken[stem.casefold()] = f"the new page {repo_path(page.path)}"


def layout_problems(pages: dict[str, Page], tops: dict[str, list], named: bool) -> list[str]:
    """The pages of the manifest that the layout does not hold exactly once, and, once pages are named (*named*), those
    without a path of their own below blueprint/roadmap/, and so without one links file (sync_wiki.links_file): a
    regression in the layout is refused by name, never written and never a crash."""
    held = Counter(id(node) for kids in tops.values() for kid in kids
                   for node in (wiki.walk(kid) if isinstance(kid, wiki.Container) else (kid,))
                   if isinstance(node, Page))
    paths = Counter(page.path for page in pages.values())
    problems = []
    for page in pages.values():
        count = held[id(page)]
        if count != 1:
            places = "no place" if count == 0 else f"{count} places"
            problems.append(f"{page.row.where()}: the layout gives its page {places}, not one, so nothing is "
                            "written")
        elif named and (page.path.suffix != ".md" or not page.path.is_relative_to(wiki.ROADMAP)
                        or paths[page.path] > 1):
            problems.append(f"{page.row.where()}: the layout gives its page no path of its own, so nothing is "
                            "written")
    return problems


def only_insertions(old: bytes, new: bytes) -> bool:
    """Whether *new* is *old* with lines inserted and none changed or removed."""
    before, after = old.decode("utf-8").split("\n"), new.decode("utf-8").split("\n")
    opcodes = difflib.SequenceMatcher(a=before, b=after, autojunk=False).get_opcodes()
    return all(tag in ("equal", "insert") for tag, *_ in opcodes)


def in_step_copy(text: str, part: Path, old_part: str, new_part: str) -> tuple[str | None, list[str]]:
    """A folder page split into parts, *text*, with its copy of the list of *part* in step with the part's new list,
    and the lines it gains. The copy is the items under the heading that links the part, which
    sync_wiki.with_part_lists keeps as the part's entries (sync_wiki.part_entries), each linked through the part. The
    page as it is when no heading links the part; None when the copy is not the part's list as it stands, when either
    page is not simple, or when the edited page would not show the copy as meant (sync_wiki.verify_edit)."""
    link = f"{part.name}/README.md"
    body = text.rstrip("\n")
    lines = body.split("\n")
    at = next((number for number, line in enumerate(lines)
               if (heading := sync.PART_HEADING.match(line)) and heading.group(2) == link), None)
    if at is None:
        return text, []
    old, new = sync.part_entries(old_part), sync.part_entries(new_part)
    if not old or new is None or not sync.simple_page(body, code=True):
        return None, []

    def copy(entries: list) -> list[tuple[str, str]]:
        return [(f"- [{title}]({part.name}/{page}){rest}", f"{part.name}/{page}") for title, page, rest in entries]

    start = at + 1
    while start < len(lines) and not lines[start].strip():
        start += 1
    end = start
    while end < len(lines) and sync.LIST_ITEM.match(lines[end]):
        end += 1
    if lines[start:end] != [line for line, _ in copy(old)]:
        return None, []
    refreshed = [line for line, _ in copy(new)]
    edited = "\n".join(lines[:start] + refreshed + lines[end:]) + text[len(body):]
    ordinal = sum(bool(re.match(r"#{1,6}(?: |$)", line)) for line in lines[:at])
    if not sync.verify_edit(text, edited, [(line, href, (ordinal, lines[at])) for line, href in copy(new)]):
        return None, []
    return edited, [line for line in refreshed if line not in lines[start:end]]


def link_item(page: Page, ref, pages: dict[str, Page]) -> tuple[str, str]:
    """A list item linking what *ref* names (see endpoint) from *page*, titled as its page is, and the address it
    links."""
    kind, value = ref
    target = pages[value].path if kind == "row" else value
    title = pages[value].title if kind == "row" else (sync.page_heading(target.read_text(encoding="utf-8"))
                                                      or target.stem)
    href = wiki.rel(page.path.relative_to(wiki.VAULT), target.relative_to(wiki.VAULT))
    return f"- [{wiki.link_text(title)}]({href})", href


def link(page: Page, ref, pages: dict[str, Page]) -> str:
    """A list item linking what *ref* names (see endpoint) from *page*, titled as its page is (see link_item)."""
    return link_item(page, ref, pages)[0]


def one_link(line: str, href: str) -> bool:
    """Whether Autoform reads *line*, a list item or heading the importer writes, as one link, to *href*
    (autoform_cli.markdown.link_targets): a title can break Markdown's link syntax, as one ending in a backslash
    does."""
    return link_targets(line) == (href,)


def listing_problems(container: wiki.Container, body: str) -> list[str]:
    """Each child a new folder page, *body*, does not list as one link to its page or folder (see one_link): the
    folder's pages and subfolders, and, when it is split into parts, each part and the part's children, linked through
    the part (generate_wiki.render_container)."""
    here = container.path.relative_to(wiki.VAULT)
    items = [line for line in body.split("\n") if re.match(r"(?:- |#{2,3} )\[", line)]
    nodes = list(container.children)
    if nodes and all(isinstance(node, wiki.Container) and node.navigation == "transparent" for node in nodes):
        nodes += [child for part in container.children for child in part.children]
    problems = []
    for node in nodes:
        href = wiki.rel(here, node.path.relative_to(wiki.VAULT))
        if not any(one_link(line, href) for line in items):
            who = node.row.where() if isinstance(node, Page) else f"{repo_path(node.path.parent)}/"
            problems.append(f"{who}: {repo_path(container.path)} would not list it as one link to {href}: its title "
                            f"{node.title!r} breaks Markdown's link syntax")
    return problems


def page_sections(page: Page, refs: list, pages: dict[str, Page]) -> list[tuple[str, str]]:
    """A new page's sections, each its title and its text; see docs/mathgraph-import.md, "Pages". A dependency
    section with nothing to list is left out: no section claims that the page has no prerequisite."""
    data = page.row.data
    statement = [link(page, ref, pages) for kind, ref in refs if kind == "statement"]
    proof = [link(page, ref, pages) for kind, ref in refs if kind == "proof"]
    sections = []
    if data["sketch"] is not None:
        sections.append((SKETCH, data["sketch"]))
    # What a good expansion of the node contains (Nodes still to expand), kept out of the statement.
    if data["prose_missing"] is not None:
        sections.append(("Expansion", data["prose_missing"]))
    if statement:
        sections.append(("Depends on", "\n".join(statement)))
    if proof:
        sections.append(("Proof depends on", "\n".join(proof)))
    sections.append(("Sources", "\n".join(f"- {source}" for source in data["sources"])))
    return sections


def page_text(page: Page, sections: list[tuple[str, str]]) -> str:
    """A new page's Markdown: its title, its statement and its *sections* (see page_sections)."""
    data = page.row.data
    parts = [f"# {data['title']}", data["statement"], *(f"## {title}\n\n{text}" for title, text in sections)]
    return "\n\n".join(parts) + "\n"


def read_as_written(page: Page, text: str, sections: list[tuple[str, str]]) -> bool:
    """Whether Autoform reads a new page's *text* as the importer wrote it (autoform_cli.markdown.article_parts):
    its statement, and its *sections*, each with its title and its text."""
    parts = article_parts(text)
    return parts.statement == page.row.data["statement"] and [(section.title, section.body)
                                                              for section in parts.sections] == sections


def page_annotation(row: Row, path: Path) -> dict:
    """The annotation of a row's page at *path*: its fresh id and seed; the pending prerequisites and `not_ready` flag
    of a page that has any; and for a Mathlib-credited row, its Lean link to Mathlib's repository with the declaration
    and its module, and Autoform's `mathlib` flag (docs/BLUEPRINT.md, "Mathlib-credited pages"). Never a `kind` or a
    `status`, which lean-facts derives."""
    data = row.data
    annotation: dict = {"subject": [{"type": "generic", "uri": "../" + path.relative_to(wiki.VAULT).as_posix()}],
                        "id": article_id(data["seed"])}
    if data["kind"] == "mathlib":
        annotation["object"] = [{"type": "lean", "uri": sync.MATHLIB, "location": {
            "declaration": data["mathlib"]["declaration"], "module": data["mathlib"]["module"]}}]
    own: dict = {"seed": {name: data["seed"][name] for name in ("source", "node", "revision")}}
    extensions: dict = {sync.OWN: own}
    if data["pending"]:
        own["pending"] = [{name: entry[name] for name in ("key", "kind", "reason")} for entry in data["pending"]]
        extensions[sync.NAMESPACE] = {"not_ready": True}
    if data["kind"] == "mathlib":
        extensions[sync.NAMESPACE] = {"mathlib": True}
    annotation["extensions"] = extensions
    return annotation


def map_row(row: Row, pages: dict[str, Page]) -> dict:
    """The row scripts/mathgraph-map.jsonl gets for a manifest row: a record of what was applied, from which upstream
    changes can be told later; see docs/mathgraph-import.md, "The map"."""
    data = row.data
    digests = ("statement_sha256", "sketch_sha256", "mg_statement_sha256", "mg_sketch_sha256", "reference_sha256",
               "edges_sha256")
    # In the order map_line writes, so that each line the importer adds is as map_problems requires.
    line = {"key": row.key, "node": data["seed"]["node"], "revision": data["seed"]["revision"],
            "page": repo_path(pages[row.key].path), **{name: data[name] for name in digests},
            "pending": [{name: entry[name] for name in ("key", "kind", "reason")} for entry in data["pending"]]}
    if data["kind"] == "mathlib":
        line["mathlib"] = {"declaration": data["mathlib"]["declaration"], "module": data["mathlib"]["module"],
                           "rev": pinned_mathlib()[0]}
    return line


def after_own_list(text: str, line: str) -> str | None:
    """A folder page that is not simple (sync_wiki.simple_page), which the sync only appends to, with *line* after the
    last item of its own list (sync_wiki.own_list): None when the page could hold raw HTML or a code fence
    (sync_wiki.uncertain), has no own list, or would not render as meant (sync_wiki.verify_edit, as for the sync's
    own edits)."""
    body = text.rstrip("\n")
    if sync.uncertain(body):
        return None
    blocks = sync.blocks(body)
    own = sync.own_list(blocks)
    if not own:
        return None
    at = max(own) + 1
    edited = blocks[:at] + [line] + blocks[at:]
    above = [block for block in edited[:at] if re.match(r"#{1,6}(?: |$)", block)]
    result = "\n".join(edited) + text[len(body):]
    href = re.search(r"\]\(([^()\s]+)\)$", line).group(1)
    under = (len(above) - 1, above[-1] if above else "")
    return result if sync.verify_edit(text, result, [(line, href, under)]) else None


def listing_edit(readme: Path, kids: list, problems: list[str]) -> tuple[bytes, list[tuple[str, str]]]:
    """An existing folder page with an item for each new child, added by sync_wiki.add_to_listing to a copy, so that
    nothing is written, and each item with how it was placed: a new folder after the folders the page lists, a new page
    at the end of its own list. On a page the sync only appends to, the item goes after the page's own list instead
    (see after_own_list), which the plan names. An item that cannot be placed so is refused, and so is any edit that
    would change a line of the page."""
    old = readme.read_bytes()
    lines = []
    with tempfile.TemporaryDirectory() as directory:
        copy = Path(directory) / "README.md"
        copy.write_bytes(old)
        for kid in sorted(kids, key=lambda kid: not isinstance(kid, wiki.Container)):
            href = kid.path.relative_to(readme.parent).as_posix()
            line = f"- [{wiki.link_text(kid.title)}]({href})"
            if not one_link(line, href):
                who = kid.row.where() if isinstance(kid, Page) else f"{repo_path(kid.path.parent)}/"
                problems.append(f"{who}: {repo_path(readme)} would not list it as one link to {href}: its title "
                                f"{kid.title!r} breaks Markdown's link syntax")
                continue
            folders = [page for page in sync.listed_links(copy) if page.endswith("/README.md")]
            saved, rule = copy.read_bytes(), "lists a new child"
            outcome = sync.add_to_listing(copy, line, folders if isinstance(kid, wiki.Container) else [])
            if outcome == "appended":
                copy.write_bytes(saved)
                text, newline = sync.read_page(copy)
                edited = after_own_list(text, line)
                if edited is not None:
                    sync.write_page(copy, edited, newline)
                    outcome, rule = "", "fallback insertion on a non-simple folder page"
            if outcome:
                problems.append(f"{repo_path(readme)}: {line!r} cannot be listed: the page may hold raw HTML or a code "
                                "fence, has no list of its own pages, or would not show the item where it belongs")
            lines.append((line, rule))
        new = copy.read_bytes()
    if not only_insertions(old, new):
        problems.append(f"{repo_path(readme)}: the listing would change an existing line; a folder page only gains "
                        "lines")
    return new, lines


def written_dependencies(page: Path, problems: list[str]) -> list[Path]:
    """The pages an existing page's dependency sections link (`## Depends on`, `## Proof depends on` and
    `## Informally uses`), as Autoform reads its sections and links; none for a path that is no page of the wiki, and
    none, with a problem, for a page that is or lies below a symbolic link, which is not read."""
    if not page.is_relative_to(wiki.ROADMAP):
        return []
    unsafe = symlink_problem(page)
    if unsafe:
        problems.append(f"{unsafe} (a page the new dependencies reach)")
        return []
    if not page.is_file():
        return []
    found = []
    for section in article_parts(page.read_text(encoding="utf-8")).sections:
        if section.title.casefold() in DEPENDENCY_SECTIONS:
            for target in link_targets(section.body):
                split = urlsplit(target)
                if not split.scheme and not split.netloc and split.path.endswith(".md"):
                    found.append(Path(os.path.normpath(page.parent / unquote(split.path))))
    return found


def cycle(edges: dict[Path, list[Path]], problems: list[str]) -> list[Path] | None:
    """A dependency cycle through a new page, over the new pages' *edges* and the dependency sections of the existing
    pages they reach (see written_dependencies), or None."""
    index: dict[Path, int] = {}
    paths: list[Path] = []
    uses: list[Counter] = []

    def node(path: Path) -> int:
        if path not in index:
            index[path] = len(paths)
            paths.append(path)
            uses.append(Counter())
        return index[path]

    for path in edges:
        node(path)
    todo, done = list(reversed(edges)), set()
    while todo:
        path = todo.pop()
        if path in done:
            continue
        done.add(path)
        for target in edges[path] if path in edges else written_dependencies(path, problems):
            uses[node(path)][node(target)] += 1
            todo.append(target)
    for group in wiki.strongly_connected(list(range(len(paths))), uses):
        new = sorted(number for number in group if paths[number] in edges)
        if len(group) < 2 or not new:
            continue
        # A shortest way from the first new page back to it inside the group.
        start, previous, queue = new[0], {new[0]: None}, deque([new[0]])
        while queue:
            current = queue.popleft()
            for used in uses[current]:
                if used == start:
                    chain = [start]
                    while current is not None:
                        chain.append(current)
                        current = previous[current]
                    return [paths[number] for number in reversed(chain)]
                if used in group and used not in previous:
                    previous[used] = current
                    queue.append(used)
    return None


def make_plan(manifest: Path, digest: str) -> Plan:
    """Every check, and the change they allow; Refused when any check fails."""
    # The manifest's one path, which read_manifest checks and opens, and the plan names.
    manifest = Path(os.path.abspath(manifest))
    data = read_manifest(manifest, digest)
    problems: list[str] = []
    rows, raw = parse_rows(data, problems)
    unsafe = input_problems()
    if unsafe:
        raise Refused(problems + unsafe)
    known = read_wiki(problems)
    resolved = check_rows(rows, raw, known, problems)
    problems += mathlib_problems(rows)
    if problems:
        raise Refused(problems)
    taxonomy = wiki.load_taxonomy()
    fields, topics = field_folders(taxonomy), topic_folders(taxonomy)
    count = Counter(row.data["page_dir"].removeprefix(PREFIX) for row in rows)
    why: dict[int, str] = {}
    created: dict[str, wiki.Container] = {}
    children: dict[str, list] = defaultdict(list)

    def make(folder: str) -> bool:
        """Plan a folder, and the folders above it that the wiki lacks; False when one cannot be made."""
        if folder in created or os.path.lexists(wiki.ROADMAP / folder / "README.md"):
            return True
        parent, _, slug = folder.rpartition("/")
        for taken in (wiki.ROADMAP / folder, wiki.ROADMAP / f"{folder}.md"):
            if os.path.lexists(taken):
                problems.append(f"{PREFIX}{folder}/ cannot be made a folder: {repo_path(taken)} is there"
                                + (", a symbolic link" if taken.is_symlink() else ""))
                return False
        if folder in known.retired:
            problems.append(f"{PREFIX}{folder}/ cannot be made a folder: scripts/card-moves.jsonl records the address")
            return False
        if not make(parent):
            return False
        if folder in fields:
            spec = fields[folder]
            container = wiki.Container(spec["title"], slug, [], prose=spec["description"])
            why[id(container)] = f"the {field_kind(folder)} {folder} of scripts/taxonomy.json, which has no folder yet"
        else:
            to, title, key = topics[folder]
            container = wiki.Container(title, slug, [])
            why[id(container)] = f"topic {title!r}, which the placement {key} defines"
        created[folder] = container
        children[parent].append(container)
        return True

    pages: dict[str, Page] = {}
    for row in rows:
        found = home(row, fields, topics, count, problems)
        unsafe = symlink_problem(wiki.ROADMAP / found[0] / "README.md") if found else None
        if unsafe:
            problems.append(f"{row.where()}: {unsafe}")
            continue
        holder = card_holding(wiki.ROADMAP / found[0], known.cards) if found else None
        if holder is not None:
            problems.append(f"{row.where()}: its folder {PREFIX}{found[0]} is in the card {repo_path(holder)}/, which "
                            "holds only the statements its editors place in it (docs/cards.md)")
        elif found and make(found[0]):
            pages[row.key] = Page.of(row, found[1])
            children[found[0]].append(pages[row.key])
    if problems:
        raise Refused(problems)
    # A page's own prerequisites among the new pages, which generate_wiki.dependency_order orders siblings by.
    for key, page in pages.items():
        for kind, (ref, value) in resolved[key]:
            if ref == "row":
                (page.depends if kind == "statement" else page.proof_depends).append(pages[value])

    def build(folder: str) -> None:
        """Build a new folder from its children, as generate_wiki.subject_tree builds one: each new subfolder first,
        with its own children in place, then the folder's children in the generator's order (see generator_order), a
        subfolder titled like the folder flattened into it, and, above wiki.MAX_CHILDREN entries, split into parts as
        generate_wiki splits such a list, named by number."""
        container, kids = created[folder], children[folder]
        for kid in kids:
            if isinstance(kid, wiki.Container):
                build(f"{folder}/{kid.slug}")
        ordered = generator_order(folder, container.title, kids, fields)
        for kid in kids:
            if isinstance(kid, wiki.Container) and all(kid is not node for node in ordered):
                # Flattened by generate_wiki.namesake_first: the folder holds the topic's pages itself.
                for page in wiki.articles(kid):
                    page.why = (f"{PREFIX}{folder}, which holds the pages of topic {kid.title!r} itself, as "
                                "generate_wiki.namesake_first lays out a topic titled like its folder")
        container.children = wiki.chunk(container.title, container.slug, ordered, ranges=False).children
        for part in container.children:
            if isinstance(part, wiki.Container) and part.navigation == "transparent":
                why[id(part)] = (f"a transparent part of {PREFIX}{folder}, which would hold {len(ordered)} entries, "
                                 f"above the {wiki.MAX_CHILDREN} generate_wiki.chunk allows")

    # The new folders, from their children up; an existing folder keeps its children where they are.
    for folder in created:
        if folder.rpartition("/")[0] not in created:
            build(folder)
    tops: dict[str, list] = {}
    for folder, kids in children.items():
        if folder not in created:
            readme = wiki.ROADMAP / folder / "README.md"
            unsafe = symlink_problem(readme)
            if unsafe or not readme.is_file():
                problems.append(unsafe or f"{repo_path(readme)} is not a file")
                continue
            tops[folder] = grouped(folder, kids, known, why, problems)
    if problems:
        raise Refused(problems)
    problems += layout_problems(pages, tops, named=False)
    if problems:
        raise Refused(problems)
    # One list, and one set of names, per folder and its transparent parts, existing and new; pages take their names in
    # manifest order, so that of two rows with one stem in a folder's list, the later is refused.
    names: dict[Path, dict[str, str]] = {}
    placed: list[tuple[Page, Path, dict[str, str]]] = []
    for folder, kids in tops.items():
        logical = logical_folder(wiki.ROADMAP / folder)
        if logical not in names:
            names[logical] = existing_names(logical)
        lay_out(wiki.ROADMAP / folder, kids, names[logical], known.retired, problems, placed)
    for page, directory, taken in sorted(placed, key=lambda item: item[0].row.line):
        name_page(page, directory, taken, known.retired, problems)
    if problems:
        raise Refused(problems)
    problems += layout_problems(pages, tops, named=True)
    if problems:
        raise Refused(problems)

    creates: dict[Path, str] = {}
    edits: dict[Path, tuple[bytes, bytes]] = {}
    report: list[tuple[str, str, str]] = []
    annotations: dict[Path, list[dict]] = defaultdict(list)
    containers = [node for kids in tops.values() for kid in kids if isinstance(kid, wiki.Container)
                  for node in wiki.walk(kid) if isinstance(node, wiki.Container)]
    taken_ids = set(known.ids) | {article_id(row.data["seed"]) for row in rows}
    for container in containers:
        fields_of, body = sync.split_frontmatter(wiki.render_container(container, None))
        creates[container.path] = body
        problems += listing_problems(container, body)
        report.append(("folder", f"{repo_path(container.path.parent)}/",
                       why.get(id(container), "a transparent part that generate_wiki.chunk makes")))
        report.append(("file", repo_path(container.path), "its folder page"))
        annotation: dict = {"subject": [{"type": "generic",
                                         "uri": "../" + container.path.relative_to(wiki.VAULT).as_posix()}],
                            "id": folder_id(container.path.parent, digest)}
        if annotation["id"] in taken_ids:
            problems.append(f"{repo_path(container.path)}: its id {annotation['id']} is already taken")
        taken_ids.add(annotation["id"])
        if "navigation" in fields_of:
            annotation["extensions"] = {sync.NAMESPACE: {"navigation": fields_of["navigation"]}}
        annotations[sync.links_file(container.path)].append(annotation)
    edges: dict[Path, list[Path]] = {}
    for key, page in pages.items():
        refs = resolved[key]
        sections = page_sections(page, refs, pages)
        creates[page.path] = page_text(page, sections)
        if not read_as_written(page, creates[page.path], sections):
            problems.append(f"{page.row.where()}: Autoform would read the statement or the sections of its page "
                            "otherwise than the importer writes them, so its text would change the page's structure")
        for _, ref in refs:
            line, href = link_item(page, ref, pages)
            if not one_link(line, href):
                problems.append(f"{page.row.where()}: {line!r} would not be one link to {href}, as the title it shows "
                                "breaks Markdown's link syntax; its dependency would be lost")
        what = "Mathlib-credited" if page.row.data["kind"] == "mathlib" else "planned"
        report.append(("file", repo_path(page.path), f"the {what} page of {key}, in {page.why}"))
        annotations[sync.links_file(page.path)].append(page_annotation(page.row, page.path))
        edges[page.path] = [pages[value].path if kind == "row" else value for _, (kind, value) in refs]
    for folder, kids in tops.items():
        readme = wiki.ROADMAP / folder / "README.md"
        new, lines = listing_edit(readme, kids, problems)
        edits[readme] = (readme.read_bytes(), new)
        report += [("line", f"{repo_path(readme)}: {line}", rule) for line, rule in lines]
    # A folder page split into parts copies each part's list, which the sync keeps in step: a part that gains a page
    # gains it in that copy too.
    for readme in [path for path in edits if sync.PART.fullmatch(path.parent.name)]:
        parent = readme.parent.parent / "README.md"
        unsafe = symlink_problem(parent)
        if unsafe or not parent.is_file():
            problems.append(unsafe or f"{repo_path(parent)} is not a file")
            continue
        old, current = edits.get(parent, (parent.read_bytes(), parent.read_bytes()))
        old_part, new_part = (version.decode("utf-8") for version in edits[readme])
        text, lines = in_step_copy(current.decode("utf-8"), readme.parent, old_part, new_part)
        if text is None or not only_insertions(old, text.encode("utf-8")):
            problems.append(f"{repo_path(parent)}: its copy of the list of {repo_path(readme.parent)}/ cannot be kept "
                            "in step with the part's new items: the copy is not the part's list as it stands, a page "
                            "is not simple, or the copy would not show as meant (sync_wiki.with_part_lists)")
        elif lines:
            edits[parent] = (old, text.encode("utf-8"))
            report += [("line", f"{repo_path(parent)}: {line}", "copies the part's new item, as "
                        "sync_wiki.with_part_lists keeps a part's list") for line in lines]

    def add(path: Path, rows_out: list[dict], why_row, place) -> None:
        """Add *rows_out* to the JSON lines file *path*, each as json.dumps writes it, where *place* (the file's bytes,
        empty when it is not there yet, and the rows) puts them: a file that is not there yet is made of them alone."""
        report.extend(("line", f"{repo_path(path)}: {json.dumps(entry, ensure_ascii=False)}", why_row(entry))
                      for entry in rows_out)
        unsafe = symlink_problem(path)
        if unsafe or os.path.lexists(path) and not path.is_file():
            problems.append(unsafe or f"{repo_path(path)} is not a file")
        elif os.path.lexists(path):
            old = path.read_bytes()
            edits[path] = (old, place(old, rows_out))
        else:
            creates[path] = place(b"", rows_out).decode("utf-8")
            report.append(("file", repo_path(path), "a new file for the rows below"))

    def appended(old: bytes, rows_out: list[dict]) -> bytes:
        """*old* and *rows_out* after it, a line feed ending *old* first if it has none."""
        return (old + b"\n" * bool(old and not old.endswith(b"\n"))
                + "".join(json.dumps(entry, ensure_ascii=False) + "\n" for entry in rows_out).encode("utf-8"))

    def inserted(old: bytes, rows_out: list[dict]) -> bytes:
        """The links file *old* with *rows_out* where the sync puts rows (sync_wiki.inserted), with the links folder's
        current defaults. On an unchanged, valid checkout the file's content raises no error here: read_wiki has read
        every links file as the sync does (sync_wiki.read_annotations, which decodes it as UTF-8 and parses each of its
        rows) and each row's subject (sync_wiki.subject_path, the read_subject that row_order makes), stopping the run
        otherwise, and the rows the importer adds are its own. A failing stat, open or read, as of the folder's
        defaults, and a file changed while the importer runs are not covered."""
        return sync.inserted(old.decode("utf-8"), rows_out).encode("utf-8")

    if any(row.data["kind"] == "mathlib" for row in rows):
        problems += written_credit_problems(rows, pages, annotations)
    # A links file takes each row where the sync puts one (sync_wiki.inserted): right after the row whose page's path
    # comes last before its own, wherever that row stands, or first if none does. The map only grows at its end.
    for path, rows_out in annotations.items():
        add(path, rows_out, lambda entry: f"the annotation of blueprint/{entry['subject'][0]['uri'][3:]}, right after "
            "the row whose page's path comes last before its own, wherever that row stands, or first if none does",
            inserted)
    add(MAP, [map_row(row, pages) for row in rows], lambda entry: f"the map row of {entry['key']}, at its end", appended)
    if MAP in creates or MAP in edits:
        written = edits[MAP][1] if MAP in edits else creates[MAP].encode("utf-8")
        problems += [f"the map the change would write is refused: {problem}"
                     for problem in map_problems(written, repo_path(MAP))[1]]
    for path, text in creates.items():
        # Autoform's check of what the site may publish, which sync_wiki.published applies to a folder page's edit.
        errors = publishable_article(text)[1] if path.suffix == ".md" else ()
        if errors:
            problems.append(f"{repo_path(path)}: render would show it as typed, as Autoform's check of what the site "
                            f"may publish finds: {'; '.join(errors)}")
    found = cycle(edges, problems)
    if found:
        problems.append("the new dependencies close a cycle: " + " -> ".join(repo_path(path) for path in found))
    # Every path written, and the folders on its way, again: no symbolic link, and nothing where a file is made.
    for path in [*creates, *edits]:
        unsafe = symlink_problem(path)
        if unsafe:
            problems.append(unsafe)
        elif path in creates and os.path.lexists(path):
            problems.append(f"{repo_path(path)} is there; the importer writes over no file")
    if len(creates) + len(edits) > MAX_CHANGED_FILES:
        problems.append(f"the change touches {len(creates) + len(edits):,} files; a graph PR stays under 3,000")
    if problems:
        raise Refused(problems)
    return Plan(manifest, digest, rows, creates, edits, report)


class SymlinkFound(Exception):
    """A symbolic link on a path being written or put back, found while the change was being written or undone."""


def identity(found: os.stat_result) -> tuple[int, int]:
    """What tells a file or folder from any other while it is there: its device and inode."""
    return found.st_dev, found.st_ino


def entry(folder: int, name: str) -> os.stat_result | None:
    """What *name* is in *folder* (a descriptor), its own lstat, not followed if it is a link; None if nothing is."""
    try:
        return os.stat(name, dir_fd=folder, follow_symlinks=False)
    except FileNotFoundError:
        return None


def open_folder(directory: Path) -> int:
    """A descriptor of *directory*, a folder in the repository, opened one component at a time from the repository
    root, each with O_NOFOLLOW, so that no symbolic link on the way is ever followed, whatever changes meanwhile:
    SymlinkFound names a component that is a link, and OSError says why another cannot be opened."""
    descriptor, at = os.open(wiki.ROOT, os.O_RDONLY | os.O_DIRECTORY), wiki.ROOT
    try:
        for part in directory.relative_to(wiki.ROOT).parts:
            at = at / part
            try:
                inner = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=descriptor)
            except OSError:
                found = entry(descriptor, part)
                if found is not None and stat.S_ISLNK(found.st_mode):
                    raise SymlinkFound(f"{repo_path(at)} is a symbolic link") from None
                raise
            descriptor, previous = inner, descriptor
            os.close(previous)
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def unlink_quietly(folder: int, name: str) -> None:
    try:
        os.unlink(name, dir_fd=folder)
    except FileNotFoundError:
        pass


def staged(folder: int, path: Path, data: bytes, mode: int | None,
           steps: list[list] | None = None) -> tuple[str, tuple[int, int], list | None]:
    """A new file beside *path*, in its folder *folder* (a descriptor), holding *data*, with *mode* or a new file's
    default: its name, its identity and, with *steps*, its step. With *steps*, the temporary file is a step of apply's
    transaction: recorded, with its parent's identity, before it is made, and with its own as soon as it is, so that
    undo removes it if it is left (see undo_step); the caller marks the step done once the file is gone."""
    temporary = f".{path.name}.{os.getpid()}.part"
    step = None
    if steps is not None:
        step = ["temporary", path.with_name(temporary), identity(os.fstat(folder)), None, False]
        steps.append(step)
    try:
        descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o666, dir_fd=folder)
    except FileExistsError:
        if step is not None:
            steps.pop()
        raise
    try:
        with os.fdopen(descriptor, "wb") as handle:
            made = identity(os.fstat(handle.fileno()))
            if step is not None:
                step[3] = made
            handle.write(data)
            if mode is not None:
                os.fchmod(handle.fileno(), mode)
        return temporary, made, step
    except BaseException:
        unlink_quietly(folder, temporary)
        if step is not None:
            step[4] = True
        raise


def make_folder(folder: Path, steps: list[list]) -> None:
    """Make *folder* in its parent, opened by open_folder; mkdir fails when anything is at the path, a link included.
    The step is recorded with the parent's identity, and the folder's once it is made, as undo checks them."""
    parent = open_folder(folder.parent)
    try:
        step = ["folder", folder, identity(os.fstat(parent)), None]
        steps.append(step)
        try:
            os.mkdir(folder.name, dir_fd=parent)
        except FileExistsError:
            steps.pop()
            raise
        step[3] = identity(os.stat(folder.name, dir_fd=parent, follow_symlinks=False))
    finally:
        os.close(parent)


def create_file(path: Path, data: bytes, steps: list[list]) -> None:
    """Put *data* in a new file at *path*: a new file beside it, in the parent opened by open_folder, linked into place
    with os.link, which fails when anything is at the path, a link included, so that no entry is ever replaced, then
    unlinked from beside it. The step is recorded with the parent's identity and the new file's before it is linked,
    and marked once it is; the new file beside it is a step of its own (see staged), done once it is unlinked."""
    parent = open_folder(path.parent)
    try:
        found = entry(parent, path.name)
        if found is not None and stat.S_ISLNK(found.st_mode):
            raise SymlinkFound(f"{repo_path(path)} is a symbolic link; the importer reads and writes no path "
                               "through one")
        if found is not None:
            raise FileExistsError(f"{repo_path(path)} appeared while the change was being written")
        temporary, made, kept = staged(parent, path, data, None, steps)
        step = ["create", path, identity(os.fstat(parent)), made, False]
        steps.append(step)
        os.link(temporary, path.name, src_dir_fd=parent, dst_dir_fd=parent)
        step[4] = True
        os.unlink(temporary, dir_fd=parent)
        kept[4] = True
    finally:
        os.close(parent)


def edit_file(path: Path, data: bytes, steps: list[list]) -> None:
    """Put *data* in the existing regular file at *path*, in the parent opened by open_folder: a new file beside it,
    with its mode, moved into place with os.replace, so that the path holds its old bytes or the new ones, never part
    of them. The step is recorded with the parent's identity, the file's and the new file's, before it is moved; the
    new file beside it is a step of its own (see staged), done once it is moved."""
    parent = open_folder(path.parent)
    try:
        found = entry(parent, path.name)
        if found is None or not stat.S_ISREG(found.st_mode):
            kind = "a symbolic link" if found is not None and stat.S_ISLNK(found.st_mode) else "no regular file"
            raise SymlinkFound(f"{repo_path(path)} is {kind} now; the importer reads and writes no path "
                               "through one")
        mode = stat.S_IMODE(found.st_mode)
        temporary, made, kept = staged(parent, path, data, mode, steps)
        steps.append(["edit", path, identity(os.fstat(parent)), (identity(found), made), mode])
        os.replace(temporary, path.name, src_dir_fd=parent, dst_dir_fd=parent)
        kept[4] = True
    finally:
        os.close(parent)


def undo_step(plan: Plan, step: list) -> tuple[str | None, str | None]:
    """Undo one of apply's steps in its parent, opened by open_folder from the repository root without following a
    link, and only once the parent is the folder the step was taken in and the file or folder is the one the run made,
    as their identities show: an edited file gets its bytes and mode back, through a new file moved into place there,
    and a file or folder the run made goes, a temporary file left beside a file it wrote included (see staged). A
    folder whose identity the run never recorded, its mkdir interrupted before the record, goes only under the
    exclusive-worktree assumption, when it is empty, and is named. Return why the step is left undone, or None, and
    what was removed under that assumption, or None."""
    kind, path, parent_identity = step[:3]
    if kind == "temporary" and step[4]:
        # Done: the file is gone, unlinked or moved into place by the run.
        return None, None
    try:
        parent = open_folder(path.parent)
    except SymlinkFound as error:
        return f"{error}; nothing is undone through it", None
    except FileNotFoundError:
        return f"its folder {repo_path(path.parent)} is gone", None
    try:
        if identity(os.fstat(parent)) != parent_identity:
            return (f"its folder {repo_path(path.parent)} is not the one the change was written in, so nothing is "
                    "undone in it"), None
        found = entry(parent, path.name)
        if kind == "temporary":
            made = step[3]
            if found is None:
                pass
            elif made is not None and stat.S_ISREG(found.st_mode) and identity(found) == made:
                os.unlink(path.name, dir_fd=parent)
            elif made is None:
                return ("this run did not record it, its creation interrupted before the record, so it is left as it "
                        "is"), None
            else:
                return "it is not the temporary file this run made, so it is left as it is", None
        elif kind == "create":
            made, landed = step[3], step[4]
            if found is not None and stat.S_ISREG(found.st_mode) and identity(found) == made:
                os.unlink(path.name, dir_fd=parent)
            elif found is not None and landed:
                return "it is not the file this run made, so it is left as it is", None
        elif kind == "folder":
            made = step[3]
            if found is None:
                pass
            elif made is not None and stat.S_ISDIR(found.st_mode) and identity(found) == made:
                # Proven to be this run's: the identity it recorded when it made the folder.
                os.rmdir(path.name, dir_fd=parent)
            elif made is None and stat.S_ISDIR(found.st_mode):
                # The instant between mkdir and the record of the folder's identity. The path was absent at the
                # check just before mkdir, and the step, with its parent's identity, was recorded before it; the
                # folder found there is taken for this run's only because the worktree is the importer's alone by
                # contract (see apply), and goes only if it is empty, in the verified parent: rmdir removes no folder
                # that holds anything.
                try:
                    os.rmdir(path.name, dir_fd=parent)
                except OSError as error:
                    if error.errno not in (errno.ENOTEMPTY, errno.EEXIST):
                        raise
                    return ("this run did not record it, its mkdir interrupted before the record, and it is not empty, "
                            "so it is left as it is"), None
                return None, (f"{repo_path(path)} was removed as the folder this run made, under the "
                              "exclusive-worktree assumption: it appeared in the instant between the importer's mkdir "
                              "and its record, and it was empty, in the verified parent")
            else:
                return "it is not the folder this run made, so it is left as it is", None
        else:
            (original, made), mode = step[3], step[4]
            same = found is not None and stat.S_ISREG(found.st_mode)
            if same and identity(found) == original:
                return None, None
            if not same or identity(found) != made:
                return "it is not the file this run wrote, so it is not restored", None
            temporary, _, _ = staged(parent, path, plan.edits[path][0], mode)
            try:
                os.replace(temporary, path.name, src_dir_fd=parent, dst_dir_fd=parent)
            except BaseException:
                unlink_quietly(parent, temporary)
                raise
        return None, None
    finally:
        os.close(parent)


def undo(plan: Plan, steps: list[list]) -> tuple[list[str], list[str]]:
    """Undo apply's *steps*, last first (see undo_step), leaving any other entry at a step's path as it is. Each step is
    recorded before it is taken, so one that never happened is undone harmlessly. Return what could not be undone, and
    what was removed under the exclusive-worktree assumption."""
    left, assumed = [], []
    for step in reversed(steps):
        try:
            problem, note = undo_step(plan, step)
        except OSError as error:
            problem, note = str(error), None
        if problem:
            left.append(f"{repo_path(step[1])} ({problem})")
        if note:
            assumed.append(note)
    return left, assumed


def apply(plan: Plan) -> None:
    """Write the plan as one transaction, once nothing it was made from has changed: nothing is at a path it creates
    yet, every file it edits still holds the bytes it was read with, and no path it writes is or lies below a symbolic
    link, as symbolic links are refused on every repository path it writes or removes (a check that fails writes
    nothing). Each write happens in its parent folder, opened from the repository root without following a link (see
    open_folder), and checks its path again there: a folder is made by make_folder and a new file goes in by
    create_file, neither of which ever replaces an entry, and an edited file by edit_file, with the bytes staged in the
    plan. If an exception or an interruption stops the writing, each step taken is undone where undo can verify it (see
    undo), and Refused says whether the tree is as it was or names what could not be put back. The worktree is assumed
    to be the importer's alone while it runs: some concurrent changes are found, and refused or reported as an
    incomplete rollback, but none is guarded against. A crash or a power loss is not covered: run on a clean worktree,
    which git restores."""
    problems = []
    for path in plan.creates:
        unsafe = symlink_problem(path)
        if unsafe or os.path.lexists(path):
            problems.append(unsafe or f"{repo_path(path)} exists now")
    for path, (old, _) in plan.edits.items():
        unsafe = symlink_problem(path)
        if unsafe or not path.is_file() or path.read_bytes() != old:
            problems.append(unsafe or f"{repo_path(path)} changed since the plan was made")
    if problems:
        raise Refused(problems)
    steps: list[list] = []
    try:
        for path, text in plan.creates.items():
            for folder in reversed([folder for folder in path.parents if not os.path.lexists(folder)]):
                make_folder(folder, steps)
            create_file(path, text.encode("utf-8"), steps)
        for path, (_, new) in plan.edits.items():
            edit_file(path, new, steps)
    except BaseException as error:
        left, assumed = undo(plan, steps)
        failed = f"the write failed ({type(error).__name__}: {error})"
        if left:
            raise Refused([failed, *(f"could not undo the change to {item}" for item in left), *assumed],
                          "the tree is NOT as it was: restore it with `git checkout -- . && git clean -fd`") from error
        raise Refused([f"{failed}; every change was undone, so the tree is as it was", *assumed]) from error


def print_plan(plan: Plan, applied: bool) -> None:
    kinds = Counter(row.data["kind"] for row in plan.rows)
    print(f"Manifest {plan.manifest}: SHA-256 {plan.digest}, {len(plan.rows)} rows ({kinds['planned']} planned, "
          f"{kinds['mathlib']} Mathlib-credited)")
    for section, title in (("folder", "Folders to create"), ("file", "Files to create"), ("line", "Lines to add")):
        entries = [(item, rule) for kind, item, rule in plan.report if kind == section]
        print(f"\n{title}: {len(entries)}")
        for item, rule in entries:
            print(f"  {item}\n      {rule}")
    print(f"\nChanged files: {len(plan.creates) + len(plan.edits):,} (at most {MAX_CHANGED_FILES:,})")
    print("Written." if applied else "Nothing written (--check).")


def print_identity(argument: str) -> int:
    """Print an existing page's identity (see page_identity) as JSON, or say why it can be no dependency."""
    path = Path(os.path.normpath(argument))
    if path.is_absolute() and path.is_relative_to(wiki.ROOT):
        path = path.relative_to(wiki.ROOT)
    target = path.as_posix()
    if path.is_absolute() or not target.startswith(PREFIX):
        print(f"error: {argument} is not below {PREFIX}", file=sys.stderr)
        return 1
    if not re.fullmatch(MANIFEST_SCHEMA["$defs"]["page"]["pattern"], target):
        print(f"error: {target} is no page a manifest can name: it does not match the manifest schema's page pattern",
              file=sys.stderr)
        return 1
    identity, problems = None, input_problems()
    if not problems:
        identity, problems = page_identity(target, read_wiki([]))
    for problem in problems:
        print(f"error: {problem}", file=sys.stderr)
    if identity is None or problems:
        return 1
    print(json.dumps(identity, ensure_ascii=False))
    return 0


def git(*args: str) -> subprocess.CompletedProcess:
    """A git command run in the repository, its output in bytes; its exit status is the caller's to read."""
    return subprocess.run(["git", "-C", str(wiki.ROOT), *args], capture_output=True, check=False)


def base_map(rev: str) -> tuple[bytes, str]:
    """The map's bytes at the commit *rev* names, read from git, and the commit; empty bytes when the map is absent
    there. Refused when *rev* names no commit of the repository, or the map is no regular file there."""
    relative = MAP.relative_to(wiki.ROOT).as_posix()
    found = git("rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}") if rev and not rev.startswith("-") else None
    if found is None or found.returncode != 0:
        raise Refused([f"--base {rev!r} names no commit of the repository; fetch it first, as Blueprint Pages does "
                       "(git fetch --no-tags --depth=1 origin <commit>)"])
    commit = found.stdout.decode("ascii").strip()
    listed = git("ls-tree", "-z", commit, "--", relative)
    if listed.returncode != 0:
        raise Refused([f"the tree of {commit} cannot be read: {listed.stderr.decode(errors='replace').strip()}"])
    if not listed.stdout:
        return b"", commit
    mode, kind, blob = listed.stdout.split(b"\t", 1)[0].decode("ascii").split()
    if kind != "blob" or mode not in ("100644", "100755"):
        raise Refused([f"{relative} at {commit} is no regular file (mode {mode})"])
    read = git("cat-file", "blob", blob)
    if read.returncode != 0:
        raise Refused([f"{relative} at {commit} cannot be read: {read.stderr.decode(errors='replace').strip()}"])
    return read.stdout, commit


def growth_problems(base: bytes, head: bytes, commit: str) -> list[str]:
    """What keeps the map's bytes *head* from being the map at *commit*, *base*, with lines appended: the base must be
    the head's start, ending at a line break, so that no line of it is edited, removed or moved. Each problem names
    the first line that differs."""
    if head.startswith(base) and (not base or base.endswith(b"\n")):
        return []
    label, rule = repo_path(MAP), "the map only grows: lines are appended to it, never edited, removed or moved"
    before, after = base.split(b"\n"), head.split(b"\n")
    for lines in (before, after):
        if lines[-1] == b"":
            lines.pop()
    for number, line in enumerate(before, 1):
        if number > len(after):
            return [f"{label} line {number}: line {number} of the map at {commit} is gone; {rule}"]
        if after[number - 1] != line:
            moved = next((index for index, other in enumerate(after, 1) if other == line), None)
            what = f"that line is now line {moved}" if moved else "that line is edited or removed"
            return [f"{label} line {number}: not line {number} of the map at {commit}: {what}; {rule}"]
    if base.endswith(b"\n"):
        return [f"{label} line {len(before)}: line {len(before)} no longer ends in a line break, as it does in the map "
                f"at {commit}; {rule}"]
    return [f"{label} line {len(before)}: the map at {commit} does not end in a line break there; {rule}"]


def paths_at(commit: str, paths: list[str]) -> set[str]:
    """Which of *paths*, repository paths read literally, the tree of *commit* holds, read from git."""
    listed = git("--literal-pathspecs", "ls-tree", "-r", "-z", "--name-only", commit, "--", *paths)
    if listed.returncode != 0:
        raise Refused([f"the tree of {commit} cannot be read: {listed.stderr.decode(errors='replace').strip()}"])
    return {name.decode("utf-8", errors="replace") for name in listed.stdout.split(b"\0")} & set(paths)


def appended_problems(appended: list[tuple[int, dict]], commit: str, label: str) -> list[str]:
    """What keeps each line appended to the map since *commit* from recording a page the same change adds, as an import
    writes them: the page is not in the commit's tree and is a file in the worktree, with no symbolic link on its path;
    it has exactly one annotation row, whose seed is the line's (source mathgraph, the line's node and revision), whose
    id is the one that seed gives (article_id), whose pending list, none when it records none, is the line's, and which
    credits, as sync_wiki reads it (page_owner), the Mathlib declaration and module of the line's `mathlib`, which no
    other page credits, to Mathlib or as a declaration of this project (claimants), and whose rev is the one
    lake-manifest.json pins, or nothing when the line has no `mathlib`; and the line's statement_sha256 and
    sketch_sha256 are those of the page (statement_sha256, sketch_sha256). The line's mg_statement_sha256,
    mg_sketch_sha256, reference_sha256 and edges_sha256 come from mathgraph, which the importer does not read, and are
    not checked; nor is whether the declaration is Mathlib's. The lines of the map at *commit* are never checked against
    the pages, which may have moved since."""
    if not appended:
        return []
    problems = input_problems()
    if problems:
        return problems
    before = paths_at(commit, [row["page"] for _, row in appended])
    owners, doubled, _, _ = annotation_owners()
    # The pages crediting each Mathlib declaration an appended line records (claimants), and the Mathlib revision
    # lake-manifest.json pins.
    names = {row["mathlib"]["declaration"] for _, row in appended if "mathlib" in row}
    claims = claimants(sync.read_annotations(), names) if names else {}
    pinned = pinned_mathlib() if names else (None, None)
    for number, row in appended:
        where, page = f"{label} line {number} ({row['key']}), appended since {commit}", wiki.ROOT / row["page"]
        unsafe = symlink_problem(page)
        if row["page"] in before:
            problems.append(f"{where}: its page {row['page']} is in the tree of {commit} already, so this change did "
                            "not add it")
            continue
        if unsafe or not page.is_file():
            problems.append(f"{where}: {unsafe}" if unsafe else f"{where}: its page {row['page']} is no file in the "
                            "worktree, so this change did not add it")
            continue
        annotation = owners.get(page.resolve())
        if annotation is None or page.resolve() in doubled:
            problems.append(f"{where}: its page {row['page']} has "
                            f"{'no annotation' if annotation is None else 'more than one annotation row'}")
            continue
        seed = {"source": "mathgraph", "node": row["node"], "revision": row["revision"]}
        extensions = annotation.get("extensions")
        own = extensions.get(sync.OWN) if isinstance(extensions, dict) else None
        own = own if isinstance(own, dict) else {}
        if own.get("seed") != seed:
            problems.append(f"{where}: the seed of its page's annotation is {json.dumps(own.get('seed'))}, not the "
                            f"line's {json.dumps(seed)}")
        if annotation.get("id") != article_id(seed):
            problems.append(f"{where}: its page's annotation id is {json.dumps(annotation.get('id'))}, not "
                            f"{article_id(seed)}, which the line's seed gives")
        if own.get("pending", []) != row["pending"]:
            problems.append(f"{where}: its pending list is not that of its page's annotation, "
                            f"{json.dumps(own.get('pending', []), ensure_ascii=False)}")
        try:
            statement, found = statement_sha256(page), sketch_sha256(page)
        except UnicodeDecodeError as error:
            problems.append(f"{where}: its page is not UTF-8: {error}")
            continue
        if row["statement_sha256"] != statement:
            problems.append(f"{where}: statement_sha256 is {row['statement_sha256']}, but its page's statement, as "
                            f"Autoform reads it, has the SHA-256 {statement}")
        if found is None:
            problems.append(f"{where}: its page has more than one `## {SKETCH}` section")
        elif row["sketch_sha256"] != found:
            problems.append(f"{where}: sketch_sha256 is {row['sketch_sha256']}, but its page's sketch, as Autoform "
                            f"reads it (the empty string when it has none), has the SHA-256 {found}")
        credit = row.get("mathlib")
        expected = ("mathlib", credit["declaration"], credit["module"]) if credit else ("none", None, None)
        try:
            owner = sync.page_owner(annotation)
        except sync.CreditError as error:
            problems.append(f"{where}: {error}")
        else:
            if owner != expected:
                problems.append(f"{where}: its page's annotation credits {credit_text(owner)}, as sync_wiki reads it, "
                                f"not {credit_text(expected)}")
        if credit:
            problems += [f"{where}: {problem}" for problem in claim_problems(credit["declaration"],
                                                                             claims[credit["declaration"]], own=page)]
        if credit and credit["rev"] != pinned[0]:
            problems.append(f"{where}: mathlib/rev is {credit['rev']}, not the Mathlib revision lake-manifest.json "
                            f"pins: {pinned[1] or pinned[0]}")
    return problems


def check_map(rev: str | None) -> int:
    """--check-map: check every line of the map (see map_problems) and, with *rev*, that it only grows from the map at
    that commit (see growth_problems) and that each line appended since records a page the change adds (see
    appended_problems); print what is wrong, or what was checked. Writes nothing."""
    label = repo_path(MAP)
    try:
        unsafe = symlink_problem(MAP)
        if unsafe or os.path.lexists(MAP) and not MAP.is_file():
            raise Refused([unsafe or f"{label} is not a file"])
        head = MAP.read_bytes() if os.path.lexists(MAP) else b""
        rows, problems = map_problems(head, label)
        if rev is not None:
            base, commit = base_map(rev)
            older, found = map_problems(base, f"{label} at {commit}")
            problems += found + growth_problems(base, head, commit)
            if not problems:
                problems += appended_problems(rows[len(older):], commit, label)
        if problems:
            raise Refused(problems)
    except Refused as refused:
        for problem in refused.problems:
            print(f"error: {problem}", file=sys.stderr)
        print(f"{len(refused.problems)} problems; nothing written", file=sys.stderr)
        return 1
    if rev is None:
        print(f"{label}: {len(rows)} valid lines; nothing written (--check-map)")
    else:
        print(f"{label}: {len(rows)} valid lines; the {len(older)} lines of the map at {commit} are its first, "
              f"unchanged, and {len(rows) - len(older)} are appended, each recording a page this change adds, with its "
              "annotation and its statement and sketch digests; nothing written (--check-map)")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Apply a reviewed mathgraph manifest to the ATLAS wiki "
                                                 "(docs/mathgraph-import.md).")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="check everything and print the change; write nothing")
    mode.add_argument("--apply", action="store_true", help="check everything and write the change")
    mode.add_argument("--identity", metavar="PAGE", help="print the identity a dependency on an existing page is bound "
                                                         "to, from the repository root; write nothing")
    mode.add_argument("--check-map", action="store_true", help="check every line of scripts/mathgraph-map.jsonl and, "
                                                              "with --base, that it only grows and that each new line "
                                                              "records a page the change adds; write nothing")
    parser.add_argument("--base", metavar="REV", help="with --check-map: the commit whose map must be the map's start")
    parser.add_argument("--manifest", type=Path, help="the reviewed manifest, JSON Lines")
    parser.add_argument("--manifest-sha256", help="the SHA-256 of the reviewed manifest")
    args = parser.parse_args(argv)
    if args.base is not None and not args.check_map:
        parser.error("--base goes with --check-map")
    if args.check_map:
        return check_map(args.base)
    if args.identity is not None:
        return print_identity(args.identity)
    if args.manifest is None or args.manifest_sha256 is None:
        parser.error("--check and --apply need --manifest and --manifest-sha256")
    try:
        plan = make_plan(args.manifest, args.manifest_sha256)
        if args.apply:
            apply(plan)
    except Refused as refused:
        for problem in refused.problems:
            print(f"error: {problem}", file=sys.stderr)
        print(f"{len(refused.problems)} problems; {refused.outcome}", file=sys.stderr)
        return 1
    print_plan(plan, args.apply)
    return 0


if __name__ == "__main__":
    sys.exit(main())
