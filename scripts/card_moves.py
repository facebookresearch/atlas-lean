#!/usr/bin/env python3
"""The card move ledger: its files, read the one way every script reads them; the checks of its rows that need no
other file of the repository; and the helpers that write its fragments.

    python scripts/card_moves.py [--repo DIR] [REVISION]
        print the logical ledger of REVISION, or of the checkout, one row a line
    python scripts/card_moves.py check [--base REVISION]
        check the ledger on its own, as the required check of every change does
    python scripts/card_moves.py new-moves SLUG [--take-appended] [--base REVISION]
        start a fragment for a change's rows; with --take-appended, move into it the rows the branch appended to the
        frozen file, beyond the base's (origin/main by default), and restore the frozen file
    python scripts/card_moves.py new-moves --restamp FILE [--base REVISION]
        give a fragment the base does not have a name that sorts after every other fragment

The ledger is the frozen scripts/card-moves.jsonl, then one fragment per change in scripts/card-moves.d/, each named
<YYYYMMDDTHHMMSSZ>-<slug>.jsonl after the UTC time it was made. Its logical order is the frozen file's rows, then
each fragment in byte order of name, each fragment's rows in file order. Every file is read on its own, line by
line, so a file without a final newline never joins two rows. A missing frozen file is an error; a missing or empty
folder of fragments holds none; every entry of that folder is a regular file with a fragment's name, a real UTC time
in it, and at least one row, and anything else is an error. The site hook, which imports nothing from scripts/, keeps
its own copy of this reading, and a test holds the two to one result. Printed, the logical ledger of a revision is
its rows, one a line, in order: what a reader of the single-file ledger expects, from a commit made before the split
or after it.

check reads the ledger's files of the checkout and the rules among its rows that need nothing else (check): each row
has one of the four shapes; an address moves once, as a page or as a folder, and is no retirement's once it moved;
an article moves into an address once; the retirements at an address are one history, each replaced in place by the
next; no chain of moves or of replacements goes round, and every hop of a move keeps its article; each article has
one history, its moves ending where its retirement says, as the kind it is retired as, or at one address if it is
retired as neither; a card's replacements end at no retired statement and no page; what ends at a retired address is
its final replacement; no two articles' moves end at one address, nor at one another moved away from, page and
folder alike; and every row comes after the rows it builds on (order_problems). With --base, a commit: the frozen
file and every fragment of that commit stay as they are (base_problems); each new fragment, one the base does not
have, is stamped no later than an hour past the check's clock (stamp_problems); and no new fragment interacts with a
fragment of the base that sorts after it, nor with another new one (guard). A base that cannot be read is an error,
never an empty one. The guard's one input beyond the ledger is which folders of ROADMAP have a folder page, a
regular file, in the commit checked out, read from Git's tree entries alone, their names, modes and types, no file
of them (live_folders). What needs the rest of the tree is the cards script's, which runs these checks too, in the
jobs that do not gate a merge: whether each chain ends at a live page or folder of its article, what holds a retired
address, the cards, the receipt the site keeps the moved addresses with, and whether every move since the base has
its row.

new-moves names a fragment with the UTC time it was made, or one second after the latest fragment the checkout and
the base hold, if that is later; --restamp renames a fragment the base does not have the same way, keeping its slug
and bytes, so that it sorts after every other one, a published fragment it crossed included. Neither names a
fragment more than an hour ahead of the clock, which the check refuses: each refuses then, and says when it can run;
nor one after a fragment stamped 9999-12-31 23:59:59, the last stamp a name can have: each refuses, naming it, as
waiting will not help. Each refuses a base it cannot read in full: a malformed fragment entry, or no frozen file.
Each writes in the checkout it is run from, the Git top level of the current folder, only when the script run is
that checkout's own scripts/card_moves.py and its scripts/ a real folder (checkout_problem), and writes over no file
and through no link.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import re
import secrets
import stat
import subprocess
import sys
from collections import defaultdict
from collections.abc import Callable, Container
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from itertools import combinations
from pathlib import Path

FROZEN = "scripts/card-moves.jsonl"
FRAGMENTS = "scripts/card-moves.d"
# How messages name a row of the frozen file, `card-moves.jsonl:<line>`; its name in scripts/.
MOVES = "card-moves.jsonl"
# The files of the folder of fragments, as a shell glob over the repository's paths: every fragment is one of them, its
# name then held to FRAGMENT_NAME (name_problem); any other entry of the folder is an error.
FRAGMENT_FILES = "scripts/card-moves.d/*.jsonl"
# ASCII digits only: a stamp of other digits would sort after every ASCII one.
FRAGMENT_NAME = re.compile(r"([0-9]{8}T[0-9]{6}Z)-[a-z0-9][a-z0-9-]*\.jsonl")
SLUG = re.compile(r"[a-z0-9][a-z0-9-]*")
STAMP = "%Y%m%dT%H%M%SZ"
# Git's modes of a regular file.
REGULAR = ("100644", "100755")
# A ledger row's kinds, by its keys.
ROW_KEYS = {"page": {"page", "to", "article_id"}, "folder": {"folder", "to", "article_id"},
            "card": {"card", "folder", "replaced_by"}, "statement": {"statement", "page", "replaced_by"}}
ARTICLE_ID = re.compile(r"af_[0-9a-f]{24}")
# How far ahead of the check's clock a new fragment's stamp may be: it is the UTC time the fragment was made, and one
# far ahead would sort the fragments made after it before it.
AHEAD = 3600
# The folder of the roadmap's pages, from the repository's root: the rows' addresses are paths below it. The check's
# one read beyond the ledger's files is which of its folders have a folder page in the commit checked out, from the
# names, modes and types of Git's tree entries alone, no file of them (live_folders), for the guard.
ROADMAP = "blueprint/roadmap"
# The checkout this file is in, from its resolved path: the one the check reads and the helpers write in, once they
# found it is the checkout they are run from (checkout_problem).
ROOT = Path(__file__).resolve().parent.parent

Files = list[tuple[str, bytes]]


def name_problem(name: str) -> str | None:
    """Why ``name``, an entry of the folder of fragments, is no fragment's: a fragment is one of FRAGMENT_FILES, named
    <YYYYMMDDTHHMMSSZ>-<slug>.jsonl, its stamp a real UTC time."""
    match = FRAGMENT_NAME.fullmatch(name) if fnmatch.fnmatchcase(f"{FRAGMENTS}/{name}", FRAGMENT_FILES) else None
    if match is None:
        return "not a fragment; a fragment is a file named <YYYYMMDDTHHMMSSZ>-<slug>.jsonl"
    try:
        datetime.strptime(match.group(1), STAMP)
    except ValueError:
        return f"not a fragment; {match.group(1)} is no UTC time"
    return None


def content_problem(data: bytes) -> str | None:
    """Why the bytes ``data`` are no fragment's: they are UTF-8 with at least one row, a line that is not blank."""
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return "not UTF-8"
    if not any(line.strip() for line in text.splitlines()):
        return "no row; a fragment holds at least one"
    return None


def read_fragments(folder: Path) -> tuple[Files, list[str]]:
    """The fragments in ``folder`` (a scripts/card-moves.d), each read once, in byte order of name, by path in the
    repository, and what is wrong with the folder; an entry that is no fragment is left out. A missing folder holds
    none."""
    try:
        found = os.lstat(folder)
    except FileNotFoundError:
        return [], []
    if not stat.S_ISDIR(found.st_mode):
        return [], [f"{FRAGMENTS} is no folder"]
    files: Files = []
    problems: list[str] = []
    for name in sorted(os.listdir(folder), key=os.fsencode):
        path = f"{FRAGMENTS}/{name}"
        problem = name_problem(name)
        if problem is None and not stat.S_ISREG(os.lstat(folder / name).st_mode):
            problem = "no regular file"
        if problem is None:
            data = (folder / name).read_bytes()
            problem = content_problem(data)
        if problem is None:
            files.append((path, data))
        else:
            problems.append(f"{path}: {problem}")
    return files, problems


def read_ledger(scripts: Path) -> tuple[Files, list[str]]:
    """The ledger's files in ``scripts``, a folder laid out as the repository's scripts/ (its card-moves.jsonl and
    card-moves.d/), each read once, in logical order, by path in the repository, and what is wrong with them. The
    frozen file comes first: a FileNotFoundError when it is missing; it is a regular file."""
    frozen = scripts / "card-moves.jsonl"
    if not stat.S_ISREG(os.lstat(frozen).st_mode):
        return [], [f"{FROZEN}: no regular file"]
    fragments, problems = read_fragments(scripts / "card-moves.d")
    return [(FROZEN, frozen.read_bytes()), *fragments], problems


def git(repo: Path, *arguments: str) -> bytes:
    """What a git command run in ``repo`` prints; a subprocess.CalledProcessError when it fails."""
    return subprocess.run(["git", "-C", str(repo), *arguments], check=True, capture_output=True).stdout


def tree(repo: Path, treeish: str, *paths: str) -> list[tuple[str, str, str, str]]:
    """The entries `git ls-tree` lists: mode, type, object id and path."""
    listing = git(repo, "ls-tree", "-z", treeish, "--", *paths)
    entries = []
    for entry in filter(None, listing.split(b"\0")):
        head, _, path = entry.partition(b"\t")
        mode, kind, oid = head.decode().split()
        entries.append((mode, kind, oid, os.fsdecode(path)))
    return entries


def object_format(repo: Path) -> str:
    """The repository's object format, `sha1` or `sha256`."""
    try:
        found = git(repo, "rev-parse", "--show-object-format").decode().strip()
    except subprocess.CalledProcessError:
        return "sha1"
    return found if found in ("sha1", "sha256") else "sha1"


def blob_id(data: bytes, form: str = "sha1") -> str:
    """Git's id of a blob of ``data``, in the object format ``form``."""
    return hashlib.new(form, b"blob %d\0" % len(data) + data).hexdigest()


def ledger_blobs(revision: str, repo: Path) -> tuple[dict[str, str], list[str]]:
    """The ledger's files as the commit ``revision`` has them, by path in the repository, as Git blob ids, read from
    its trees alone, and what is wrong with them: the frozen file is a regular file, and every entry of the folder of
    fragments one with a fragment's name. A commit with no frozen file has none in the result. A revision that is no
    commit, or a tree Git cannot read, is a subprocess.CalledProcessError, never an empty ledger."""
    commit = git(repo, "rev-parse", "--verify", "--quiet", f"{revision}^{{commit}}").decode().strip()
    blobs: dict[str, str] = {}
    problems: list[str] = []
    for mode, kind, oid, path in tree(repo, commit, FROZEN, FRAGMENTS):
        if path == FROZEN:
            if kind == "blob" and mode in REGULAR:
                blobs[path] = oid
            else:
                problems.append(f"{FROZEN}: no regular file")
        elif path == FRAGMENTS and kind != "tree":
            problems.append(f"{FRAGMENTS} is no folder")
        elif path == FRAGMENTS:
            for mode_in, kind_in, oid_in, name in tree(repo, oid):
                problem = name_problem(name)
                if problem is None and not (kind_in == "blob" and mode_in in REGULAR):
                    problem = "no regular file"
                if problem is None:
                    blobs[f"{FRAGMENTS}/{name}"] = oid_in
                else:
                    problems.append(f"{FRAGMENTS}/{name}: {problem}")
    return blobs, problems


def read_revision(revision: str, repo: Path) -> tuple[Files, list[str]]:
    """The ledger's files as the commit ``revision`` has them, each read once from Git, in logical order, by path in
    the repository, and what is wrong with them, as read_ledger reads a folder: a FileNotFoundError when the commit has
    no frozen file, a commit made before the ledger was."""
    blobs, problems = ledger_blobs(revision, repo)
    if FROZEN not in blobs:
        raise FileNotFoundError(f"{revision}: there is no {FROZEN}")
    files: Files = []
    for path in [FROZEN, *sorted((path for path in blobs if path != FROZEN), key=os.fsencode)]:
        data = git(repo, "cat-file", "blob", blobs[path])
        problem = None if path == FROZEN else content_problem(data)
        if problem is None:
            files.append((path, data))
        else:
            problems.append(f"{path}: {problem}")
    return files, problems


def ledger_rows(files: Files) -> list[tuple[str, int, str]]:
    """Each row of the logical ledger ``files``: its file's path, its line number there and its text, in order; each
    file read on its own, as UTF-8 (a UnicodeDecodeError otherwise), line by line, a blank line being no row."""
    return [(path, number, line) for path, data in files
            for number, line in enumerate(data.decode("utf-8").splitlines(), 1) if line.strip()]


def digest(files: Files) -> str:
    """The digest of the ledger as read, which a moves receipt (`atlas-card-moves/v3`) records and the site hook
    recomputes from the files: sha256 over each file, in logical order, as its path in the repository, a NUL, its
    length in bytes in decimal, a NUL and its bytes."""
    found = hashlib.sha256()
    for path, data in files:
        found.update(path.encode() + b"\0" + str(len(data)).encode() + b"\0" + data)
    return found.hexdigest()


# The rows and the checks among them -----------------------------------------------------------------------------


def row_kind(row: dict) -> str | None:
    """A ledger row's kind, by its keys: `page`, `folder`, `card` or `statement`; None for no row of the ledger."""
    return next((kind for kind, keys in ROW_KEYS.items() if set(row) == keys), None)


def valid_address(value: str) -> bool:
    """A page's or folder's node id: a relative path below roadmap/, without `.md`, `.` or `..` parts."""
    parts = value.split("/")
    return (not value.endswith(".md") and all(part and part not in (".", "..") for part in parts)
            and not value.startswith("/"))


@dataclass(frozen=True)
class LedgerRow:
    """A row of the logical ledger: the file it is in, by path in the repository, its line there, and its fields,
    those of one of the four kinds (ROW_KEYS)."""

    path: str
    number: int
    fields: dict

    @property
    def kind(self) -> str:
        return row_kind(self.fields)

    @property
    def where(self) -> str:
        """How messages name the row: `card-moves.jsonl:<line>` in the frozen file, `<path>:<line>` in a fragment."""
        return f"{MOVES}:{self.number}" if self.path == FROZEN else f"{self.path}:{self.number}"

    @property
    def left(self) -> str:
        """The address the row leaves: a move's old address, a retirement's last one."""
        return self.fields["folder" if self.kind in ("folder", "card") else "page"]

    @property
    def addresses(self) -> tuple[str, ...]:
        """The addresses whose resolution the row sets: a move's old and new address, a retirement's last one."""
        return (self.left, self.fields["to"]) if self.kind in ("page", "folder") else (self.left,)

    @property
    def article(self) -> str:
        """The id the row moves or retires."""
        return self.fields["article_id" if self.kind in ("page", "folder") else self.kind]

    @property
    def names(self) -> set[str]:
        """Every address and id the row names, a retirement's replacement too."""
        return {*self.addresses, self.article, *([self.fields["replaced_by"]] if "replaced_by" in self.fields else [])}


@dataclass
class BaseLedger:
    """The move ledger of the base commit a change is checked against: the Git blob id of each of its files, by path
    in the repository, in the object format ``form``, and the bytes of those read (all of them from a folder; none from
    Git, whose files the checkout's, which must be the base's, stand for)."""

    blobs: dict[str, str]
    data: dict[str, bytes] = field(default_factory=dict)
    form: str = "sha1"


def base_from_folder(folder: Path) -> tuple[BaseLedger | None, list[str]]:
    """The base commit's move ledger from ``folder``, which holds its card-moves.jsonl and card-moves.d/ as scripts/
    does (the card job extracts them there), and what is wrong with it. A folder without the frozen file is an error,
    never an empty base: the base's ledger could not be compared."""
    try:
        files, problems = read_ledger(folder)
    except OSError as error:
        return None, [f"--base-ledger {folder}: the base commit's move ledger cannot be read: {error}"]
    if not files:
        return None, [f"the base commit's {problem}" for problem in problems]
    return (BaseLedger({path: blob_id(data) for path, data in files}, dict(files)),
            [f"the base commit's {problem}" for problem in problems])


def base_at(revision: str, repo: Path) -> tuple[BaseLedger | None, list[str]]:
    """The move ledger of the commit ``revision`` of the repository ``repo``, from Git's trees alone, and what is wrong
    with it: no byte of its files is read, the checkout's own files, which must be the base's, standing for them (a
    sparse, partial checkout such as the graph job's has no blob of the base). A revision Git cannot read, or one
    without the frozen file, is an error, never an empty base."""
    try:
        blobs, problems = ledger_blobs(revision, repo)
    except (OSError, subprocess.CalledProcessError):
        return None, [f"--base {revision}: no commit Git can read here; the base commit's move ledger cannot be "
                      "compared"]
    if FROZEN not in blobs:
        return None, [f"--base {revision}: the commit has no {FROZEN} as a regular file; the base commit's move ledger "
                      "cannot be compared", *(f"the base commit's {problem}" for problem in problems)]
    return (BaseLedger(blobs, {}, object_format(repo)),
            [f"the base commit's {problem}" for problem in problems])


def base_problems(current: dict[str, bytes], base: BaseLedger) -> list[str]:
    """The ledger held to its base's: the frozen file is the base's, byte for byte, and every fragment the base has is
    there under its name, unchanged; a published part is never edited, deleted, renamed or made another kind of
    file. What else the folder of fragments holds is a well-formed new fragment, as read_ledger checks."""
    errors = []
    for path in sorted(base.blobs, key=lambda path: (path != FROZEN, os.fsencode(path))):
        found = current.get(path)
        same = found is not None and blob_id(found, base.form) == base.blobs[path]
        if path == FROZEN:
            if not same:
                errors.append(f"{MOVES} is not the base commit's; it is frozen: move the rows added to it into a "
                              "fragment with `python scripts/card_moves.py new-moves <slug> --take-appended`")
        elif found is None:
            errors.append(f"{path}, a fragment of the base commit, is gone; a published fragment is never deleted, "
                          "renamed or made another kind of file")
        elif not same:
            errors.append(f"{path}, a fragment of the base commit, changed; a published fragment is never edited: put "
                          "new rows in a new fragment (`python scripts/card_moves.py new-moves <slug>`)")
    return errors


def utc_now() -> datetime:
    return datetime.now(timezone.utc)


def stamp_problems(fresh: list[str]) -> list[str]:
    """The new fragments stamped ahead of the check's clock by more than AHEAD: a stamp is the UTC time its fragment
    was made, and one ahead would sort the fragments made after it before it."""
    now = utc_now()
    errors = []
    for path in fresh:
        stamp = datetime.strptime(path.rsplit("/", 1)[1][:16], STAMP).replace(tzinfo=timezone.utc)
        if (stamp - now).total_seconds() > AHEAD:
            errors.append(f"{path} is stamped {stamp:%Y-%m-%d %H:%M:%S} UTC, ahead of this check's clock, "
                          f"{now:%Y-%m-%d %H:%M:%S} UTC; a stamp is the UTC time its fragment was made: restamp it "
                          f"with `python scripts/card_moves.py new-moves --restamp {path}`")
    return errors


def ancestors(address: str) -> list[str]:
    """The folders above ``address``, nearest first, the roadmap's own left out."""
    parts = address.split("/")
    return ["/".join(parts[:end]) for end in range(len(parts) - 1, 0, -1)]


def stable_folders(rows: list[LedgerRow], live: Container[str]) -> Callable[[str], bool]:
    """Whether a folder is there at every point of the ledger's reverse replay (the site hook's history): one of
    ``live``, the folders that have a folder page in the tree checked (live_folders), that no folder row moves in and
    whose address no page row or statement retirement names (an address that was a page's at some point). Undoing a
    folder row takes its new address out of the replay, and a page's address may have been no folder then; any other
    folder may be found gone at some point of the replay, and lead where its nearest enclosing folder leads."""
    unsettled = {row.fields["to"] for row in rows if row.kind == "folder"}
    unsettled.update(address for row in rows if row.kind in ("page", "statement") for address in row.addresses)
    known: dict[str, bool] = {}

    def stable(folder: str) -> bool:
        if folder not in known:
            known[folder] = folder not in unsettled and folder in live
        return known[folder]

    return stable


def live_folders(repo: Path, commit: str = "HEAD") -> frozenset[str]:
    """The folders of ROADMAP that the commit ``commit`` of the repository ``repo`` has a folder page in, by address
    (the path below ROADMAP), as the guard asks of the tree checked (stable_folders): read from Git's tree entries
    below ROADMAP alone, their names, modes and types, no file of them. A folder page is a regular file: an entry of
    that name that is a symbolic link or a submodule makes no folder live. A commit Git cannot read is a
    subprocess.CalledProcessError."""
    listing = git(repo, "ls-tree", "-r", "-z", commit, "--", ROADMAP)
    prefix, page = f"{ROADMAP}/", "/README.md"
    found = set()
    for entry in filter(None, listing.split(b"\0")):
        head, _, name = entry.partition(b"\t")
        mode, kind, _ = head.decode().split()
        path = os.fsdecode(name)
        # The roadmap's own folder page is no folder's below it: no row's address is the roadmap itself.
        if kind == "blob" and mode in REGULAR and path.startswith(prefix) and path[len(prefix):].endswith(page):
            found.add(path[len(prefix):-len(page)])
    return frozenset(found)


def footprint(rows: list[LedgerRow], stable: Callable[[str], bool]) -> tuple[set[str], set[str]]:
    """What the rows of one fragment write and read in the ledger's replay, as `address:<address>` and `id:<id>`. They
    write every address whose resolution a row sets (a move's old and new address, a retirement's last one), every id a
    row moves or retires, and every folder above an address a row leaves that the replay could find gone there and lead
    where its nearest enclosing folder leads: each one up to the first ``stable`` folder (stable_folders). They read
    every folder above an address they write. A retirement's replacement is none of it: the replay resolves it by id at
    the end state, where the combined check follows every replacement chain to its live owner."""
    writes: set[str] = set()
    for row in rows:
        writes.update(f"address:{address}" for address in row.addresses)
        writes.add(f"id:{row.article}")
        for above in ancestors(row.left):
            if stable(above):
                break
            writes.add(f"address:{above}")
    reads = {f"address:{above}" for entry in writes if entry.startswith("address:")
             for above in ancestors(entry.removeprefix("address:"))}
    return writes, reads


def interaction(one: tuple[set[str], set[str]], two: tuple[set[str], set[str]]) -> str | None:
    """What makes two fragments interact, by their footprints: an address or id one writes and the other writes or
    reads (two reads of a folder never do), the first in order; None for none."""
    shared = (one[0] & two[0]) | (one[0] & two[1]) | (one[1] & two[0])
    if not shared:
        return None
    kind, _, value = min(shared).partition(":")
    return f"the {kind} {value}"


def guard(rows: list[LedgerRow], fresh: list[str], published: set[str], live: Container[str]) -> list[str]:
    """The fragments whose order nothing vouches for, and whose rows interact (interaction): each new fragment of
    ``fresh`` and each fragment of the base (``published``) that sorts after it, an interleaving that a restamp of the
    new one undoes; and each two new fragments, which their names do not order, so that no restamp makes them
    independent: their rows go in one fragment, in the order they happened, or one change lands first and the other
    is checked again with it in its base. Fragments that do not interact give one resolution in either order.
    ``live``: the folders that have a folder page in the tree checked (stable_folders)."""
    by_file: dict[str, list[LedgerRow]] = defaultdict(list)
    for row in rows:
        if row.path != FROZEN:
            by_file[row.path].append(row)
    stable = stable_folders(rows, live)
    prints = {path: footprint(found, stable) for path, found in by_file.items()}
    errors = []
    for path in fresh:
        for other in sorted(published & prints.keys(), key=os.fsencode):
            if (path in prints and os.fsencode(other) > os.fsencode(path)
                    and (shared := interaction(prints[path], prints[other]))):
                errors.append(f"{path} sorts before {other}, which the base commit has, and both touch {shared}: "
                              f"restamp it with `python scripts/card_moves.py new-moves --restamp {path}`, so that it "
                              "sorts after it")
    for one, two in combinations(fresh, 2):
        if one in prints and two in prints and (shared := interaction(prints[one], prints[two])):
            errors.append(f"{one} and {two}, both new, touch {shared}: put their rows in one fragment, in the order "
                          "they happened, or land one change first and check the other again with it in its base")
    return errors


def ordering_fix(path: str, later: str, fresh: set[str] | None) -> str:
    """How a new fragment comes after a fragment it builds on that sorts after it: a restamp, past a published one;
    one fragment for the rows, when both are new, since no restamp orders two new fragments for the check. With no
    base, ``fresh`` is None and both are said."""
    restamp = f"restamp yours with `python scripts/card_moves.py new-moves --restamp {path}`"
    together = "put the rows of the two in one fragment, in the order they happened"
    if fresh is None:
        return f": {restamp}; if {later} is new too, {together}"
    return f": {together}" if later in fresh else f": {restamp}"


def order_problems(rows: list[LedgerRow], fresh: set[str] | None) -> list[str]:
    """The rows that come before a row they build on, in the ledger's order, which the site hook's reverse
    replay could not resolve as they happened. A move or retirement of an article builds on the move that
    put it at that address. A retirement in place builds on the retirement there that named it as the replacement. A
    move into an address builds on the retirement there of an earlier occupant whose replacements lead to the article
    moving in, page or folder alike, since a page and a folder of one name share an address: that retirement freed the
    address for it. Retirements there of later occupants, which it handed the address to, are none of its
    prerequisites. ``fresh``, the new fragments when the base is known, chooses the fix (ordering_fix)."""
    shape = {"card": "folder", "statement": "page"}
    replaced = {row.article: row.fields["replaced_by"] for row in rows if row.kind in ("card", "statement")}

    def leads_to(article: str, target: str) -> bool:
        """Whether the replacements of the retired ``article`` reach ``target``."""
        seen = {article}
        while article in replaced:
            article = replaced[article]
            if article == target:
                return True
            if article in seen:
                return False
            seen.add(article)
        return False

    moved_in: dict[tuple[str, str, str], list[int]] = defaultdict(list)
    retired_at: dict[str, list[tuple[int, str]]] = defaultdict(list)
    handed: dict[tuple[str, str], list[int]] = defaultdict(list)
    for position, row in enumerate(rows):
        if row.kind in ("page", "folder"):
            moved_in[(row.kind, row.fields["to"], row.article)].append(position)
        else:
            retired_at[row.left].append((position, row.article))
            handed[(row.left, row.fields["replaced_by"])].append(position)
    errors = []
    for position, row in enumerate(rows):
        if row.kind in ("page", "folder"):
            bases = moved_in[(row.kind, row.left, row.article)] + [
                at for at, retired in retired_at[row.fields["to"]]
                if retired != row.article and leads_to(retired, row.article)]
        else:
            bases = moved_in[(shape[row.kind], row.left, row.article)] + handed[(row.left, row.article)]
        later = sorted(at for at in bases if at > position)
        if not later:
            continue
        built = rows[later[0]]
        if built.path == row.path:
            errors.append(f"{row.where}: it builds on line {built.number}, below it; a file's rows come in the order "
                          "they happened")
        elif FROZEN in (row.path, built.path) or (fresh is not None and row.path not in fresh):
            errors.append(f"{row.where}: it builds on {built.where}, which comes after it in the ledger")
        else:
            errors.append(f"{row.where}: it builds on {built.path}, which sorts after it"
                          f"{ordering_fix(row.path, built.path, fresh)}")
    return errors


@dataclass
class Ledger:
    """What check read of a ledger, for the checks that need the tree as well (the cards script's): its rows, in order;
    each kind's moves, by old address, as (new address, article id); the retired cards and the retired statements, by
    id, as (replacement, last address); the articles the moves leave live, by kind, retired as neither; the new
    fragments, by path, when the base is known (None otherwise); and how to tell a row of a fragment that fails what
    to do (the hint of check)."""

    rows: list[LedgerRow]
    chains: dict[str, dict[str, tuple[str, str]]]
    retired: dict[str, tuple[str, str]]
    statements: dict[str, tuple[str, str]]
    living: dict[str, set[str]]
    fresh: set[str] | None
    hint: Callable[[LedgerRow], str]


def check(files: Files, base: BaseLedger | None = None, live: Container[str] = frozenset()) -> tuple[list[str], Ledger]:
    """The errors of the move ledger ``files`` (read_ledger's: the frozen file, then the fragments) that need no other
    file, each row named by its file and line, and what was read of it. A row is one of the four kinds (ROW_KEYS), its
    ids article ids and its addresses paths below the roadmap. An address has one owner: it moves once, as a page or as
    a folder, never as both; one that moved is no retired card's or statement's last address; and the retirements at an
    address, of cards and of statements apart, are one history, each replaced in place by the next. An article moves
    into an address once, or its history would branch. Every hop of a chain of moves keeps the article id it started
    with, so that an old address always leads to its own article; no chain of moves, and no chain of replacements,
    through the cards and statements retired on the way, goes round; nothing is retired both as a card and as a
    statement. A retired article's chain of moves ends at the address its retirement records, as the kind it is retired
    as (a statement as a page, a card as a folder); every chain of an article retired as neither ends at one address,
    as a page or as a folder; a retired card's replacements end at no retired statement and no article that moved as a
    page; an article the rows leave live at a retired address is that address's final replacement; and no two articles
    retired as neither end at one address, nor does one end at an address another moved away from, page and folder
    alike. Every row comes after the rows it builds on (order_problems). A row of a fragment that fails says which
    fragment sorting after its own names what it names, and how to order the two (the hint). ``base``, the base
    commit's ledger (BaseLedger): the frozen file and every fragment the base has stay as they are (base_problems); the
    new fragments are the ones the base does not have, by path, never by count or position: each is stamped no later
    than the check's clock allows (stamp_problems), and none interacts with a fragment of the base that sorts after it,
    nor with another new one (guard), ``live`` being the folders that have a folder page in the tree checked. Whether
    each chain ends at a live page or folder of its article, and what else holds an address, is for the caller that has
    the tree."""
    errors: list[str] = []
    current = dict(files)
    fresh_paths: set[str] | None = None
    if base is not None:
        errors += base_problems(current, base)
        fresh_paths = {path for path in current if path not in base.blobs}
    rows: list[LedgerRow] = []
    for path, data in files:
        label = MOVES if path == FROZEN else path
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            errors.append(f"{label}: not UTF-8")
            continue
        for number, line in enumerate(text.splitlines(), 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                errors.append(f"{label}:{number}: not JSON")
                continue
            if not isinstance(row, dict) or not all(isinstance(value, str) and value for value in row.values()):
                errors.append(f"{label}:{number}: a row is an object of non-empty strings")
                continue
            if row_kind(row) is None:
                errors.append(f"{label}:{number}: expected {{page, to, article_id}}, {{folder, to, article_id}}, "
                              "{card, folder, replaced_by} or {statement, page, replaced_by}")
                continue
            rows.append(LedgerRow(path, number, row))
    names_by_file: dict[str, set[str]] = defaultdict(set)
    for row in rows:
        names_by_file[row.path] |= row.names

    def hint(row: LedgerRow) -> str:
        """For a row of a fragment that fails: the first fragment sorting after its own whose rows name an address or id
        it names, and how to order the two (ordering_fix)."""
        if row.path == FROZEN or (fresh_paths is not None and row.path not in fresh_paths):
            return ""
        later = next((path for path in sorted(names_by_file, key=os.fsencode) if path != FROZEN
                      and os.fsencode(path) > os.fsencode(row.path) and names_by_file[path] & row.names), None)
        if later is None:
            return ""
        return f"; it builds on {later}, which sorts after it{ordering_fix(row.path, later, fresh_paths)}"

    chains: dict[str, dict[str, tuple[str, str]]] = {"page": {}, "folder": {}}
    # The row that moved each article into each address, by kind: an article arrives at an address once.
    arrivals: dict[tuple[str, str, str], LedgerRow] = {}
    retired: dict[str, tuple[str, str]] = {}
    # A retired statement page, by id: what replaces it, and its last address.
    statements: dict[str, tuple[str, str]] = {}
    # The retirements at each address, of cards and of statements apart, in the ledger's order: row, id, replacement.
    claims: dict[str, dict[str, list[tuple[LedgerRow, str, str]]]] = {"card": defaultdict(list),
                                                                      "statement": defaultdict(list)}
    for row in rows:
        fields, kind = row.fields, row.kind
        if kind in ("page", "folder"):
            if not ARTICLE_ID.fullmatch(fields["article_id"]):
                errors.append(f"{row.where}: `article_id` is not an article id")
            if not (valid_address(fields[kind]) and valid_address(fields["to"])):
                errors.append(f"{row.where}: an address is a path below roadmap/ without `.md`")
            if fields[kind] in chains[kind]:
                errors.append(f"{row.where}: {fields[kind]} already moved{hint(row)}")
            chains[kind][fields[kind]] = (fields["to"], fields["article_id"])
            # Two moves of one article into one address, from two old addresses, would be two branches of one
            # history: it never leaves the address in between, as no address moves twice.
            arrival = (kind, fields["article_id"], fields["to"])
            if arrival in arrivals:
                errors.append(f"{row.where}: {fields['article_id']} moves into {fields['to']} a second time, from "
                              f"{fields[kind]}, after {arrivals[arrival].where} moved it there from "
                              f"{arrivals[arrival].fields[kind]}; an article moves into an address once, or its "
                              "history would branch")
            arrivals.setdefault(arrival, row)
        elif kind == "card":
            if not (ARTICLE_ID.fullmatch(fields["card"]) and ARTICLE_ID.fullmatch(fields["replaced_by"])):
                errors.append(f"{row.where}: `card` and `replaced_by` are article ids")
            if not valid_address(fields["folder"]):
                errors.append(f"{row.where}: an address is a path below roadmap/ without `.md`")
            if fields["card"] in retired:
                errors.append(f"{row.where}: the card {fields['card']} is already retired{hint(row)}")
            retired.setdefault(fields["card"], (fields["replaced_by"], fields["folder"]))
            claims["card"][fields["folder"]].append((row, fields["card"], fields["replaced_by"]))
        else:
            if not (ARTICLE_ID.fullmatch(fields["statement"]) and ARTICLE_ID.fullmatch(fields["replaced_by"])):
                errors.append(f"{row.where}: `statement` and `replaced_by` are article ids")
            if not valid_address(fields["page"]):
                errors.append(f"{row.where}: an address is a path below roadmap/ without `.md`")
            if fields["statement"] in statements:
                errors.append(f"{row.where}: the statement {fields['statement']} is already retired{hint(row)}")
            statements.setdefault(fields["statement"], (fields["replaced_by"], fields["page"]))
            claims["statement"][fields["page"]].append((row, fields["statement"], fields["replaced_by"]))

    # An address has one owner: the retirements at one address are one history, each replaced in place by the next,
    # in the ledger's order; two that are not would be two articles claiming it, and no order may choose between them.
    # Two in the reverse of that order are order_problems'.
    for kind, at_address in claims.items():
        for address, found in sorted(at_address.items()):
            for (_, one, successor), (row, two, then) in zip(found, found[1:]):
                if successor != two and then != one:
                    errors.append(f"{row.where}: {address} is the last address of the retired {kind} {one}, replaced "
                                  f"by {successor}, and of {two}; an address has one owner, so each retirement there "
                                  f"is replaced in place by the next{hint(row)}")

    for old in sorted(set(chains["page"]) & set(chains["folder"])):
        errors.append(f"{MOVES}: {old} moved both as a page and as a folder; an address has one owner")
    # Where each chain of moves leaves its article, by kind and old address, unless it goes round: a retired article
    # was retired where the rows leave it, as the kind it moved as; an article retired nowhere ends where it lives.
    ends: dict[tuple[str, str], tuple[str, str]] = {}
    for kind, chain in chains.items():
        for old in sorted(chain):
            seen, at, article_id = {old}, *chain[old]
            while at in chain:
                if at in seen:
                    errors.append(f"{MOVES}: the moves of {old} go round")
                    break
                seen.add(at)
                if chain[at][1] != article_id:
                    errors.append(f"{MOVES}: {old} moved as {article_id} to {at}, which moved on as {chain[at][1]}; "
                                  "an old address must keep leading to its own article")
                at, article_id = chain[at]
            else:
                ends[(kind, old)] = (at, article_id)
                if kind == "page" and article_id in statements:
                    if statements[article_id][1] != at:
                        errors.append(f"{MOVES}: the page {old} ends at {at}, but its statement {article_id} was "
                                      f"retired at {statements[article_id][1]}")
                elif kind == "page" and article_id in retired:
                    errors.append(f"{MOVES}: the page {old} ends at {at}, but {article_id} was retired as a card, "
                                  "which is a folder")
                if kind == "folder" and article_id in retired:
                    if retired[article_id][1] != at:
                        errors.append(f"{MOVES}: the folder {old} ends at {at}, but its card {article_id} was retired "
                                      f"at {retired[article_id][1]}")
                elif kind == "folder" and article_id in statements:
                    errors.append(f"{MOVES}: the folder {old} ends at {at}, but {article_id} was retired as a "
                                  "statement, which is a page")
    # An article retired as neither lives at one address, as a page or as a folder: every chain of its moves ends
    # there. What ends at an address the ledger retires is that address's final replacement.
    places: dict[str, set[tuple[str, str]]] = defaultdict(set)
    for (kind, _), (at, article) in ends.items():
        if article not in retired and article not in statements:
            places[article].add((at, kind))
    for article, found in sorted(places.items()):
        if len(found) > 1:
            errors.append(f"{MOVES}: the moves of {article} end at {len(found)} addresses, "
                          f"{', '.join(f'{at} as a {kind}' for at, kind in sorted(found))}; an article lives at one "
                          "address, as a page or as a folder")
    living = {kind: {article for article, found in places.items() if any(moved == kind for _, moved in found)}
              for kind in chains}
    holders: dict[str, list[tuple[str, str, str]]] = defaultdict(list)
    for (kind, old), (at, article) in sorted(ends.items()):
        if article in living[kind]:
            holders[at].append((kind, old, article))
    # An address has one owner, page and folder alike, since a page and a folder of one name share it: the moves of two
    # articles retired as neither end at no one address (two paths of one article do), and none ends at an address
    # another article moved away from as the other kind (as the same kind, its chain goes on from there, an error
    # above). Lawful successive owners are retired ones, each handing the address on by its retirement.
    for at, found in sorted(holders.items()):
        claims: dict[str, tuple[str, str]] = {}
        for kind, old, article in found:
            claims.setdefault(article, (kind, old))
        if len(claims) > 1:
            listed = ", ".join(f"{article} from the {kind} {old}" for article, (kind, old) in sorted(claims.items()))
            errors.append(f"{MOVES}: the moves of {len(claims)} articles end at {at}, {listed}; an address has one "
                          "owner")
        for article, (kind, old) in sorted(claims.items()):
            other = "folder" if kind == "page" else "page"
            if at in chains[other] and chains[other][at][1] != article:
                errors.append(f"{MOVES}: {chains[other][at][1]} moved from {at} as a {other}, and the {kind} {old} "
                              f"ends there as {article}; an address has one owner")
    # A retired card's replacements, through the cards retired on the way; a retired statement's, through the
    # statements and cards retired on the way: that they end, at no retired statement or page for a card, is this
    # check's; where they end live is the caller's.
    finals: dict[str, str] = {}
    for card_id in sorted(retired):
        seen, at = {card_id}, retired[card_id][0]
        while at in retired:
            if at in seen:
                errors.append(f"{MOVES}: the replacements of {card_id} go round")
                break
            seen.add(at)
            at = retired[at][0]
        else:
            finals[card_id] = at
            if at in statements:
                errors.append(f"{MOVES}: the retired card {card_id} is replaced by {at}, a retired statement, which is "
                              "no card")
            elif at in living["page"]:
                errors.append(f"{MOVES}: the retired card {card_id} is replaced by {at}, which moved as a page, so is "
                              "no card")
    for card_id, (_, folder) in sorted(retired.items()):
        if folder in chains["page"] or folder in chains["folder"]:
            errors.append(f"{MOVES}: {folder} is the last address of the retired card {card_id} and moved too; an "
                          "address has one owner")
        for kind, old, article in holders.get(folder, []):
            if card_id in finals and article != finals[card_id]:
                errors.append(f"{MOVES}: {folder} is the last address of the retired card {card_id}, replaced by "
                              f"{finals[card_id]}, and the {kind} {old} ends there as {article}; an address has one "
                              "owner")
    folders = {folder for _, folder in retired.values()}
    for statement, (_, address) in sorted(statements.items()):
        if statement in retired:
            errors.append(f"{MOVES}: {statement} is retired both as a card and as a statement")
        seen, at = {statement}, statements[statement][0]
        while at in statements or at in retired:
            if at in seen:
                errors.append(f"{MOVES}: the replacements of {statement} go round")
                at = None
                break
            seen.add(at)
            at = (statements if at in statements else retired)[at][0]
        if address in chains["page"] or address in chains["folder"] or address in folders:
            errors.append(f"{MOVES}: {address} is the last address of the retired statement {statement} and moved or "
                          "was a retired card's too; an address has one owner")
        for kind, old, article in holders.get(address, []):
            if at is not None and article != at:
                errors.append(f"{MOVES}: {address} is the last address of the retired statement {statement}, replaced "
                              f"by {at}, and the {kind} {old} ends there as {article}; an address has one owner")
    errors += order_problems(rows, fresh_paths)
    if base is not None:
        fresh = sorted(fresh_paths - {FROZEN}, key=os.fsencode)
        errors += stamp_problems(fresh) + guard(rows, fresh, set(base.blobs) - {FROZEN}, live)
    return errors, Ledger(rows, chains, retired, statements, living, fresh_paths, hint)


# The helpers that write the ledger ------------------------------------------------------------------------------


def fresh_name(slug: str, fragments: int | None, base: str, leave_out: str | None = None) -> tuple[str, str | None]:
    """The name new-moves gives a fragment of ``slug``, and None; or "" and why it gives none. The name is stamped
    with the current UTC time or, if that is later, one second after the latest stamp among the fragments of the
    checkout's scripts/card-moves.d (``fragments``, a descriptor; None for a missing folder) and of the commit
    ``base``, but ``leave_out``: so it sorts after every one of them, one stamped ahead of the clock (stamp_problems
    lets a new fragment be) or in the same second with a later slug included. It gives none when ``base`` is no
    commit Git can read, or one whose ledger cannot be read in full (read_revision: a malformed entry of
    its scripts/card-moves.d, such as a misnamed file or an empty fragment, or no scripts/card-moves.jsonl), as a base
    is never taken for an empty or partial one; when the latest stamp is 9999-12-31 23:59:59, the last a fragment's
    name can have, after which no
    stamp exists; or when that stamp would be more than AHEAD seconds past the clock, which the check refuses of a new
    fragment, saying when it would not be."""
    now = utc_now()
    unreadable = (f"--base {base} is no commit Git can read here: a new name sorts after every fragment of the "
                  "checkout and of that commit, so it must be read")
    try:
        files, problems = read_revision(base, ROOT)
    except FileNotFoundError as error:
        if not str(error).endswith(f"there is no {FROZEN}"):
            return "", unreadable
        files, problems = [], [f"there is no {FROZEN}"]
    except (OSError, UnicodeDecodeError, subprocess.CalledProcessError):
        return "", unreadable
    # A new name sorts after every fragment of the base: a base whose ledger is malformed or incomplete is none to read.
    if problems:
        return "", (f"--base {base}: the commit's move ledger cannot be read in full ({'; '.join(problems)}): a new "
                    "name sorts after every fragment of the checkout and of that commit, so it must be read")
    known = {path.rsplit("/", 1)[1]: f"{path} at {base}" for path, _ in files if path != FROZEN}
    if fragments is not None:
        known.update({name: f"{FRAGMENTS}/{name}" for name in os.listdir(fragments)})
    known.pop(leave_out, None)
    stamps = [(datetime.strptime(name[:16], STAMP).replace(tzinfo=timezone.utc), where)
              for name, where in known.items() if name_problem(name) is None]
    stamp = now.replace(microsecond=0)
    if stamps:
        latest, where = max(stamps)
        # A name's stamp has four digits for the year: none comes after the last second of 9999.
        if latest == datetime.max.replace(microsecond=0, tzinfo=timezone.utc):
            return "", (f"{where} holds the last stamp a fragment's name can have, {latest:%Y-%m-%d %H:%M:%S} UTC: no "
                        "later four-digit stamp exists, so no fragment can sort after it, and waiting will not help; "
                        "rename or remove that fragment")
        stamp = max(stamp, latest + timedelta(seconds=1))
        if (stamp - now).total_seconds() > AHEAD:
            return "", (f"{where} is stamped {latest:%Y-%m-%d %H:%M:%S} UTC: a fragment sorting after it would be "
                        f"stamped more than an hour ahead of the clock, {now:%Y-%m-%d %H:%M:%S} UTC, which the check "
                        f"refuses of a new fragment; run again at {stamp - timedelta(seconds=AHEAD):%Y-%m-%d %H:%M:%S} "
                        "UTC or later")
    return f"{stamp:%Y%m%dT%H%M%SZ}-{slug}.jsonl", None


class FolderRefused(Exception):
    """A folder of the ledger that the helpers refuse to write in: its message names it as the readers do."""


def checkout_problem() -> str | None:
    """Why the helpers would not write in the checkout they are run from: that checkout is the Git top level of the
    current folder, its scripts/ is a real folder, not a link, the script run is its scripts/card_moves.py, as named
    when run (Path(__file__).absolute(): the links of scripts/ not followed), and ROOT, from this file's resolved
    path, which a link at scripts/ would move to the link's target, is that top level."""
    invoked = Path(__file__).absolute()
    try:
        top = Path(os.path.realpath(git(Path.cwd(), "rev-parse", "--show-toplevel").decode().strip()))
    except (OSError, subprocess.CalledProcessError):
        return "new-moves writes in the checkout it is run from, and the current folder is in no Git checkout"
    try:
        real = stat.S_ISDIR(os.lstat(top / "scripts").st_mode)
    except FileNotFoundError:
        real = False
    if not real:
        return "scripts is no folder"
    if ((invoked.parent.name, invoked.name) != ("scripts", "card_moves.py")
            or Path(os.path.realpath(invoked.parent.parent)) != top or Path(os.path.realpath(ROOT)) != top):
        return (f"{invoked} is not the scripts/card_moves.py of the checkout it is run from, {top}: run that "
                "checkout's own")
    return None


def ledger_folders(make: bool) -> tuple[int, int | None]:
    """Descriptors of the checkout's scripts/ and scripts/card-moves.d, each opened from the folder above it without
    following a symbolic link, so that no write of the helpers lands outside the checkout: a link at either, or
    anything but a folder, is a FolderRefused naming it, as the readers name it. With ``make``, a missing
    scripts/card-moves.d is made; without, it is None."""
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    root = os.open(ROOT, os.O_RDONLY | os.O_DIRECTORY)
    try:
        scripts = os.open("scripts", flags, dir_fd=root)
    except OSError as error:
        raise FolderRefused("scripts is no folder") from error
    finally:
        os.close(root)
    try:
        if make:
            try:
                os.mkdir("card-moves.d", dir_fd=scripts)
            except FileExistsError:
                pass
        try:
            fragments = os.open("card-moves.d", flags, dir_fd=scripts)
        except FileNotFoundError:
            if make:
                raise
            fragments = None
        except OSError as error:
            raise FolderRefused(f"{FRAGMENTS} is no folder") from error
    except BaseException:
        os.close(scripts)
        raise
    return scripts, fragments


def new_moves(argv: list[str]) -> int:
    """The new-moves command (see the module's docstring): 2 for a usage error, 1 for a refusal, which writes
    nothing. It writes in the checkout it is run from (checkout_problem); scripts/ and scripts/card-moves.d are real
    folders and the frozen file a regular file, read and written without following a symbolic link (ledger_folders),
    as the readers require of them."""
    argv, base = option(argv, "--base")
    argv, restamp = option(argv, "--restamp")
    base = base or "origin/main"
    take = "--take-appended" in argv
    argv = [given for given in argv if given != "--take-appended"]
    if (restamp is not None and (argv or take)) or (restamp is None and (len(argv) != 1
                                                                        or not SLUG.fullmatch(argv[0]))):
        print(__doc__, file=sys.stderr)
        return 2
    # Bound to the checkout it is run from, before anything is opened, created, written or renamed.
    if problem := checkout_problem():
        print(f"error: {problem}", file=sys.stderr)
        return 1
    if restamp is not None:
        return restamp_fragment(Path(restamp), base)
    try:
        scripts, fragments = ledger_folders(make=False)
    except FolderRefused as refused:
        print(f"error: {refused}", file=sys.stderr)
        return 1
    try:
        return made_fragment(scripts, fragments, argv[0], base, take)
    finally:
        os.close(scripts)
        if fragments is not None:
            os.close(fragments)


def made_fragment(scripts: int, fragments: int | None, slug: str, base: str, take: bool) -> int:
    """new-moves <slug> [--take-appended] in the folders ``scripts`` and ``fragments`` (descriptors; None for a
    missing scripts/card-moves.d, made here once nothing refuses), the fragment named by fresh_name, which reads the
    base first, for both modes: one it cannot read in full is refused before anything else."""
    name, problem = fresh_name(slug, fragments, base)
    if problem:
        print(f"error: {problem}", file=sys.stderr)
        return 1
    text = published = None
    if take:
        # The frozen file is a regular file, never a link: it is read and restored here.
        try:
            frozen = os.stat(MOVES, dir_fd=scripts, follow_symlinks=False)
        except FileNotFoundError:
            frozen = None
        if frozen is not None and not stat.S_ISREG(frozen.st_mode):
            print(f"error: {FROZEN}: no regular file", file=sys.stderr)
            return 1
        try:
            published = git(ROOT, "show", f"{base}:{FROZEN}")
            descriptor = os.open(MOVES, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=scripts)
            with os.fdopen(descriptor, "rb") as handle:
                mine = handle.read()
        except (OSError, subprocess.CalledProcessError):
            print(f"error: {FROZEN} cannot be read at {base} and here", file=sys.stderr)
            return 1
        if not mine.startswith(published):
            print(f"error: {FROZEN} at {base} is not the start of yours, byte for byte: rebase first", file=sys.stderr)
            return 1
        try:
            added = [line for line in mine[len(published):].decode("utf-8").splitlines() if line.strip()]
            published.decode("utf-8")
        except UnicodeDecodeError:
            print(f"error: {FROZEN} is not UTF-8", file=sys.stderr)
            return 1
        if not added:
            print(f"error: your {FROZEN} has no row beyond {base}'s; there is nothing to take", file=sys.stderr)
            return 1
        text = "".join(f"{line}\n" for line in added)
    if fragments is None:
        os.mkdir("card-moves.d", dir_fd=scripts)
        try:
            fragments = os.open("card-moves.d", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=scripts)
        except OSError:
            print(f"error: {FRAGMENTS} is no folder", file=sys.stderr)
            return 1
        made = True
    else:
        made = False
    try:
        # Made exclusively, in the folder opened above: a file or a link of that name, made since fresh_name looked,
        # is never written over or followed.
        try:
            descriptor = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644, dir_fd=fragments)
        except FileExistsError:
            print(f"error: {FRAGMENTS}/{name} is there already; run again in a second", file=sys.stderr)
            return 1
        if not take:
            os.close(descriptor)
            print(f"{FRAGMENTS}/{name}: add the change's rows to it, one JSON object a line")
            return 0
        # Both or neither: the rows leave the frozen file only as they reach the fragment, which goes if the frozen
        # file cannot be restored; the frozen file is replaced whole, from a file beside it.
        restored = None
        try:
            with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
                handle.write(text)
            while restored is None:
                candidate = f".{MOVES}.{secrets.token_hex(6)}.partial"
                try:
                    staged = os.open(candidate, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644,
                                     dir_fd=scripts)
                except FileExistsError:
                    continue
                restored = candidate
            with os.fdopen(staged, "wb") as handle:
                handle.write(published)
            os.replace(restored, MOVES, src_dir_fd=scripts, dst_dir_fd=scripts)
        except BaseException:
            os.unlink(name, dir_fd=fragments)
            if restored is not None:
                try:
                    os.unlink(restored, dir_fd=scripts)
                except FileNotFoundError:
                    pass
            raise
        print(f"{FRAGMENTS}/{name}: {len(added)} rows taken from {FROZEN}, which is {base}'s again")
        return 0
    finally:
        if made:
            os.close(fragments)


def restamp_fragment(given: Path, base: str) -> int:
    """new-moves --restamp: rename the fragment ``given``, which the commit ``base`` must not have (a published
    fragment keeps its name), to the current UTC time or, if that is later, one second after the latest other fragment
    of the checkout and of ``base`` (fresh_name), keeping its slug and bytes. ``given`` names an entry of the
    checkout's scripts/card-moves.d, a real folder (ledger_folders): its folder is that one, compared by lstat, and
    the entry is a regular file, never a link."""
    try:
        scripts, fragments = ledger_folders(make=False)
    except FolderRefused as refused:
        print(f"error: {refused}", file=sys.stderr)
        return 1
    try:
        return renamed_fragment(fragments, given, base)
    finally:
        os.close(scripts)
        if fragments is not None:
            os.close(fragments)


def renamed_fragment(fragments: int | None, given: Path, base: str) -> int:
    """new-moves --restamp in the folder ``fragments`` (a descriptor; None for a missing scripts/card-moves.d)."""
    path = given if given.is_absolute() else Path.cwd() / given
    name = path.name
    try:
        same_folder = fragments is not None and (os.path.samestat(os.lstat(path.parent), os.fstat(fragments)))
        entry = os.stat(name, dir_fd=fragments, follow_symlinks=False) if same_folder else None
    except FileNotFoundError:
        entry = None
    if entry is None or not stat.S_ISREG(entry.st_mode) or name_problem(name) is not None:
        print(f"error: {given} is no fragment in {FRAGMENTS}", file=sys.stderr)
        return 1
    relative = f"{FRAGMENTS}/{name}"
    try:
        git(ROOT, "rev-parse", "--verify", "--quiet", f"{base}^{{commit}}")
    except (OSError, subprocess.CalledProcessError):
        print(f"error: {base} is no commit here; a fragment it has keeps its name, so it must be read", file=sys.stderr)
        return 1
    if tree(ROOT, f"{base}^{{commit}}", relative):
        print(f"error: {relative} is published at {base}; a published fragment keeps its name", file=sys.stderr)
        return 1
    new, problem = fresh_name(name[len("YYYYMMDDTHHMMSSZ-"):-len(".jsonl")], fragments, base, leave_out=name)
    if problem:
        print(f"error: {problem}", file=sys.stderr)
        return 1
    if new == name:
        print(f"{relative} sorts after every other fragment here and at {base} already")
        return 0
    # Linked, then unlinked, in the folder opened above: the new name is never one a file or a link has.
    try:
        os.link(name, new, src_dir_fd=fragments, dst_dir_fd=fragments, follow_symlinks=False)
    except FileExistsError:
        print(f"error: {FRAGMENTS}/{new} is there already; run again in a second", file=sys.stderr)
        return 1
    os.unlink(name, dir_fd=fragments)
    print(f"{relative} -> {FRAGMENTS}/{new}")
    return 0


def option(argv: list[str], name: str) -> tuple[list[str], str | None]:
    """``argv`` without ``name VALUE``, and VALUE (None when absent); a name without a value is a usage error."""
    if name not in argv:
        return argv, None
    at = argv.index(name)
    if at + 1 >= len(argv):
        raise SystemExit(__doc__)
    return argv[:at] + argv[at + 2:], argv[at + 1]


# The commands ---------------------------------------------------------------------------------------------------


def check_command(argv: list[str]) -> int:
    """The check command (see the module's docstring): 2 for a usage error, 1 for an error of the ledger; it writes
    nothing. It reads the ledger's files of this checkout (ROOT) and, with --base, the base commit's ledger from Git's
    trees (base_at) and which roadmap folders the commit checked out has a folder page in (live_folders)."""
    argv, base = option(argv, "--base")
    if argv:
        print(__doc__, file=sys.stderr)
        return 2
    try:
        files, problems = read_ledger(ROOT / "scripts")
    except FileNotFoundError:
        print(f"error: {MOVES}: missing; the moves check certifies a ledger that exists", file=sys.stderr)
        return 1
    errors = list(problems)
    known = None
    if base is not None:
        known, found = base_at(base, ROOT)
        errors += found
    live: Container[str] = frozenset()
    if known is not None:
        try:
            live = live_folders(ROOT)
        except (OSError, subprocess.CalledProcessError):
            errors.append(f"the commit checked out cannot be read: which folders of {ROADMAP} it has cannot be told")
    found, ledger = check(files, known, live)
    errors += found
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    if errors:
        return 1
    print(f"{len(ledger.rows)} ledger rows checked" + (f" against {base}" if base is not None else ""))
    return 0


def main(argv: list[str]) -> int:
    if argv[:1] == ["check"]:
        return check_command(argv[1:])
    if argv[:1] == ["new-moves"]:
        return new_moves(argv[1:])
    parser = argparse.ArgumentParser(description="Print the logical card move ledger, one row a line.")
    parser.add_argument("revision", nargs="?", help="a commit; the checkout's files when absent")
    parser.add_argument("--repo", type=Path, default=ROOT, help="the repository (this script's by default)")
    arguments = parser.parse_args(argv)
    try:
        if arguments.revision is None:
            files, problems = read_ledger(arguments.repo / "scripts")
        else:
            files, problems = read_revision(arguments.revision, arguments.repo)
        rows = ledger_rows(files)
    except (OSError, UnicodeDecodeError, subprocess.CalledProcessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    for problem in problems:
        print(f"error: {problem}", file=sys.stderr)
    if problems:
        return 1
    sys.stdout.write("".join(f"{line}\n" for _, _, line in rows))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
