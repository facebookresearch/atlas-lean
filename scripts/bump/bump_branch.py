#!/usr/bin/env python3
"""Keep a Lean/Mathlib bump branch close to main. See docs/BUMPS.md.

    scripts/bump/bump_branch.py status [--main REF] [--json]
        How far the checked-out bump branch is behind main, whether merging main now
        conflicts and where, and how much of the tree the bump touches.

    scripts/bump/bump_branch.py merge-main [--main REF] [--no-commit] [--adjacent]
        Merge main into the checked-out bump branch with a merge commit (never a rebase,
        so the bump commit stays exactly what pinned_bump.py produced) and resolve
        provenance row by row, in either layout. When a sharded ledger file conflicts, or
        both sides changed the ledger, the whole ledger is merged by path, since a row can
        sit in its legacy shard on one side and in its module file on the other; a merged row
        goes to its module file if either side keeps it there, and is removed from the
        legacy shard. It refuses to start while the ledger directory has untracked files,
        and saves every ledger file it deletes. A merge across the sharding cutover needs a
        manual provenance resolution. With --adjacent, a conflict where one side rewrote one
        whole doc comment and the other changed the one line next to it (a non-blank line
        with no `/-` or `-/`) is merged too. Other conflicts are left for you: resolve them,
        `git add` them, then run `resolve-manifest`. Before committing, the merge is checked
        with scripts/check_formal_math_sync.py against main, on the exact tree that would be
        committed. Build before pushing either way.

    scripts/bump/bump_branch.py resolve-manifest [--no-commit] [--adjacent] [--regenerate]
        Finish a merge that `merge-main` left open. It replaces only provenance files
        that are as `git merge` left them or its own unedited drafts: the conflicted ones,
        and in the sharded layout the ledger files a moved row leaves or enters. After merging
        main yourself, or to throw away your edits, pass --regenerate (the replaced files
        are saved first); in a merge that merge-main started it still never removes a file
        created since the merge, nor rewrites a clean file edited since. Use --check-only to
        validate a fully staged merge, including one across the sharding cutover, without
        resolving conflicts or committing.

    scripts/bump/bump_branch.py breakage LOG [--main REF] [--since REV]
        Read a failed `lake build` log and list each failing module with the main pull
        requests that changed its file since REV (default: the main commits that the
        latest merge of main brought in): candidates for the cause, not proof of it.

REF defaults to origin/main; fetch it first. The manifest rule: a row only one side
changed takes that side's row. A row both sides changed needs both rows `diverged` and
the file resolved and staged:
- the same file on both sides: every field merged three ways;
- one side changed only the row (its file is the base's): the other side's file, with the
  fields merged three ways and the two rationales combined;
  (two rationales combine when at most one side rewrote the base one: the rewrite
  stays, and the other side's added sentences follow it)
- the staged file is git's clean merge of the two sides, or --adjacent's, even if that
  equals one side: the staged hash, the other fields merged three ways, and the two
  rationales combined (with no base rationale, two different first rationales are
  combined only when the two edits provably touch different lines; otherwise they may
  describe the same edit and go to a person);
- a conflict resolved by keeping main's file: main's row (or the bump's, for the bump's
  file), as long as the other side changed nothing else in the row and only added to
  its rationale (a rewrite, such as a corrected reference, goes to a person).
Anything else, such as a removed row, a file resolved by hand or put back to the merge
base, stops with the rows to finish by hand. The manifest is then left parseable, with
main's version of those rows, for `scripts/check_formal_math_sync.py
--record-divergence` or `--retire`; `git add` it and run resolve-manifest again.
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from collections.abc import Callable
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_formal_math_sync as fms  # noqa: E402  (one manifest format and hash for every writer)

MANIFEST = fms.MANIFEST
CHECKER = "scripts/check_formal_math_sync.py"
PR_NUMBER = re.compile(r"(?:Merge pull request #(\d+)|\(#(\d+)\)\s*$)")
# `lake build` marks a failed job `✖ [12/345] Building Some.Module (8.0s)`.
FAILED_JOB = re.compile(r"✖ \[\d+/\d+\] (?:Building|Built|Compiling|Running) (\S+)")
ERROR_FILE = re.compile(r"^error: (?:\./)*(\S+?\.lean):\d+:\d+:", re.M)
MISSING = object()


class Stop(Exception):
    """A condition the user must handle; the message says how."""


# The checkout the command works on: the one the command runs in.
REPO = Path.cwd()


# File names are never read as path patterns (`Notes[1].lean` must not also match `Notes1.lean`).
GIT_ENV = {**os.environ, "GIT_LITERAL_PATHSPECS": "1"}


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess:
    proc = subprocess.run(["git", *args], cwd=REPO, capture_output=True, text=True, env=GIT_ENV)
    if check and proc.returncode != 0:
        raise Stop(f"git {' '.join(args)} failed:\n{proc.stderr.strip()}")
    return proc


def git_bytes(*args: str) -> bytes | None:
    proc = subprocess.run(["git", *args], cwd=REPO, capture_output=True, env=GIT_ENV)
    return proc.stdout if proc.returncode == 0 else None


def rev(ref: str) -> str:
    return git("rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}", check=False).stdout.strip()


def merge_head() -> str:
    return git("rev-parse", "-q", "--verify", "MERGE_HEAD", check=False).stdout.strip()


def pr_numbers(subjects: list[str]) -> list[int]:
    numbers = []
    for subject in subjects:
        match = PR_NUMBER.search(subject)
        if match:
            numbers.append(int(match.group(1) or match.group(2)))
    return numbers


def rows_by_path(manifest: dict) -> dict[str, dict]:
    return {row["path"]: row for row in manifest["rows"]}


def manifest_rows(text: str) -> dict[str, dict]:
    return rows_by_path(json.loads(text))


def show(spec: str) -> str | None:
    data = git_bytes("show", spec)
    return None if data is None else data.decode("utf-8")


def provenance_at(revision: str) -> dict | None:
    manifest, errors = fms.load_revision(REPO, revision)
    if errors:
        raise Stop(f"cannot read provenance at {revision}:\n  " + "\n  ".join(errors))
    return manifest


# ---------------------------------------------------------------- status


def status(main_ref: str) -> dict:
    head, main = rev("HEAD"), rev(main_ref)
    if not main:
        raise Stop(f"{main_ref} is not a commit; run `git fetch origin main` first")
    base = git("merge-base", head, main).stdout.strip()
    subjects = git("log", "--first-parent", "--format=%s", f"{base}..{main}").stdout.splitlines()
    tree = git("merge-tree", "--write-tree", "--name-only", "-z", "--no-messages", head, main, check=False)
    if tree.returncode not in (0, 1):
        raise Stop(f"git merge-tree failed:\n{tree.stderr.strip()}")
    conflicts = [p for p in tree.stdout.split("\0")[1:] if p] if tree.returncode == 1 else []
    changed = [p for p in git("diff", "--name-only", "--no-renames", "-z", base, head).stdout.split("\0") if p]
    rows_changed = 0
    base_manifest, head_manifest = provenance_at(base), provenance_at(head)
    if base_manifest is not None and head_manifest is not None:
        before = rows_by_path(base_manifest)
        rows_changed = sum(before.get(row["path"]) != row for row in head_manifest["rows"])
    return {
        "head": head,
        "main": main,
        "merge_base": base,
        "main_commits_since": len(subjects),
        "main_prs_since": pr_numbers(subjects),
        "main_since": git("log", "-1", "--format=%cI", base).stdout.strip(),
        "conflicts_with_main": conflicts,
        "toolchain": (show(f"{head}:lean-toolchain") or "").strip(),
        "main_toolchain": (show(f"{main}:lean-toolchain") or "").strip(),
        "files_changed": len(changed),
        "lean_files_changed": sum(1 for path in changed if path.endswith(".lean")),
        "manifest_rows_changed": rows_changed,
    }


def print_status(report: dict) -> None:
    print(f"bump  {report['head'][:12]}  {report['toolchain']}")
    print(f"main  {report['main'][:12]}  {report['main_toolchain']}")
    print(f"behind main by {report['main_commits_since']} commit(s), "
          f"{len(report['main_prs_since'])} pull request(s), since {report['main_since']}")
    print(f"the bump changes {report['files_changed']} file(s), {report['lean_files_changed']} of them Lean, "
          f"and {report['manifest_rows_changed']} manifest row(s)")
    if report["conflicts_with_main"]:
        print(f"merging main now conflicts in {len(report['conflicts_with_main'])} file(s):")
        for path in report["conflicts_with_main"]:
            print(f"  {path}")
    else:
        print("merging main now is clean")


# ---------------------------------------------------------------- manifest


def appended(base: str, text: str) -> str | None:
    """What `text` adds to the rationale `base` as further sentences ("" for nothing), or
    None when `text` rewrites it rather than adding to it."""
    base, text = base.strip(), text.strip()
    if not base:
        return text
    if not text.startswith(base):
        return None
    rest = text[len(base):]
    if not rest:
        return ""
    # Only at a sentence boundary: "X." + " More." or "X" + ". More.".
    ends_sentence = base[-1] in ".!?" and rest[0].isspace()
    starts_sentence = rest[0] in ".;" and (len(rest) == 1 or rest[1].isspace())
    return rest.lstrip(" .;").strip() if ends_sentence or starts_sentence else None


def join_rationale(main_rationale: str, addition: str) -> str:
    """Main's rationale, then the bump's addition as a further sentence. Nothing is dropped
    here as a duplicate: text inside a rationale cannot be told apart from a sentence (a
    Lean name such as `MonoidHom.map_mul` has full stops), so only `combine_rationales`
    drops an addition, and only when both sides added exactly the same text."""
    main_rationale = main_rationale.strip()
    if not addition:
        return main_rationale
    if not main_rationale:
        return addition
    if not main_rationale.endswith((".", "!", "?")):
        main_rationale += "."
    if addition.startswith("Also"):
        return f"{main_rationale} {addition}"
    return f"{main_rationale} Also: {addition}"


def merge_value(base, ours, theirs):
    """Three-way merge of one value (MISSING when absent); MISSING marks a clash too."""
    if ours == theirs or theirs == base:
        return ours, True
    if ours == base:
        return theirs, True
    return MISSING, False


def merge_fields(b, o: dict, t: dict, skip: tuple[str, ...]) -> tuple[dict | None, str | None]:
    """Three-way merge of a row's fields other than `skip`: (row, clashing field)."""
    row = {}
    for key in dict.fromkeys(list(t) + list(o) + list(b or {})):
        if key in skip:
            continue
        value, ok = merge_value((b or {}).get(key, MISSING), o.get(key, MISSING), t.get(key, MISSING))
        if not ok:
            return None, key
        if value is not MISSING:
            row[key] = value
    return row, None


def combine_rationales(b, o: dict, t: dict, mode: str) -> str | None:
    """One rationale for both sides' changes to a row, or None for a person to write.

    mode "same": both sides made the same change to the file, so two different
    rationales are two accounts of one change and are never joined. mode "row": one side
    changed only the row. mode "overlap": both changed the file and the edits may share
    lines (one may contain the other). mode "distinct": the edits provably touch different
    lines (`disjoint_changes`). Otherwise a side that rewrote the base rationale (a
    correction, say) keeps its account, and the other side's added sentences follow it;
    when both rewrote it, or there was no base rationale and the changes may overlap (modes
    "row" and "overlap"), the accounts may contradict each other and a person writes one."""
    base = (b or {}).get("rationale", "").strip()
    mine, theirs = o.get("rationale", "").strip(), t.get("rationale", "").strip()
    if mine in (base, theirs):
        return theirs
    if theirs == base:
        return mine
    if mode == "same" or (mode in ("row", "overlap") and not base):
        return None
    added_by_bump, added_by_main = appended(base, mine), appended(base, theirs)
    if added_by_bump is not None and added_by_bump == added_by_main:
        return theirs
    if added_by_bump is not None:
        return join_rationale(theirs, added_by_bump)
    if added_by_main is not None:
        return join_rationale(mine, added_by_main)
    return None


def merge_both_changed(path: str, b, o: dict, t: dict, versions) -> tuple[dict | None, str, str | None]:
    """The merged row for a row both sides changed: (row, whose, problem).

    `versions(path)` gives the staged file and the file in the bump (ours), in main
    (theirs), in the merge base, and as merged automatically (git, or --adjacent); or
    None while the file is unresolved or differs from what is staged."""
    if o.get("disposition") != "diverged" or t.get("disposition") != "diverged":
        return None, "", f"dispositions {o.get('disposition')} (bump) and {t.get('disposition')} (main)"
    files = versions(path)
    if files is None:
        return None, "", "the file is not resolved and staged, or differs from what is staged"
    data, ours, theirs, base = files["staged"], files["ours"], files["theirs"], files["base"]
    content = ("published_sha256", "rationale")

    def others(row) -> dict:
        return {k: v for k, v in (row or {}).items() if k not in content}

    def combined(whose: str, mode: str, file_changed_from_main: bool):
        """Every field merged three ways, the staged file's hash, both rationales combined."""
        row, clash = merge_fields(b, o, t, content)
        if clash is not None:
            return None, "", f"both sides changed its {clash!r}"
        rationale = combine_rationales(b, o, t, mode)
        if rationale is None:
            why = {"same": "both sides describe the same change differently",
                   "overlap": "both sides' first rationales differ and their edits may overlap",
                   }.get(mode, "the two sides' rationales cannot be combined")
            return None, "", f"{why}; write one rationale that covers both"
        if file_changed_from_main and rationale == t.get("rationale", "").strip():
            return None, "", "the bump's rationale adds nothing to main's; write one for the merged file"
        row["published_sha256"], row["rationale"] = fms.sha256(data), rationale
        return row, whose, None

    if data == ours == theirs:
        return combined("both", "same", False)
    if data == theirs and ours == base:  # the bump changed only the row
        return combined("main", "row", False)
    if data == ours and theirs == base:  # main changed only the row, a correction for instance
        return combined("bump", "row", True)
    if data == base:
        return None, "", "the staged file is back to the merge base, so neither side's rationale holds"
    if data == files["auto"]:
        # Git's own merge (or --adjacent's) keeps both sides' changes, even when it comes out
        # equal to one side because that side's change contains the other's.
        disjoint = data not in (ours, theirs) and disjoint_changes(base, ours, theirs, data)
        return combined("both", "distinct" if disjoint else "overlap", data != theirs)
    # A conflict resolved by keeping one side's file drops the other side's change, and the
    # sentences that side added to describe it; a rewrite of the base rationale (a correction)
    # is not about that change alone, so it needs a person.
    base_rationale = (b or {}).get("rationale", "")
    if data == theirs:
        if others(o) != others(b):
            return None, "", "the staged file is main's, but the bump also changed the row's other fields"
        if appended(base_rationale, o.get("rationale", "")) is None:
            return None, "", "the staged file is main's, but the bump also rewrote the rationale; write one"
        return t, "main", None
    if data == ours:
        if others(t) != others(b):
            return None, "", "the staged file is the bump's, but main also changed the row's other fields"
        if appended(base_rationale, t.get("rationale", "")) is None:
            return None, "", "the staged file is the bump's, but main also rewrote the rationale; write one"
        return o, "bump", None
    return None, "", "the file was resolved by hand: record its rationale with --record-divergence"


def merge_manifest(
    base_text: str, ours_text: str, theirs_text: str, versions: Callable[[str], dict | None]
) -> tuple[str, dict[str, int], list[str]]:
    base, ours, theirs = (json.loads(text) for text in (base_text, ours_text, theirs_text))
    merged, counts, problems = merge_manifest_data(base, ours, theirs, versions)
    return fms.dump_manifest(merged), counts, problems


def merge_manifest_data(
    base: dict, ours: dict, theirs: dict, versions: Callable[[str], dict | None]
) -> tuple[dict, dict[str, int], list[str]]:
    """Row-level three-way merge: (logical manifest, counts, problems).

    `versions` is as for `merge_both_changed`. With problems, each such row is main's
    (or, if main has none, the bump's, else the base's), for a person to finish.
    """
    problems, merged = [], {}
    for key in dict.fromkeys(list(theirs) + list(ours) + list(base)):
        if key == "rows":
            continue
        value, ok = merge_value(
            base.get(key, MISSING), ours.get(key, MISSING), theirs.get(key, MISSING)
        )
        if not ok:
            problems.append(f"top-level field {key!r}: both sides changed it")
            value = theirs.get(key, MISSING)
        if value is not MISSING:
            merged[key] = value
    rows_b, rows_o, rows_t = (rows_by_path(manifest) for manifest in (base, ours, theirs))
    counts = {"main": 0, "bump": 0, "both": 0}
    rows = {}
    for path in sorted(set(rows_b) | set(rows_o) | set(rows_t)):
        b, o, t = (rows.get(path, MISSING) for rows in (rows_b, rows_o, rows_t))
        fallback = next((r for r in (t, o, b) if r is not MISSING), MISSING)
        if b is not MISSING and MISSING in (o, t):
            side = "both sides" if o is t else "the bump" if o is MISSING else "main"
            problems.append(f"{path}: {side} removed the row; rows are never removed (use --retire)")
            rows[path] = fallback
            continue
        if o == t:
            rows[path] = o
            continue
        if o == b:
            rows[path], counts["main"] = t, counts["main"] + 1
            continue
        if t == b:
            rows[path], counts["bump"] = o, counts["bump"] + 1
            continue
        if MISSING in (o, t, b):
            problems.append(f"{path}: both sides added a row, differently")
            rows[path] = fallback
            continue
        row, whose, problem = merge_both_changed(path, b, o, t, versions)
        if problem:
            problems.append(f"{path}: {problem}")
            rows[path] = fallback
        else:
            rows[path], counts[whose] = row, counts[whose] + 1
    merged["rows"] = [rows[path] for path in sorted(rows) if rows[path] is not MISSING]
    return merged, counts, problems


def unmerged_paths() -> list[str]:
    out = git("diff", "--name-only", "--diff-filter=U", "-z").stdout
    return [path for path in out.split("\0") if path]


def auto_merge(base: bytes, ours: bytes, theirs: bytes) -> bytes | None:
    """The file as `git merge-file` merges it cleanly, or as --adjacent would; else None."""
    with tempfile.TemporaryDirectory() as tmp:
        names = []
        for name, data in (("ours", ours), ("base", base), ("theirs", theirs)):
            (Path(tmp) / name).write_bytes(data)
            names.append(str(Path(tmp) / name))
        proc = subprocess.run(["git", "merge-file", "-p", *names], capture_output=True)
    if proc.returncode == 0:
        return proc.stdout
    try:
        texts = [data.decode("utf-8") for data in (base, ours, theirs)]
    except UnicodeDecodeError:
        return None
    if any(text and not text.endswith("\n") for text in texts):
        return None
    merged = merge_conflicts_adjacent(*texts)
    return None if merged is None else merged.encode("utf-8")


def file_versions(path: str) -> dict | None:
    """The staged file and its versions in the bump, in main and in the merge base, with
    the automatic merge of the three; None while the file is unresolved or unstaged."""
    staged = git_bytes("show", f":0:{path}")
    if staged is None or git("diff", "--quiet", "--", path, check=False).returncode != 0:
        return None
    base_commit = git("merge-base", "HEAD", "MERGE_HEAD").stdout.strip()
    ours, theirs = git_bytes("show", f"HEAD:{path}"), git_bytes("show", f"MERGE_HEAD:{path}")
    base = git_bytes("show", f"{base_commit}:{path}")
    auto = auto_merge(base, ours, theirs) if None not in (base, ours, theirs) else None
    return {"staged": staged, "ours": ours, "theirs": theirs, "base": base, "auto": auto}


# ---------------------------------------------------------------- neighbouring lines


def lines_of(text: str) -> list[str]:
    """`text` split after each LF, as git splits lines; a CR stays part of its line, and no
    other character (form feed, U+2028, ...) ends a line."""
    lines = [line + "\n" for line in text.split("\n")]
    lines[-1] = lines[-1][:-1]
    return lines if lines[-1] else lines[:-1]


def edits(base: list[str], side: list[str]) -> list[tuple[int, int, list[str]]]:
    """The changes from `base` to `side` as (start, end, new lines) over base line ranges."""
    matcher = difflib.SequenceMatcher(None, base, side, autojunk=False)
    return [(i1, i2, side[j1:j2]) for tag, i1, i2, j1, j2 in matcher.get_opcodes() if tag != "equal"]


def disjoint_changes(base: bytes, ours: bytes, theirs: bytes, merged: bytes) -> bool:
    """Whether the two sides provably made different edits: no base line is changed by both,
    neither inserts at the same place as the other or inside the other's change, no line
    with a letter or digit was added by both, and applying both sides' edits to the base
    gives exactly `merged`. The last check catches a line alignment that differs from git's
    (repeated lines can make one shared deletion look like two). A shared edit always fails
    this; two edits on neighbouring lines pass."""
    try:
        b, o, t = (lines_of(data.decode("utf-8")) for data in (base, ours, theirs))
    except UnicodeDecodeError:
        return False
    mine, other = edits(b, o), edits(b, t)
    if not mine or not other:
        return False
    for s1, e1, _ in mine:
        for s2, e2, _ in other:
            if s1 < e2 and s2 < e1:  # both change some of the same lines
                return False
            if (s1 == e1 and s2 <= s1 <= e2) or (s2 == e2 and s1 <= s2 <= e1):  # an insertion there
                return False
    added = lambda changes: {line.strip() for _, _, new in changes for line in new if re.search(r"\w", line)}
    if added(mine) & added(other):
        return False
    rebuilt, position = [], 0
    for start, end, new in sorted(mine + other, key=lambda change: (change[0], change[1])):
        rebuilt += b[position:start] + new
        position = end
    return "".join(rebuilt + b[position:]).encode("utf-8") == merged


DOC_OPENERS = ("/--", "/-!")


def is_doc_comment(lines: list[str]) -> bool:
    """Exactly one whole Lean doc comment: it opens on the first line and closes on the last,
    with no other comment delimiter in between."""
    text = "".join(lines).strip()
    return (bool(lines) and text.startswith(DOC_OPENERS) and text.endswith("-/")
            and text.count("/-") == 1 and text.count("-/") == 1)


def is_code_line(lines: list[str]) -> bool:
    """A single non-blank line with no comment delimiter."""
    return len(lines) == 1 and bool(lines[0].strip()) and "/-" not in lines[0] and "-/" not in lines[0]


def merge_adjacent(base: str, ours: str, theirs: str) -> str | None:
    """Three-way merge of one conflict whose two sides only touch: one side rewrote a whole
    doc comment and the other edited the single declaration line next to it, which is how a
    docstring campaign on main meets a bump's `noncomputable`. Neither change can then
    contain any of the other. Every other conflict (overlapping changes, an insertion or
    deletion at the seam, any other pair of neighbouring changes) returns None, for a
    person."""
    b, o, t = (lines_of(text) for text in (base, ours, theirs))
    mine, other = edits(b, o), edits(b, t)
    for s1, e1, new1 in mine:
        for s2, e2, new2 in other:
            if s1 < e2 and s2 < e1:  # both change some of the same lines
                return None
            if s1 == e1 or s2 == e2:  # an insertion: refused at or inside the other change
                if (s1 == e1 and s2 <= s1 <= e2) or (s2 == e2 and s1 <= s2 <= e1):
                    return None
                continue
            if e1 != s2 and e2 != s1:  # apart
                continue
            old1, old2 = b[s1:e1], b[s2:e2]
            doc_then_code = is_doc_comment(old1) and is_doc_comment(new1) and is_code_line(old2) and is_code_line(new2)
            code_then_doc = is_doc_comment(old2) and is_doc_comment(new2) and is_code_line(old1) and is_code_line(new1)
            if not (doc_then_code or code_then_doc):
                return None
    merged, position = [], 0
    for start, end, new in sorted(mine + other, key=lambda change: (change[0], change[1])):
        merged += b[position:start] + new
        position = end
    return "".join(merged + b[position:])


def marker_size(*texts: str) -> int:
    """A conflict-marker width that no line of the inputs can be mistaken for."""
    longest = 0
    for text in texts:
        for char in "<|=>":
            for run in re.findall(r"(?m)^" + re.escape(char) + "+", text):
                longest = max(longest, len(run))
    return max(32, longest + 1)


def merge_conflicts_adjacent(base: str, ours: str, theirs: str) -> str | None:
    """Git's own merge of the file, with each conflict block that only joins changes to
    neighbouring lines merged by `merge_adjacent`; None if any block needs a person, or if the
    result cannot be read back unambiguously."""
    size = marker_size(base, ours, theirs)
    with tempfile.TemporaryDirectory() as tmp:
        names = []
        for name, text in (("ours", ours), ("base", base), ("theirs", theirs)):
            path = Path(tmp) / name
            path.write_bytes(text.encode("utf-8"))
            names.append(str(path))
        proc = subprocess.run(["git", "merge-file", "-p", "--diff3", f"--marker-size={size}",
                               "-L", "ours", "-L", "base", "-L", "theirs", *names], capture_output=True)
    if proc.returncode < 0 or proc.returncode > 127:
        raise Stop(f"git merge-file failed:\n{proc.stderr.decode('utf-8', 'replace').strip()}")
    output = proc.stdout.decode("utf-8")
    if proc.returncode == 0:
        return output
    starts, middle, separator, ends = ("<" * size + " ours", "|" * size + " base", "=" * size,
                                       ">" * size + " theirs")
    out, block, state, blocks = [], {"ours": [], "base": [], "theirs": []}, None, 0
    for line in lines_of(output):
        bare = line.rstrip("\r\n")
        if state is None and bare == starts:
            state = "ours"
        elif state == "ours" and bare == middle:
            state = "base"
        elif state == "base" and bare == separator:
            state = "theirs"
        elif state == "theirs" and bare == ends:
            merged = merge_adjacent(*("".join(block[k]) for k in ("base", "ours", "theirs")))
            if merged is None:
                return None
            out.append(merged)
            blocks += 1
            block, state = {"ours": [], "base": [], "theirs": []}, None
        elif state is None:
            out.append(line)
        else:
            block[state].append(line)
    if state is not None or blocks != proc.returncode:
        return None
    return "".join(out)


def stage_entries(path: str) -> dict[int, str]:
    """The unmerged index entries of `path`: stage number -> mode."""
    entries = {}
    for entry in git("ls-files", "-u", "-z", "--", path).stdout.split("\0"):
        if entry:
            meta = entry.split("\t", 1)[0].split()
            entries[int(meta[2])] = meta[0]
    return entries


def resolve_adjacent(paths: list[str]) -> list[str]:
    """Resolve and stage each conflicted file whose conflicts only join changes to
    neighbouring lines; return the files that still need a person. Only files still exactly
    as merge-main's `git merge` left them, regular, in UTF-8 and with all three versions
    ending in a newline, are tried."""
    left, edited = [], []
    for path in paths:
        if not untouched(path):
            edited.append(path)
            left.append(path)
            continue
        texts = None
        if stage_entries(path) == {1: "100644", 2: "100644", 3: "100644"}:
            blobs = [git_bytes("show", f":{stage}:{path}") for stage in (1, 2, 3)]
            try:
                texts = [blob.decode("utf-8") for blob in blobs]
            except (AttributeError, UnicodeDecodeError):
                texts = None
        if texts is None or any(text and not text.endswith("\n") for text in texts):
            left.append(path)
            continue
        merged = merge_conflicts_adjacent(*texts)
        if merged is None:
            left.append(path)
            continue
        (REPO / path).write_bytes(merged.encode("utf-8"))
        git("add", "--", path)
        print(f"{path}: merged changes to neighbouring lines")
    for path in edited:
        print(f"{path}: not as merge-main's `git merge` left it, so --adjacent leaves it to you")
    return left


# ---------------------------------------------------------------- merge


def merge_uses_shards(ours: str, theirs: str, *, in_progress: bool = False) -> bool:
    base = git("merge-base", ours, theirs).stdout.strip()
    manifests = [provenance_at(revision) for revision in (base, ours, theirs)]
    sharded = [
        manifest is not None and manifest["schema_version"] == fms.SHARDED_SCHEMA_VERSION
        for manifest in manifests
    ]
    if any(sharded) and not all(sharded):
        action = (
            "Resolve the open merge by hand" if in_progress
            else f"Start a manual merge with `git merge --no-ff --no-commit {theirs}`"
        )
        raise Stop(
            f"cannot automatically merge across the provenance sharding cutover. {action}; "
            "keep the sharded layout and carry over both sides' row changes. Stage the "
            "resolution, then run `python3 scripts/bump/bump_branch.py resolve-manifest "
            "--check-only` before committing."
        )
    return all(sharded)


def merge_provenance_file(path: str) -> tuple[str, dict[str, int], list[str]]:
    """Merge the conflicted monolithic manifest using the actual Git index stages."""
    entries = stage_entries(path)
    if set(entries) != {1, 2, 3} or any(mode not in ("100644", "100755") for mode in entries.values()):
        raise Stop(f"{path}: unsupported index stages; resolve and stage it by hand")
    manifests = []
    try:
        for stage in (1, 2, 3):
            text = show(f":{stage}:{path}")
            if text is None:
                raise ValueError(f"cannot read stage {stage}")
            manifests.append(fms.parse_manifest(Path(MANIFEST), text, {}))
        merged, counts, problems = merge_manifest_data(*manifests, versions=file_versions)
        return fms.dump_manifest(merged), counts, problems
    except (ValueError, KeyError, TypeError) as error:
        raise Stop(f"{path}: {error}; resolve and stage it by hand") from error


def ledger_files(revision: str) -> set[Path]:
    """The files of the sharded ledger directory at `revision`."""
    directory = fms.shard_directory(Path(MANIFEST)).as_posix()
    listing = git("ls-tree", "-r", "-z", "--name-only", revision, "--", directory).stdout
    return {Path(name) for name in listing.split("\0") if name}


def tracked_ledger() -> list[str]:
    """The ledger files in the index, unmerged ones included; never an untracked file."""
    directory = fms.shard_directory(Path(MANIFEST)).as_posix()
    return sorted({name for name in git("ls-files", "-z", "--", MANIFEST, directory).stdout.split("\0") if name})


def ledger_changed(a: str, b: str) -> bool:
    directory = fms.shard_directory(Path(MANIFEST)).as_posix()
    return git("diff", "--quiet", a, b, "--", MANIFEST, directory, check=False).returncode != 0


def merge_ledger() -> tuple[dict[str, str | None], dict[str, int], list[str], dict[str, dict]]:
    """Merge the whole sharded ledger row by row, keyed by path, whichever file holds each row.

    The merge base, the bump (HEAD) and main (MERGE_HEAD) are read from their commits, so a row
    that one side moved into its module file and the other side edited in its legacy shard is
    still one row. A merged row goes to its module file if either side keeps it there, so rows
    never move back to a legacy shard; otherwise it stays in its legacy shard. Returns
    the ledger files whose rows in the worktree differ from that layout (None: delete the file),
    the counts and the problems of `merge_manifest_data`, and the merged rows by path."""
    header = Path(MANIFEST)
    head, main = rev("HEAD"), merge_head()
    base = git("merge-base", head, main).stdout.strip()
    sides = []
    for revision in (base, head, main):
        manifest = provenance_at(revision)
        if manifest is None:
            raise Stop(f"no provenance ledger at {revision[:12]}; resolve the merge by hand")
        paths = {row["path"] for row in manifest["rows"]}
        sides.append((manifest, paths, fms.module_rows(header, manifest, ledger_files(revision))))
    merged, counts, problems = merge_manifest_data(*(side[0] for side in sides), versions=file_versions)
    # A module file is fixed by the row's path, so the two sides cannot disagree on it. A row that
    # neither side has (both removed it: a problem) keeps the base's file.
    (_, _, base_modules), (_, bump_paths, bump_modules), (_, main_paths, main_modules) = sides
    modules = bump_modules | main_modules | (base_modules - bump_paths - main_paths)
    try:
        documents = {path.as_posix(): text for path, text in fms.manifest_documents(header, merged, modules).items()}
        current = {path: (REPO / path).read_text(encoding="utf-8") for path in tracked_ledger()
                   if (REPO / path).is_file() and not (REPO / path).is_symlink()}
    except (OSError, ValueError) as error:
        raise Stop(f"cannot lay out the merged provenance: {error}") from error

    def parsed(text: str) -> object:
        try:
            return json.loads(text)
        except ValueError:
            return None  # conflict markers, say

    # A file is rewritten only if its rows change, never merely to reformat it.
    changes: dict[str, str | None] = {path: text for path, text in documents.items()
                                      if path not in current or parsed(current[path]) != json.loads(text)}
    changes.update({path: None for path in current if path not in documents})
    return changes, counts, problems, rows_by_path(merged)


def provenance_rows(manifest: dict | None, revision: str) -> dict[str, dict]:
    rows: dict[str, dict] = {}
    if manifest is None:
        return rows
    for row in manifest["rows"]:
        path = row.get("path") if isinstance(row, dict) else None
        if not isinstance(path, str) or not path:
            raise Stop(f"provenance at {revision} has an invalid row path")
        if path in rows:
            raise Stop(f"provenance at {revision} has duplicate row path {path}")
        rows[path] = row
    return rows


def inherited_row_problems(
    path: str, before: dict, row: dict, revision: str, *, same_pin: bool, bound_at_pin: bool,
) -> list[str]:
    if (before.get("disposition") in ("identical", "attributed")
            and not same_pin and not bound_at_pin):
        return [f"{path}: source is bound only at {revision[:12]}; sync it at the selected pin first"]
    if row == before:
        return []
    short = revision[:12]
    if before.get("disposition") == "retired":
        return [f"{path}: inherited retired row from {short} must be kept exactly"]
    if not same_pin:
        # A shared row already recorded at the selected pin is checked against that parent.
        # For a row known only at a different pin there is no new binding to validate.
        if bound_at_pin:
            return []
        return [f"{path}: keep the row from {short} unchanged across an upstream pin change"]
    problems = fms.row_transition_problems(path, before, row, short)
    if not problems and row.get("disposition") == "retired":
        previous = show(f"{revision}:{path}")
        if previous is None or row != fms.retired_row(before, path, previous):
            problems.append(f"{path}: retirement does not match the record and file at {short}")
    return problems


def check_parent_rows(tree: str, bump: str, main: str) -> None:
    merged = provenance_at(tree)
    parents = [(revision, provenance_at(revision)) for revision in (bump, main)]
    parent_rows = [(rev, provenance_rows(manifest, rev)) for rev, manifest in parents]
    staged_rows = provenance_rows(merged, tree)
    required = set().union(*(rows for _, rows in parent_rows))
    missing = required - staged_rows.keys()
    if missing:
        listed = "\n".join(f"  {path}" for path in sorted(missing))
        raise Stop(
            "the staged merge drops provenance rows from its parents; nothing was committed. "
            f"Restore the rows (use --retire for deleted files) and stage them:\n{listed}"
        )
    # The canonical checker compares with main. Protect against rollback when it is
    # the bump parent that already uses the sharded layout.
    sharded = fms.SHARDED_SCHEMA_VERSION
    if any(manifest is not None and manifest["schema_version"] == sharded
           for _, manifest in parents) and (merged is None or merged["schema_version"] != sharded):
        raise Stop("the staged merge must keep sharded provenance; nothing was committed")
    if merged is None:
        return
    pin = merged["upstream"]["commit"]
    pins = {rev: manifest["upstream"]["commit"] for rev, manifest in parents if manifest}
    if pins and pin not in pins.values():
        raise Stop("the staged merge introduces a new upstream pin; sync it separately")
    bound_paths = set().union(*(rows for rev, rows in parent_rows if pins.get(rev) == pin))
    problems = []
    for revision, rows in parent_rows:
        for path, before in sorted(rows.items()):
            problems.extend(inherited_row_problems(
                path, before, staged_rows[path], revision,
                same_pin=pins[revision] == pin, bound_at_pin=path in bound_paths,
            ))
    if problems:
        listed = "\n".join(f"  {problem}" for problem in problems)
        raise Stop(f"the staged merge changes inherited provenance; no commit was made:\n{listed}")


def two_files_advice() -> str:
    """How to finish a staged merge that keeps a row in two ledger files."""
    copies: dict[str, list[str]] = {}
    for path in tracked_ledger():
        try:
            rows = json.loads((REPO / path).read_text(encoding="utf-8")).get("rows") or []
        except (OSError, ValueError, AttributeError):
            continue
        for row in rows:
            if isinstance(row, dict) and isinstance(row.get("path"), str):
                copies.setdefault(row["path"], []).append(path)
    doubled = {path: files for path, files in sorted(copies.items()) if len(files) > 1}
    state = load_state()
    if "preimages" not in state:
        return ("The merge keeps a row in two files. This merge was not started by merge-main, so "
                "`resolve-manifest --regenerate` rewrites every ledger file that differs from the merged ledger, "
                "your edits included (each file is saved first): run it with --no-commit and review the result.")
    theirs = sorted({file for files in doubled.values() for file in files
                     if signature(file) not in known_signatures(state, file)})
    if theirs:
        listed = []
        for path, files in doubled.items():
            versions = {file: json.dumps(rows[path], sort_keys=True) for file, rows in
                        ((file, {row["path"]: row for row in json.loads((REPO / file).read_text(encoding="utf-8"))["rows"]
                                 if isinstance(row, dict)}) for file in files)}
            listed.append(f"  {path}: {', '.join(files)}")
            if len(set(versions.values())) > 1:  # keeping either copy would drop the other's change
                listed.append("    the copies differ; keep one row with both sides' changes:")
                listed += [f"    {file}: {row}" for file, row in versions.items()]
        listed_text = "\n".join(listed)
        return (f"The merge keeps a row in two files, and {', '.join(theirs)} was edited or created since the "
                "merge, so resolve-manifest leaves it alone: keep one copy of each row below, delete the other, "
                f"run `git add -A provenance/`, and run resolve-manifest again.\n{listed_text}")
    return ("The merge keeps a row in two files. Run `resolve-manifest --regenerate --no-commit`: it moves each "
            "such row to its module file, saves every file it replaces, and leaves files edited or created since "
            "the merge as they are; review the result, run `git add -A provenance/`, then run resolve-manifest.")


def check_candidate() -> None:
    """Check inherited records from both parents and run the canonical checker against main."""
    if unmerged_paths():
        raise Stop("the merge has unresolved conflicts; resolve and stage them first")
    if git("diff", "--quiet", check=False).returncode != 0:
        raise Stop("some tracked files differ from what is staged; `git add` or restore them first")
    bump, main = rev("HEAD"), merge_head()
    tree = git("write-tree").stdout.strip()
    try:
        check_parent_rows(tree, bump, main)
    except Stop as stop:
        if "recorded in two files" not in str(stop):
            raise
        raise Stop(f"{stop}\n{two_files_advice()}") from None
    candidate = git(
        "commit-tree", tree, "-p", bump, "-p", main, "-m", "candidate merge"
    ).stdout.strip()
    if git_bytes("cat-file", "-e", f"{candidate}:{CHECKER}") is None:
        raise Stop(f"{CHECKER} is missing from the merge; cannot check the manifest")
    scratch = Path(tempfile.mkdtemp(prefix="bump-branch-check-"))
    try:
        git("worktree", "add", "--detach", "--quiet", str(scratch / "tree"), candidate)
        check = subprocess.run(
            [sys.executable, str(scratch / "tree" / CHECKER), "--root", str(scratch / "tree"),
             "--base", main], cwd=scratch / "tree", capture_output=True, text=True,
        )
    finally:
        git("worktree", "remove", "--force", str(scratch / "tree"), check=False)
        shutil.rmtree(scratch, ignore_errors=True)
    if check.returncode != 0:
        raise Stop(f"the merge does not pass {CHECKER} against main; nothing was committed:\n"
                   f"{check.stdout.strip()}\n{check.stderr.strip()}".rstrip())
    print(check.stdout.strip().splitlines()[-1] if check.stdout.strip() else f"{CHECKER} passed")


def git_path(name: str) -> Path:
    path = Path(git("rev-parse", "--git-path", name).stdout.strip())
    return path if path.is_absolute() else REPO / path


def merge_attempt() -> str | None:
    """Which merge is open: git writes MERGE_HEAD anew for every merge, so its inode and
    time tell a retried merge of the same commit from the one before it."""
    try:
        info = git_path("MERGE_HEAD").stat()
    except OSError:
        return None
    return f"{merge_head()}-{info.st_ino}-{info.st_mtime_ns}"


def load_state() -> dict:
    try:
        state = json.loads(git_path("bump-branch-draft.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return state if isinstance(state, dict) and state.get("attempt") == merge_attempt() else {}


def save_state(state: dict) -> None:
    git_path("bump-branch-draft.json").write_text(json.dumps({**state, "attempt": merge_attempt()}),
                                                  encoding="utf-8")


def signature(path: str) -> str | None:
    """The file's bytes and git's view of its mode, or None for anything but a regular file."""
    target = REPO / path
    if target.is_symlink() or not target.is_file():
        return None
    executable = target.stat().st_mode & stat.S_IXUSR  # git's 100755 versus 100644
    return f"{fms.sha256(target.read_bytes())}:{'755' if executable else '644'}"


def record_preimages(sharded: bool = False) -> None:
    """Remember every conflicted file exactly as `git merge` left it, mode included: the tool
    replaces such a file only while it is still that, never once someone has changed it. In the
    sharded layout every ledger file counts, conflicted or not, since a row can move between files."""
    paths = unmerged_paths() + (tracked_ledger() if sharded else [])
    preimages = {path: signature(path) for path in paths}
    save_state({"preimages": {path: sig for path, sig in preimages.items() if sig}, "drafts": {}})


def known_signatures(state: dict, path: str) -> set:
    """What `path` was after `git merge` and after this tool last wrote it, as far as recorded: a
    file that was never recorded matches nothing, so a person's deletion counts as an edit."""
    return {record[path] for record in (state.get("preimages", {}), state.get("drafts", {})) if path in record}


def ledger_untouched() -> bool:
    """Whether every ledger file is still as merge-main's `git merge` left it or as this tool last
    wrote it: until a person changes one, the tool may merge the ledger again."""
    state = load_state()
    if "preimages" not in state:
        return False  # a merge started without merge-main
    directory = fms.shard_directory(Path(MANIFEST))
    ledger = set(tracked_ledger()) | {path for path in {**state["preimages"], **state.get("drafts", {})}
                                      if path == MANIFEST or Path(path).is_relative_to(directory)}
    return all(signature(path) in known_signatures(state, path) for path in ledger)


def untouched(path: str) -> bool:
    """Whether `path` is still exactly as merge-main's `git merge` left it."""
    recorded = load_state().get("preimages", {}).get(path)
    return bool(recorded) and signature(path) == recorded


def save_backup(data: bytes) -> Path:
    """Save `data` in a new file in the git directory, never over an earlier backup."""
    stem, attempt = f"bump-branch-manifest-{time.time_ns()}", 0
    while True:
        backup = git_path(f"{stem}-{attempt}.json" if attempt else f"{stem}.json")
        try:
            with open(backup, "xb") as out:
                out.write(data)
            return backup
        except FileExistsError:
            attempt += 1


def write_draft(path: str, merged: str | None, regenerate: bool, *, sharded: bool) -> bool:
    """Replace (or, for None, delete) only Git's original file or an unedited draft, unless asked."""
    target, state = REPO / path, load_state()
    if fms.symlinked_component(REPO, target) or (target.exists() and not target.is_file()):
        raise Stop(f"{path}: expected a regular file with no symlinked components")
    data = None if merged is None else merged.encode("utf-8")
    current = target.read_bytes() if target.exists() else None
    drafts = state.get("drafts", {})
    known = {state.get("preimages", {}).get(path), drafts.get(path)} - {None}
    sig = signature(path)
    saved = False
    # Keep the legacy shortcut of deleting the monolithic draft to start over.
    # In the sharded layout treat a missing file as a manual edit unless asked.
    if sig not in known and (current is not None or sharded):
        mode = sig.split(":")[1] if sig else None
        same = current == data and any(entry.split(":")[1] == mode for entry in known)
        if not same and not regenerate:
            print(f"{path} has changes this tool did not make: resolve and `git add` it, "
                  "then run resolve-manifest again, or use resolve-manifest --regenerate "
                  "to replace it (any existing file is saved first).")
            return False
        if not same and current is not None:
            saved = True
            print(f"{path}: the version it replaces is saved as {save_backup(current)}")
    if current != data and data is None:
        if not saved:  # a deleted file is always saved first
            print(f"{path}: deleted; it is saved as {save_backup(current)}")
        target.unlink()
    elif current != data:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    save_state({**state, "drafts": {**drafts, path: signature(path)}})
    return True


def clear_state() -> None:
    git_path("bump-branch-draft.json").unlink(missing_ok=True)


def resolve_manifest(
    commit: bool, adjacent: bool = False, regenerate: bool = False, *, check_only: bool = False
) -> int:
    main = merge_head()
    if not main:
        raise Stop("no merge in progress; run `merge-main`")
    if check_only:
        if adjacent or regenerate:
            raise Stop("--check-only cannot be combined with --adjacent or --regenerate")
        check_candidate()
        return 0
    sharded = merge_uses_shards("HEAD", main, in_progress=True)
    return finish_merge(commit, adjacent, regenerate, sharded=sharded)


def finish_merge(commit: bool, adjacent: bool, regenerate: bool, *, sharded: bool) -> int:
    unmerged = unmerged_paths()
    directory = fms.shard_directory(Path(MANIFEST))
    provenance = {path for path in unmerged if path == MANIFEST or (
        sharded and Path(path).is_relative_to(directory)
    )}
    others = [path for path in unmerged if path not in provenance]
    if adjacent and others:
        others = resolve_adjacent(others)
    if others:
        print("Resolve these, `git add` them, then run resolve-manifest again:")
        for path in others:
            print(f"  {path}")
        return 3
    manual = False
    head, main = rev("HEAD"), merge_head()
    base = git("merge-base", head, main).stdout.strip() if sharded else ""
    # A clean merge can still leave a row in two files (one side added it to a legacy shard, the
    # other to its module file): merge the ledger whenever both sides changed it, until a person
    # changes a ledger file, and always while one is conflicted.
    if sharded and (provenance or (ledger_changed(base, head) and ledger_changed(base, main)
                                   and (regenerate or ledger_untouched()))):
        changes, counts, problems, merged_rows = merge_ledger()
        state = load_state()
        written, unverified, blocked, unreadable = [], [], set(), []
        # A ledger file someone created or edited since merge-main's merge is theirs: it stays as it is,
        # and a row it holds that differs from the merged row is theirs to finish, with its other file.
        theirs = {}
        for path in changes:
            now, known = signature(path), known_signatures(state, path)
            if path not in provenance and known and now not in known:
                theirs[path] = "edited"
            elif path not in provenance and not known and now is not None and "preimages" in state:
                theirs[path] = "created"
        for path, how in sorted(theirs.items()):
            manual = manual or how == "created"
            print(f"{path}: {how} since the merge, so it is left as it is" + (
                "; once the ledger is resolved, stage all of it with `git add -A provenance/`" if how == "created" else ""))
            if not (REPO / path).exists():
                continue  # deleted by hand: check_candidate reports the rows it held
            try:
                kept = {row["path"]: row for row in json.loads((REPO / path).read_text(encoding="utf-8"))["rows"]}
                homes = {row_path: {home(Path(MANIFEST), row_path).as_posix() for home in (fms.shard_path, fms.module_path)}
                         for row_path in kept}
            except (OSError, ValueError, KeyError, TypeError):
                unreadable.append(path)
                continue
            for row_path, row in sorted(kept.items()):
                if merged_rows.get(row_path) != row:
                    if (homes[row_path] - {path}) & set(changes):
                        problems.append(f"{row_path}: {path}, {how} since the merge, holds another row than the "
                                        "merged one; finish the row by hand")
                    else:  # no other file would change: a deliberate edit
                        problems.append(f"{row_path}: {path}, {how} since the merge, holds another row than the "
                                        "merged one, and that edit is kept as it is: it needs only "
                                        "`git add -A provenance/` and a plain resolve-manifest")
                    blocked |= homes[row_path] - {path}
        if unreadable:  # its rows are unknown, so no other file can be laid out safely
            manual = True
            print(f"{', '.join(unreadable)} changed since the merge and cannot be read as a ledger file: fix it, "
                  "then run resolve-manifest again. No ledger file was written.")
        for path, merged in sorted(changes.items()) if not unreadable else []:
            if path in theirs or path in blocked:
                continue
            if path not in provenance and not known_signatures(state, path) and signature(path) is not None \
                    and not regenerate:
                unverified.append(path)
                continue
            if write_draft(path, merged, regenerate or path not in provenance, sharded=sharded):
                written.append(path)
            else:
                manual = True
        if unverified:
            manual = True
            print(f"{len(unverified)} ledger file(s) that git merged cleanly need changes, but this merge "
                  "was not started by merge-main: run resolve-manifest --regenerate to rewrite them "
                  "(each is saved first).")
        if problems:
            manual = True
            print("provenance entries to finish by hand:")
            for problem in problems:
                print(f"  {problem}")
        elif not manual:
            if written or provenance:
                git("add", "--", *sorted(set(written) | provenance))
            print(f"provenance: {counts['main']} row(s) from main, {counts['bump']} from the bump, "
                  f"{counts['both']} changed on both sides re-recorded; {len(written)} file(s) written")
    elif not sharded:
        for path in sorted(provenance):
            merged, counts, problems = merge_provenance_file(path)
            if not write_draft(path, merged, regenerate, sharded=sharded):
                manual = True
                continue
            if problems:
                manual = True
                print(f"{path}: provenance entries to finish by hand:")
                for problem in problems:
                    print(f"  {problem}")
                continue
            git("add", "--", path)
            print(f"{path}: {counts['main']} row(s) from main, {counts['bump']} from the bump, "
                  f"{counts['both']} changed on both sides re-recorded")
    if manual:
        print(f"Once all provenance files parse, you can use {CHECKER} --record-divergence "
              "or --retire. Stage the resolved files and run resolve-manifest again.")
        return 3
    check_candidate()
    if commit:
        git("commit", "--no-edit")
        print(f"committed {rev('HEAD')[:12]}")
        clear_state()
    return 0


def merge_main(main_ref: str, commit: bool, adjacent: bool = False) -> int:
    main = rev(main_ref)
    if not main:
        raise Stop(f"{main_ref} is not a commit; run `git fetch origin main` first")
    if merge_head():
        raise Stop("a merge is already in progress; finish it with `resolve-manifest` or abort it")
    if git("status", "--porcelain", "--untracked-files=no").stdout.strip():
        raise Stop("the working tree has uncommitted changes; commit or stash them first")
    if git("merge-base", "--is-ancestor", main, "HEAD", check=False).returncode == 0:
        print(f"{main_ref} is already merged")
        return 0
    sharded = merge_uses_shards("HEAD", main)
    directory = fms.shard_directory(Path(MANIFEST)).as_posix()
    if sharded and git("status", "--porcelain", "--untracked-files=all", "--", directory).stdout.strip():
        raise Stop(f"{directory} has untracked files, such as a new module file: commit or remove them first")
    proc = git("merge", "--no-ff", "--no-commit", main, check=False)
    if proc.returncode != 0 and not unmerged_paths():
        raise Stop(f"git merge failed:\n{proc.stdout.strip()}\n{proc.stderr.strip()}")
    record_preimages(sharded)
    return finish_merge(commit, adjacent, regenerate=False, sharded=sharded)


# ---------------------------------------------------------------- breakage


def failing_modules(log: str) -> list[str]:
    modules = dict.fromkeys(FAILED_JOB.findall(log))
    for path in ERROR_FILE.findall(log):
        modules.setdefault(path[:-len(".lean")].replace("/", "."), None)
    return list(modules)


def default_range(main_ref: str) -> str:
    """The main commits the latest merge of main into this branch brought in (or is bringing
    in, during a merge). Only the branch's own merges count, not main's history."""
    pending = merge_head()
    if pending:
        return f"{git('merge-base', 'HEAD', pending).stdout.strip()}..{pending}"
    main = rev(main_ref)
    if not main:
        raise Stop(f"{main_ref} is not a commit; run `git fetch origin main` first")
    log = git("log", "--first-parent", "--merges", "--format=%H %P", f"{main}..HEAD").stdout
    for line in log.splitlines():
        parents = line.split()[1:]
        if len(parents) >= 2 and git("merge-base", "--is-ancestor", parents[1], main, check=False).returncode == 0:
            return f"{git('merge-base', parents[0], parents[1]).stdout.strip()}..{parents[1]}"
    raise Stop("this branch has no merge of main yet; pass --since")


def breakage(log_path: Path, main_ref: str, since: str | None) -> int:
    modules = failing_modules(log_path.read_text(encoding="utf-8", errors="replace"))
    if not modules:
        print("no failing module found in the log")
        return 0
    if since:
        main = rev(main_ref)
        if not main:
            raise Stop(f"{main_ref} is not a commit; run `git fetch origin main` first")
        span = f"{since}..{main}"
    else:
        span = default_range(main_ref)
    start, end = span.split("..")
    print(f"candidate pull requests: main commits {start[:12]}..{end[:12]} that changed each failing module")
    for module in modules:
        path = module.replace(".", "/") + ".lean"
        print(module)
        if not (REPO / path).is_file() and git_bytes("cat-file", "-e", f"{end}:{path}") is None:
            print("  not a file of this repository (an upstream module, or a missing import)")
            continue
        lines = git("log", "--first-parent", "--format=%h %s", span, "--", path).stdout.splitlines()
        if not lines:
            print("  not changed on main in that range: a dependency changed, or the bump itself breaks it")
        for line in lines:
            print(f"  {line}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p_status = sub.add_parser("status", help="how far the bump branch is behind main")
    p_status.add_argument("--main", default="origin/main")
    p_status.add_argument("--json", action="store_true")
    for name, help_text in (("merge-main", "merge main and resolve the manifest"),
                            ("resolve-manifest", "finish a merge that merge-main left open")):
        p = sub.add_parser(name, help=help_text)
        if name == "merge-main":
            p.add_argument("--main", default="origin/main")
        p.add_argument("--no-commit", action="store_true")
        p.add_argument("--adjacent", action="store_true",
                       help="also merge a conflict where one side rewrote a whole doc comment and the other "
                            "changed the one line next to it")
        if name == "resolve-manifest":
            p.add_argument("--check-only", action="store_true",
                           help="validate the staged merge without resolving or committing it")
            p.add_argument("--regenerate", action="store_true",
                           help="replace unresolved provenance files this tool did not write "
                                "(existing files are saved first)")
    p_break = sub.add_parser("breakage", help="name the main pull requests behind failing modules")
    p_break.add_argument("log", type=Path)
    p_break.add_argument("--main", default="origin/main")
    p_break.add_argument("--since")
    args = parser.parse_args(argv)
    global REPO
    try:
        REPO = Path(git("rev-parse", "--show-toplevel").stdout.strip())
        if args.command == "status":
            report = status(args.main)
            print(json.dumps(report, indent=2)) if args.json else print_status(report)
            return 0
        if args.command == "merge-main":
            return merge_main(args.main, commit=not args.no_commit, adjacent=args.adjacent)
        if args.command == "resolve-manifest":
            return resolve_manifest(
                commit=not args.no_commit, adjacent=args.adjacent,
                regenerate=args.regenerate, check_only=args.check_only,
            )
        return breakage(args.log, args.main, args.since)
    except Stop as stop:
        print(f"bump_branch: {stop}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
