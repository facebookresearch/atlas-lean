#!/usr/bin/env python3
"""Keep a Lean/Mathlib bump branch close to main. See docs/BUMPS.md.

    scripts/bump/bump_branch.py status [--main REF] [--json]
        How far the checked-out bump branch is behind main, whether merging main now
        conflicts and where, and how much of the tree the bump touches.

    scripts/bump/bump_branch.py merge-main [--main REF] [--no-commit] [--adjacent]
        Merge main into the checked-out bump branch with a merge commit (never a rebase,
        so the bump commit stays exactly what pinned_bump.py produced), resolve
        provenance/formal-math-sync.json row by row, and commit. With --adjacent, a
        conflicted file whose two sides changed different lines that merely touch (main
        restated a docstring right above a declaration the bump changed) is merged too.
        Other conflicts are left for you: resolve them, `git add` them, then run
        `resolve-manifest`. Build before pushing either way.

    scripts/bump/bump_branch.py resolve-manifest [--no-commit] [--adjacent]
        Finish a merge that `merge-main` left open: resolve the manifest once every other
        conflicted file is resolved and staged, then commit.

    scripts/bump/bump_branch.py breakage LOG [--main REF] [--since REV]
        Read a failed `lake build` log and list each failing module with the main pull
        requests that changed it since REV (default: the main commits that the latest
        merge of main brought in), so the fix can name them.

REF defaults to origin/main; fetch it first. The manifest rule: a row only one side
changed takes that side's row. A row both sides changed starts from main's row, takes the
SHA-256 of the merged file, and appends the bump's rationale, what the bump added to the
base rationale, to main's; this needs both rows `diverged` with the same upstream fields,
and the merged file resolved and staged. Anything else stops with the rows to resolve by
hand (`scripts/check_formal_math_sync.py --record-divergence`).
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_formal_math_sync as fms  # noqa: E402  (one manifest format and hash for every writer)

MANIFEST = fms.MANIFEST
PR_NUMBER = re.compile(r"(?:Merge pull request #(\d+)|\(#(\d+)\)\s*$)")
# `lake build` marks a failed job `✖ [12/345] Building Some.Module (8.0s)`.
FAILED_JOB = re.compile(r"✖ \[\d+/\d+\] (?:Building|Built|Compiling|Running) ([A-Za-z0-9_.'«»]+)")
ERROR_FILE = re.compile(r"^error: (?:\./)*([A-Za-z0-9_/'.-]+\.lean):\d+:\d+:", re.M)


class Stop(Exception):
    """A condition the user must handle; the message says how."""


# The checkout the command works on: the one the command runs in.
REPO = Path.cwd()


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess:
    proc = subprocess.run(["git", *args], cwd=REPO, capture_output=True, text=True)
    if check and proc.returncode != 0:
        raise Stop(f"git {' '.join(args)} failed:\n{proc.stderr.strip()}")
    return proc


def rev(ref: str) -> str:
    return git("rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}").stdout.strip()


def pr_numbers(subjects: list[str]) -> list[int]:
    numbers = []
    for subject in subjects:
        match = PR_NUMBER.search(subject)
        if match:
            numbers.append(int(match.group(1) or match.group(2)))
    return numbers


def manifest_rows(text: str) -> dict[str, dict]:
    return {row["path"]: row for row in json.loads(text)["rows"]}


def show(spec: str) -> str | None:
    proc = git("show", spec, check=False)
    return proc.stdout if proc.returncode == 0 else None


# ---------------------------------------------------------------- status


def status(main_ref: str) -> dict:
    head, main = rev("HEAD"), rev(main_ref)
    if not main:
        raise Stop(f"{main_ref} is not a commit; run `git fetch origin main` first")
    base = git("merge-base", head, main).stdout.strip()
    subjects = git("log", "--first-parent", "--format=%s", f"{base}..{main}").stdout.splitlines()
    tree = git("merge-tree", "--write-tree", "--name-only", "--no-messages", head, main, check=False)
    if tree.returncode not in (0, 1):
        raise Stop(f"git merge-tree failed:\n{tree.stderr.strip()}")
    conflicts = tree.stdout.splitlines()[1:] if tree.returncode == 1 else []
    changed = git("diff", "--name-only", "--no-renames", base, head).stdout.splitlines()
    rows_changed = 0
    base_text, head_text = show(f"{base}:{MANIFEST}"), show(f"{head}:{MANIFEST}")
    if base_text and head_text:
        before, after = manifest_rows(base_text), manifest_rows(head_text)
        rows_changed = sum(1 for path, row in after.items() if before.get(path) != row)
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


def bump_rationale(base: dict | None, ours: dict) -> str:
    """What the bump's row says beyond the base row's rationale: all of it when the bump
    rewrote the rationale, the appended sentences when it extended it."""
    mine = ours.get("rationale", "").strip()
    theirs = (base or {}).get("rationale", "").strip()
    if theirs and mine.startswith(theirs):
        mine = mine[len(theirs):]
    return mine.lstrip(" .;,").strip()


def join_rationale(main_rationale: str, addition: str) -> str:
    """Main's rationale, then the bump's addition as a further sentence."""
    main_rationale = main_rationale.strip()
    if not addition or addition in main_rationale:
        return main_rationale
    if not main_rationale:
        return addition
    if not main_rationale.endswith((".", "!", "?")):
        main_rationale += "."
    if addition.startswith("Also"):
        return f"{main_rationale} {addition}"
    return f"{main_rationale} Also: {addition}"


def merge_field(name: str, base, ours, theirs):
    if ours == theirs or theirs == base:
        return ours
    if ours == base:
        return theirs
    raise Stop(f"{MANIFEST}: both sides changed the top-level field {name!r}; resolve it by hand")


def merge_manifest(base_text: str, ours_text: str, theirs_text: str, read_file) -> tuple[str, dict]:
    """Row-level three-way merge of the manifest; `read_file(path)` returns the merged file's bytes,
    or None when that file is still unresolved."""
    base, ours, theirs = (json.loads(t) for t in (base_text, ours_text, theirs_text))
    merged = {}
    for key in list(theirs) + [k for k in ours if k not in theirs]:
        if key != "rows":
            merged[key] = merge_field(key, base.get(key), ours.get(key), theirs.get(key))
    rows_b = {row["path"]: row for row in base["rows"]}
    rows_o = {row["path"]: row for row in ours["rows"]}
    rows_t = {row["path"]: row for row in theirs["rows"]}
    counts = {"main": 0, "bump": 0, "both": 0}
    problems, rows = [], {}
    for path in sorted(set(rows_b) | set(rows_o) | set(rows_t)):
        b, o, t = rows_b.get(path), rows_o.get(path), rows_t.get(path)
        if o == t:
            if o is not None:
                rows[path] = o
            continue
        if o == b:
            counts["main"] += 1
            if t is not None:
                rows[path] = t
            continue
        if t == b:
            counts["bump"] += 1
            if o is not None:
                rows[path] = o
            continue
        why = None
        if o is None or t is None:
            why = "one side removed the row"
        elif o.get("disposition") != "diverged" or t.get("disposition") != "diverged":
            why = f"dispositions {o.get('disposition')} (bump) and {t.get('disposition')} (main)"
        elif any(o.get(k) != t.get(k) for k in ("upstream_sha256", "upstream_commit")):
            why = "the two rows record different upstream versions"
        if why is None:
            data = read_file(path)
            if data is None:
                why = "the file is not resolved and staged yet"
        if why is None:
            rationale = join_rationale(t.get("rationale", ""), bump_rationale(b, o))
            row = dict(t)
            row["published_sha256"] = fms.sha256(data)
            row["rationale"] = rationale
            if row["published_sha256"] != t.get("published_sha256") and rationale == t.get("rationale", "").strip():
                why = "main's rationale already says what the bump's rationale adds; write one for the bump's change"
            else:
                rows[path] = row
                counts["both"] += 1
                continue
        problems.append(f"{path}: {why}")
    if problems:
        raise Stop("rows to resolve by hand (scripts/check_formal_math_sync.py --record-divergence or --retire):\n  "
                   + "\n  ".join(problems))
    merged["rows"] = [rows[path] for path in sorted(rows)]
    return fms.dump_manifest(merged), counts


def edits(base: list[str], side: list[str]) -> list[tuple[int, int, list[str]]]:
    """The changes from `base` to `side` as (start, end, new lines) over base line ranges."""
    matcher = difflib.SequenceMatcher(None, base, side, autojunk=False)
    return [(i1, i2, side[j1:j2]) for tag, i1, i2, j1, j2 in matcher.get_opcodes() if tag != "equal"]


def merge_adjacent(base: str, ours: str, theirs: str) -> str | None:
    """Three-way merge that also accepts changes to neighbouring lines: main restated a
    docstring right above a declaration the bump changed, for instance. None, for a
    person to resolve, when the sides change the same base lines, insert at the same
    place or inside the other's change, or when one side's change next to the other's is
    a pure deletion (what was inserted beside a deleted line may have belonged to it)."""
    b, o, t = (text.splitlines(keepends=True) for text in (base, ours, theirs))
    mine, other = edits(b, o), edits(b, t)
    for s1, e1, new1 in mine:
        for s2, e2, new2 in other:
            if s1 < e2 and s2 < e1:  # both change some of the same lines
                return None
            touching = e1 == s2 or e2 == s1 or (s1 == e1 and s2 <= s1 <= e2) or (s2 == e2 and s1 <= s2 <= e1)
            if not touching:
                continue
            if s1 == e1 == s2 == e2 or (s1 == e1 and s2 < s1 < e2) or (s2 == e2 and s1 < s2 < e1):
                return None
            if not new1 or not new2:
                return None
    merged, position = [], 0
    for start, end, new in sorted(mine + other, key=lambda change: (change[0], change[1])):
        merged += b[position:start] + new
        position = end
    return "".join(merged + b[position:])


MARKER = 31  # conflict-marker width: longer than any run of `<`, `=` or `>` in a Lean source


def merge_conflicts_adjacent(base: str, ours: str, theirs: str) -> str | None:
    """Git's own merge of the file, with each conflict block that only joins changes to
    neighbouring lines merged by `merge_adjacent`; None if any block needs a person."""
    with tempfile.TemporaryDirectory() as tmp:
        names = []
        for name, text in (("ours", ours), ("base", base), ("theirs", theirs)):
            path = Path(tmp) / name
            path.write_text(text, encoding="utf-8")
            names.append(str(path))
        proc = subprocess.run(["git", "merge-file", "-p", "--diff3", f"--marker-size={MARKER}",
                               "-L", "ours", "-L", "base", "-L", "theirs", *names],
                              capture_output=True, text=True)
    if proc.returncode < 0 or proc.returncode > 127:
        raise Stop(f"git merge-file failed:\n{proc.stderr.strip()}")
    if proc.returncode == 0:
        return proc.stdout
    starts, middle, separator, ends = ("<" * MARKER + " ours", "|" * MARKER + " base", "=" * MARKER,
                                       ">" * MARKER + " theirs")
    out, block, state = [], {"ours": [], "base": [], "theirs": []}, None
    for line in proc.stdout.splitlines(keepends=True):
        bare = line.rstrip("\n")
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
            block, state = {"ours": [], "base": [], "theirs": []}, None
        elif state is None:
            out.append(line)
        else:
            block[state].append(line)
    return None if state is not None else "".join(out)


def resolve_adjacent(paths: list[str]) -> list[str]:
    """Resolve and stage each conflicted file whose conflicts only join changes to
    neighbouring lines; return the files that still need a person."""
    left = []
    for path in paths:
        texts = [show(f":{stage}:{path}") for stage in (1, 2, 3)]
        merged = None if any(text is None for text in texts) else merge_conflicts_adjacent(*texts)
        if merged is None:
            left.append(path)
            continue
        (REPO / path).write_text(merged, encoding="utf-8")
        git("add", "--", path)
        print(f"{path}: merged changes to neighbouring lines")
    return left


def unmerged_paths() -> list[str]:
    return git("diff", "--name-only", "--diff-filter=U").stdout.splitlines()


def staged_bytes(path: str) -> bytes | None:
    """The file as staged at stage 0 (resolved), or None while it is unmerged."""
    proc = subprocess.run(["git", "show", f":0:{path}"], cwd=REPO, capture_output=True)
    return proc.stdout if proc.returncode == 0 else None


def resolve_manifest(commit: bool, adjacent: bool = False) -> int:
    if not git("rev-parse", "-q", "--verify", "MERGE_HEAD", check=False).stdout.strip():
        raise Stop("no merge in progress; run `merge-main`")
    unmerged = unmerged_paths()
    others = [path for path in unmerged if path != MANIFEST]
    if adjacent and others:
        others = resolve_adjacent(others)
    if MANIFEST in unmerged:
        if others:
            print("Resolve these first, `git add` them, then run resolve-manifest again:")
            for path in others:
                print(f"  {path}")
            return 3
        texts = [show(f":{stage}:{MANIFEST}") for stage in (1, 2, 3)]
        if any(text is None for text in texts):
            raise Stop(f"{MANIFEST} has no common base version; resolve it by hand")
        merged, counts = merge_manifest(*texts, read_file=staged_bytes)
        (REPO / MANIFEST).write_text(merged, encoding="utf-8")
        git("add", "--", MANIFEST)
        print(f"{MANIFEST}: {counts['main']} row(s) from main, {counts['bump']} from the bump, "
              f"{counts['both']} changed on both sides re-recorded")
    elif others:
        print("Resolve these, `git add` them, then commit:")
        for path in others:
            print(f"  {path}")
        return 3
    checker = REPO / "scripts" / "check_formal_math_sync.py"
    if checker.is_file():
        check = subprocess.run([sys.executable, str(checker)], cwd=REPO)
        if check.returncode != 0:
            print("The merged manifest does not check; fix it before committing.", file=sys.stderr)
            return 1
    if commit:
        git("commit", "--no-edit")
        print(f"committed {rev('HEAD')[:12]}")
    return 0


def merge_main(main_ref: str, commit: bool, adjacent: bool = False) -> int:
    main = rev(main_ref)
    if not main:
        raise Stop(f"{main_ref} is not a commit; run `git fetch origin main` first")
    if git("rev-parse", "-q", "--verify", "MERGE_HEAD", check=False).stdout.strip():
        raise Stop("a merge is already in progress; finish it with `resolve-manifest` or abort it")
    if git("status", "--porcelain", "--untracked-files=no").stdout.strip():
        raise Stop("the working tree has uncommitted changes; commit or stash them first")
    if git("merge-base", "--is-ancestor", main, "HEAD", check=False).returncode == 0:
        print(f"{main_ref} is already merged")
        return 0
    proc = git("merge", "--no-ff", "--no-commit", main, check=False)
    if proc.returncode != 0 and not unmerged_paths():
        raise Stop(f"git merge failed:\n{proc.stdout.strip()}\n{proc.stderr.strip()}")
    return resolve_manifest(commit, adjacent)


# ---------------------------------------------------------------- breakage


def failing_modules(log: str) -> list[str]:
    modules = dict.fromkeys(FAILED_JOB.findall(log))
    for path in ERROR_FILE.findall(log):
        modules.setdefault(path[:-len(".lean")].replace("/", "."), None)
    return list(modules)


def default_range(main_ref: str) -> str:
    """The main commits the latest merge of main brought in (or is bringing in)."""
    merge_head = git("rev-parse", "-q", "--verify", "MERGE_HEAD", check=False).stdout.strip()
    if merge_head:
        return f"{git('merge-base', 'HEAD', merge_head).stdout.strip()}..{merge_head}"
    main = rev(main_ref)
    for line in git("log", "--first-parent", "--merges", "--format=%H %P", "HEAD").stdout.splitlines():
        commit, first, second = line.split()[:3]
        if git("merge-base", "--is-ancestor", second, main, check=False).returncode == 0:
            return f"{git('merge-base', first, second).stdout.strip()}..{second}"
    raise Stop("the branch has no merge of main yet; pass --since")


def breakage(log_path: Path, main_ref: str, since: str | None) -> int:
    modules = failing_modules(log_path.read_text(encoding="utf-8", errors="replace"))
    if not modules:
        print("no failing module found in the log")
        return 0
    span = f"{since}..{rev(main_ref)}" if since else default_range(main_ref)
    print(f"main commits in {span[:12]}..{span.split('..')[1][:12]}")
    for module in modules:
        path = module.replace(".", "/") + ".lean"
        lines = git("log", "--first-parent", "--format=%h %s", span, "--", path).stdout.splitlines()
        print(f"{module}")
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
    p_merge = sub.add_parser("merge-main", help="merge main and resolve the manifest")
    p_merge.add_argument("--main", default="origin/main")
    p_merge.add_argument("--no-commit", action="store_true")
    p_merge.add_argument("--adjacent", action="store_true",
                         help="also merge conflicts where the two sides changed disjoint neighbouring lines")
    p_resolve = sub.add_parser("resolve-manifest", help="finish a merge that merge-main left open")
    p_resolve.add_argument("--no-commit", action="store_true")
    p_resolve.add_argument("--adjacent", action="store_true",
                           help="also merge conflicts where the two sides changed disjoint neighbouring lines")
    p_break = sub.add_parser("breakage", help="name the main pull requests behind failing modules")
    p_break.add_argument("log", type=Path)
    p_break.add_argument("--main", default="origin/main")
    p_break.add_argument("--since")
    args = parser.parse_args(argv)
    global REPO
    try:
        top = git("rev-parse", "--show-toplevel").stdout.strip()
        REPO = Path(top)
        if args.command == "status":
            report = status(args.main)
            print(json.dumps(report, indent=2)) if args.json else print_status(report)
            return 0
        if args.command == "merge-main":
            return merge_main(args.main, commit=not args.no_commit, adjacent=args.adjacent)
        if args.command == "resolve-manifest":
            return resolve_manifest(commit=not args.no_commit, adjacent=args.adjacent)
        return breakage(args.log, args.main, args.since)
    except Stop as stop:
        print(f"bump_branch: {stop}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
