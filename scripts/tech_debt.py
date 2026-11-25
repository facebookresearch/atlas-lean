#!/usr/bin/env python3
"""Count Atlas technical debt: source markers and compiler warnings.

    python3 scripts/tech_debt.py [--build-log LOG] [--base OLD.json] [--json OUT] [--markdown OUT]

Source counters are `git grep` counts over the tracked Lean files of the library roots,
modelled on Mathlib's technical-debt counters. A build log (the output of `lake build`,
for example CI's build job log, where Lake replays the warnings of cached modules too)
adds the compiler warnings, grouped by the linter that raised them and by library.
With `--base`, each count is compared with an earlier `--json` report.

The counts are a trend, not a verdict: a line can match a pattern inside a comment, and
the warning counts cover the modules the log's build replayed or rebuilt. The script
never invokes Lean and always exits 0 unless its inputs are unreadable.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

LIBRARIES = ("MathlibExt", "CSLibExt", "PhyslibExt", "Domains", "WantedExt")
TESTS = ("MathlibExtTest", "CSLibExtTest", "PhyslibExtTest", "DomainsTest")
LONG_FILE_LINES = 1500

# (name, extended regex, roots[, excluded regex]); each counts the matching lines of tracked
# `.lean` files, leaving out lines that also match the excluded regex.
SOURCE_COUNTERS = (
    ("`erw` rewrites", r"erw \[", LIBRARIES),
    ("`maxHeartbeats` raises", r"^ *set_option (synthInstance\.)?maxHeartbeats [0-9]+", LIBRARIES),
    ("linters disabled with `set_option ... false`", r"set_option linter\.[A-Za-z.]+ false", LIBRARIES),
    ("`nolint` attributes", r"nolint ", LIBRARIES),
    ("`set_option backward.*`", r"set_option backward\.", LIBRARIES),
    ("top-level `open Classical`", r"^open (scoped )?Classical( |$)", LIBRARIES, r" in *$"),
    ("`theorem_wanted` and `def_wanted`", r"^(theorem|def)_wanted ", ("WantedExt",)),
    ("`@[deprecated]` declarations", r"@\[deprecated", LIBRARIES),
    ("`TODO` and `FIXME` comments", r"(TODO|FIXME)", LIBRARIES),
    ("`#adaptation_note`", r"#adaptation_note", LIBRARIES),
    ("`native_decide` in tests", r"native_decide", TESTS),
)

WARNING = re.compile(r"^(?:\S+Z )?warning: (?P<path>[^:\s]+\.lean):(?:\d+:\d+:)? (?P<message>.*)$")
NOTE = re.compile(r"This linter can be disabled with `set_option (?P<option>[A-Za-z0-9_.]+) false`")
TIMESTAMP = re.compile(r"^\S+Z ")
ANSI = re.compile(r"\x1b\[[0-9;]*m")


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(root), *args], capture_output=True,
                          encoding="utf-8", check=True).stdout


def grep_count(root: Path, regex: str, roots: tuple[str, ...], excluded: str | None = None) -> int:
    pathspecs = [f"{r}/*.lean" for r in roots]
    patterns = ["-e", regex] + (["--and", "--not", "-e", excluded] if excluded else [])
    out = subprocess.run(["git", "-C", str(root), "grep", "-c", "-E", *patterns, "--", *pathspecs],
                         capture_output=True, encoding="utf-8", check=False)
    if out.returncode not in (0, 1):
        raise RuntimeError(out.stderr.strip())
    return sum(int(line.rsplit(":", 1)[1]) for line in out.stdout.splitlines())


def long_files(root: Path) -> int:
    files = git(root, "ls-files", "--", *(f"{r}/*.lean" for r in LIBRARIES)).split()
    count = 0
    for name in files:
        with open(root / name, "rb") as handle:
            if sum(1 for _ in handle) > LONG_FILE_LINES:
                count += 1
    return count


def manifest_pending(root: Path) -> int:
    # Schema 1 keeps the rows in the manifest; schema 2 shards them under formal-math-sync.d/.
    provenance = root / "provenance"
    shards = [provenance / "formal-math-sync.json", *sorted((provenance / "formal-math-sync.d").glob("**/*.json"))]
    rows = [row for shard in shards if shard.exists()
            for row in json.loads(shard.read_text(encoding="utf-8")).get("rows", [])]
    return sum(1 for row in rows if row.get("disposition") == "diverged" and row.get("backport") == "pending")


def source_counts(root: Path) -> dict[str, int]:
    counts = {counter[0]: grep_count(root, *counter[1:]) for counter in SOURCE_COUNTERS}
    counts[f"library files over {LONG_FILE_LINES} lines"] = long_files(root)
    counts["Formal-Math divergences with a pending backport"] = manifest_pending(root)
    return counts


def unlinted_kind(message: str) -> str:
    """A category for a warning that no linter raised."""
    if "has been deprecated" in message:
        return "deprecated module imported" if message.startswith("'") else "deprecated declaration used"
    words = re.sub(r"`[^`]*`", "…", message).split(":")[0].split()
    return "other: " + " ".join(words[:4])


def warning_counts(lines) -> tuple[Counter, Counter]:
    """Count the warnings of a build log by linter option and by top-level directory.

    A warning repeated verbatim counts once (CI's build log repeats some). A warning without a "can be disabled" note counts as a deprecation or under the first
    words of its message, so no warning goes uncounted.
    """
    by_linter: Counter = Counter()
    by_library: Counter = Counter()
    pending = None  # (path, message) of the warning whose note may follow
    seen = set()  # a log can repeat a warning verbatim

    def flush():
        if pending is not None:
            by_linter[pending[1]] += 1

    for raw in lines:
        line = TIMESTAMP.sub("", ANSI.sub("", raw.rstrip("\n")))
        match = WARNING.match(line)
        if match:
            flush()
            pending = None
            if line in seen:
                continue
            seen.add(line)
            by_library[match["path"].split("/", 1)[0]] += 1
            pending = (match["path"], unlinted_kind(match["message"]))
            continue
        note = NOTE.search(line)
        if note and pending is not None:
            by_linter[note["option"]] += 1
            pending = None
    flush()
    return by_linter, by_library


def report(root: Path, log: Path | None) -> dict:
    data = {"commit": git(root, "rev-parse", "HEAD").strip(), "source": source_counts(root)}
    if log is not None:
        with open(log, encoding="utf-8", errors="replace") as handle:
            by_linter, by_library = warning_counts(handle)
        data["warnings"] = {"total": sum(by_library.values()),
                            "by_linter": dict(by_linter.most_common()),
                            "by_library": dict(sorted(by_library.items()))}
    return data


def change(new: int, old: int | None) -> str:
    if old is None:
        return ""
    diff = new - old
    return f"{diff:+d}" if diff else "0"


def markdown(data: dict, base: dict | None) -> str:
    base = base or {}
    old_source = base.get("source", {})
    lines = [f"Technical debt at `{data['commit'][:10]}`"
             + (f", compared with `{base['commit'][:10]}`" if base.get("commit") else "") + ".", "",
             "| Count | Change | Source marker |", "|---:|---:|---|"]
    for name, count in data["source"].items():
        lines.append(f"| {count} | {change(count, old_source.get(name))} | {name} |")
    warnings = data.get("warnings")
    if warnings:
        old = base.get("warnings", {})
        lines += ["", f"Compiler warnings: {warnings['total']}"
                  + (f" ({change(warnings['total'], old.get('total'))})" if old else "") + ".", "",
                  "| Count | Change | Linter |", "|---:|---:|---|"]
        for name, count in warnings["by_linter"].items():
            lines.append(f"| {count} | {change(count, old.get('by_linter', {}).get(name, 0) if old else None)} | `{name}` |")
        lines += ["", "| Count | Change | Library |", "|---:|---:|---|"]
        for name, count in warnings["by_library"].items():
            lines.append(f"| {count} | {change(count, old.get('by_library', {}).get(name, 0) if old else None)} | `{name}` |")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--build-log", type=Path, help="lake build output to count warnings in")
    parser.add_argument("--base", type=Path, help="an earlier --json report to compare with")
    parser.add_argument("--json", type=Path, help="write the report as JSON")
    parser.add_argument("--markdown", type=Path, help="write the report as Markdown (default: stdout)")
    args = parser.parse_args()
    data = report(args.root, args.build_log)
    base = json.loads(args.base.read_text(encoding="utf-8")) if args.base else None
    if args.json:
        args.json.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    text = markdown(data, base)
    if args.markdown:
        args.markdown.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
