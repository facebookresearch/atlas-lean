#!/usr/bin/env python3
"""The Lean files that a change adds or modifies, and the lines it adds to them.

The linter checks in CI report a finding only on code that a pull request adds,
so existing code does not fail a check whatever its style. This module reads
the change from `git diff BASE...HEAD`, the way scripts/check_copyright.py
does, and writes the temporary aggregator modules that the Lean tools need.

Run with: python3 -m unittest discover -s scripts -p test_lean_changes.py
"""

from __future__ import annotations

import contextlib
import os
import re
import subprocess
from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The libraries that lakefile.toml builds with Mathlib's standard linter set.
PRODUCTION_LIBRARIES = ("MathlibExt", "CSLibExt", "PhyslibExt", "Domains", "WantedExt")

# Each library globs its submodules (`MathlibExt.+`), so an aggregator must be
# one of them to build. It is untracked, and removed when the check ends.
AGGREGATOR = "LintChanged"

HUNK = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")


@dataclass(frozen=True)
class ChangedFile:
    """A Lean file of the change: its path, git status letter and added lines."""

    path: str
    status: str
    added_lines: frozenset[int]

    @property
    def library(self) -> str:
        return self.path.split("/", 1)[0]

    @property
    def module(self) -> str:
        return self.path.removesuffix(".lean").replace("/", ".")


def parse_diff(text: str) -> dict[str, frozenset[int]]:
    """Map each file of a `git diff --unified=0` to the line numbers it adds."""
    added: dict[str, set[int]] = {}
    path: str | None = None
    for line in text.splitlines():
        if line.startswith("+++ "):
            target = line[4:]
            path = target[2:] if target.startswith("b/") else None
            if path is not None:
                added.setdefault(path, set())
            continue
        match = HUNK.match(line)
        if match and path is not None:
            start = int(match.group(1))
            count = int(match.group(2)) if match.group(2) is not None else 1
            added[path].update(range(start, start + count))
    return {path: frozenset(lines) for path, lines in added.items()}


def parse_name_status(text: str) -> dict[str, str]:
    """Map each path of a `git diff --name-status -z` to its status letter."""
    fields = text.split("\0")
    statuses: dict[str, str] = {}
    i = 0
    while i < len(fields) and fields[i]:
        letter = fields[i][0]
        if letter in "RC":
            statuses[fields[i + 2]] = letter
            i += 3
        else:
            statuses[fields[i + 1]] = letter
            i += 2
    return statuses


def git(args: Sequence[str], cwd: Path) -> str:
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True,
                          text=True).stdout


def changed_files(base: str, libraries: Sequence[str] = PRODUCTION_LIBRARIES,
                  cwd: Path = ROOT) -> list[ChangedFile]:
    """The Lean files of `libraries` that `base...HEAD` adds, modifies or renames."""
    specs = [f"{library}/*.lean" for library in libraries]
    common = ["--no-color", "--no-ext-diff", "-M", "--diff-filter=AMR", f"{base}...HEAD", "--"]
    diff = git(["diff", "--unified=0", "--src-prefix=a/", "--dst-prefix=b/", *common, *specs],
               cwd)
    statuses = parse_name_status(git(["diff", "--name-status", "-z", *common, *specs], cwd))
    added = parse_diff(diff)
    return [ChangedFile(path, statuses[path], added.get(path, frozenset()))
            for path in sorted(statuses)]


@contextlib.contextmanager
def aggregators(files: Sequence[ChangedFile], cwd: Path = ROOT) -> Iterator[list[str]]:
    """Write one aggregator module per library that imports its changed modules.

    Yields the aggregator module names. The files are plain (not `module`), so
    that they can import files of either kind, and are deleted on exit.
    """
    written: list[Path] = []
    names: list[str] = []
    try:
        for library in sorted({file.library for file in files}):
            path = cwd / library / f"{AGGREGATOR}.lean"
            if path.exists():
                raise FileExistsError(f"{path} already exists")
            imports = sorted({file.module for file in files if file.library == library})
            path.write_text("".join(f"import {module}\n" for module in imports))
            written.append(path)
            names.append(f"{library}.{AGGREGATOR}")
        yield names
    finally:
        for path in written:
            path.unlink(missing_ok=True)


def relative(path: str, cwd: Path = ROOT) -> str:
    """A path as Lean prints it (absolute or relative), relative to the repository."""
    return os.path.relpath(Path(cwd, path).resolve(), cwd.resolve()) if path else path


def escape(text: str, property_value: bool = False) -> str:
    text = text.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    if property_value:
        text = text.replace(":", "%3A").replace(",", "%2C")
    return text


def annotation(level: str, path: str, line: int, title: str, message: str,
               col: int | None = None) -> str:
    """A GitHub Actions workflow command that annotates `path` at `line`."""
    fields = [f"file={escape(path, True)}", f"line={line}"]
    if col is not None:
        fields.append(f"col={col}")
    fields.append(f"title={escape(title, True)}")
    return f"::{level} {','.join(fields)}::{escape(message)}"


def in_actions() -> bool:
    return os.environ.get("GITHUB_ACTIONS") == "true"


def write_summary(markdown: str) -> None:
    """Append to the job summary in GitHub Actions; elsewhere, do nothing."""
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as out:
            out.write(markdown)
