"""Bounded, advisory source scanning shared by the two diagnostics.

Reuse pinned_bump's lexer without modifying or copying it. It blanks nested
comments and ordinary escaped string/character literals and preserves offsets.
An appended sentinel detects unterminated comments/strings. Raw strings and
quoted identifiers containing lexical delimiters are explicitly unsupported
and fail the scan rather than losing declarations silently.
Prime sequences that the shared lexer reads as character literals also fail
visibly. Compound forms such as `class inductive` are not supported.

This is not a Lean parser: recognize line-leading declaration keywords with
common modifiers and single-line attributes. Names may use Unicode, primes,
qualification, or ordinary «quoted components». Custom commands, macro
expansions, multiline attributes, and syntax quotations are not interpreted;
quoted commands can look like declarations. Headers are source text, not
elaborated types. Unknown header syntax is retained, never classified as a
semantic conflict. Lean's compiler remains the syntax/semantic authority.
"""

from __future__ import annotations

import os
import re
import stat
from dataclasses import dataclass
from pathlib import Path

from bump.pinned_bump import _strip_lean_comments_and_strings

EXCLUDED = {".lake", ".git", "v1", "dependencies"}
DEFINITION_KINDS = {"def", "abbrev", "structure", "class", "inductive"}
WANTED_KINDS = {"theorem_wanted", "def_wanted"}
COMPONENT = r"(?:«[^«»\n]+»|[^\W\d][\w'!?]*)"
NAME = re.compile(rf"{COMPONENT}(?:\.{COMPONENT})*")
COMPONENT_RE = re.compile(COMPONENT)
COMMAND = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public|meta)[ \t]+)*"
    r"(?P<kind>def|abbrev|structure|class|inductive|theorem_wanted|def_wanted|"
    r"theorem|lemma|opaque|axiom|constant|instance|example|namespace|end|section|"
    r"mutual|import|open|variable|universe|set_option|attribute|export|notation|"
    r"syntax|macro_rules|macro|elab|initialize|deriving)\b",
    re.MULTILINE,
)
HEADER_TOKEN = re.compile(r"«[^«»\n]*»|:=|\bwhere\b|[(){}\[\]⦃⦄|]")
# Require qualification: an unqualified token might be a keyword, placeholder,
# or user notation. Retaining it costs a candidate, excluding it could hide one.
DIRECT_ALIAS = re.compile(rf"\s*:=\s*{COMPONENT}(?:\.{COMPONENT})+\s*")


class ScanError(ValueError):
    """Input could not be scanned reliably; report-only must still fail."""


@dataclass(frozen=True)
class Declaration:
    path: Path
    line: int
    kind: str
    name: str
    short_name: str
    signature: str
    direct_alias: bool


def lean_files(roots: list[Path]) -> list[Path]:
    """Read only real directories; deduplicate directories/files by device+inode."""
    files: dict[tuple[int, int], Path] = {}
    counts: dict[tuple[int, int], int] = {}

    def walk(directory: Path) -> int:
        info = directory.stat()
        identity = (info.st_dev, info.st_ino)
        if identity in counts:
            return counts[identity]
        counts[identity] = 0
        count = 0
        with os.scandir(directory) as entries:
            children = sorted(entries, key=lambda entry: entry.name)
        for entry in children:
            if entry.name in EXCLUDED:
                continue
            path = Path(entry.path)
            if entry.is_symlink():
                if path.suffix == ".lean":
                    raise ScanError(f"symlinked Lean source: {path}")
                continue
            if entry.is_dir(follow_symlinks=False):
                count += walk(path)
            elif path.suffix == ".lean":
                info = entry.stat(follow_symlinks=False)
                if not stat.S_ISREG(info.st_mode):
                    raise ScanError(f"not a regular Lean file: {path}")
                files.setdefault((info.st_dev, info.st_ino), path)
                count += 1
        counts[identity] = count
        return count

    if not roots:
        raise ScanError("at least one directory root is required")
    for root in sorted(roots):
        root = root.absolute()
        if EXCLUDED.intersection(root.parts):
            raise ScanError(f"excluded directory in root: {root}")
        for parent in (root, *root.parents):
            if parent.is_symlink():
                raise ScanError(f"symlink directory in root: {root}")
        if not root.is_dir():
            raise ScanError(f"not a directory root: {root}")
        if walk(root) == 0:
            raise ScanError(f"no Lean inputs in root: {root}")
    return sorted(files.values())


def clean_source(source: str) -> str:
    sentinel = "\nSOURCE_DIAGNOSTICS_SENTINEL"
    extended = _strip_lean_comments_and_strings(source + sentinel)
    if not extended.endswith(sentinel):
        raise ScanError("unterminated comment or string")
    code = extended[: -len(sentinel)]
    for match in re.finditer(r'\br#*"', source):
        if code[match.start()] == "r":
            raise ScanError("unsupported raw string literal")
    for match in re.finditer("«", code):
        end = source.find("»", match.start())
        if end < 0 or "\n" in source[match.start() : end]:
            raise ScanError("unterminated quoted identifier")
        if code[match.start() : end + 1] != source[match.start() : end + 1]:
            raise ScanError("unsupported lexical delimiter in quoted identifier")
    return code


def source_signature(source: str, code: str) -> str:
    """Stop at a body delimiter outside binders; no type normalization/truncation."""
    brackets: list[str] = []
    pairs = {")": "(", "}": "{", "]": "[", "⦄": "⦃"}
    for match in HEADER_TOKEN.finditer(code):
        token = match.group()
        if token.startswith("«"):
            continue
        if token in ("(", "{", "[", "⦃"):
            brackets.append(token)
        elif token in pairs:
            if not brackets or brackets.pop() != pairs[token]:
                raise ScanError("unbalanced declaration header")
        elif not brackets:
            return source[: match.start()].strip()
    if brackets:
        raise ScanError("unbalanced declaration header")
    return source.strip()


def declarations(path: Path) -> list[Declaration]:
    try:
        source = path.read_text(encoding="utf-8")
        code = clean_source(source)
        commands = list(COMMAND.finditer(code))
        found = []
        line, previous_start = 1, 0
        for index, command in enumerate(commands):
            kind = command.group("kind")
            if kind not in DEFINITION_KINDS | WANTED_KINDS:
                continue
            end = (
                commands[index + 1].start() if index + 1 < len(commands) else len(code)
            )
            start = command.end()
            while start < end and code[start].isspace():
                start += 1
            name = NAME.match(code, start, end)
            if name is None:
                raise ScanError(f"missing or unsupported name after {kind}")
            raw_name = NAME.match(source, start, end)
            if raw_name is None or raw_name.group() != name.group():
                raise ScanError(f"unsupported lexical delimiter in name after {kind}")
            if name.group() in DEFINITION_KINDS | WANTED_KINDS:
                raise ScanError(
                    f"unsupported compound declaration: {kind} {name.group()}"
                )
            tail = code[name.end() : end]
            if tail and not (
                tail[0].isspace() or tail[0] in ":({[⦃" or tail.startswith(".{")
            ):
                raise ScanError(f"unsupported name after {kind}: {name.group()!r}")
            raw_tail = source[name.end() : end]
            line += source.count("\n", previous_start, command.start())
            previous_start = command.start()
            found.append(
                Declaration(
                    path=path,
                    line=line,
                    kind=kind,
                    name=name.group(),
                    short_name=COMPONENT_RE.findall(name.group())[-1],
                    signature=source_signature(raw_tail, tail),
                    # Only a bare qualified RHS name with no type/binders/comments.
                    # Applied, typed or otherwise ambiguous aliases stay candidates.
                    direct_alias=kind == "abbrev"
                    and DIRECT_ALIAS.fullmatch(raw_tail) is not None,
                )
            )
        return found
    except (OSError, UnicodeError, ScanError) as exc:
        raise ScanError(f"{path}: {exc}") from exc


def scan(roots: list[Path]) -> tuple[int, list[Declaration]]:
    files = lean_files(roots)
    found = [declaration for path in files for declaration in declarations(path)]
    return len(files), found
