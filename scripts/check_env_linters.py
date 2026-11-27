#!/usr/bin/env python3
"""Report Mathlib's environment-linter findings on the declarations a change adds.

The environment linters of Batteries' `#lint`, with the ones Mathlib adds
(`docBlame`, `simpNF`, `unusedArguments`, `defsWithUnderscore`, ...), check
declarations after they are built. This script builds the Lean files that
`BASE...HEAD` adds or modifies (through one temporary aggregator module per
library), runs `lake exe runLinter` on each aggregator, and keeps the findings
on the declarations that the change adds.

A declaration counts as added when the change adds the line that declares it
(the line with its keyword and name, below any docstring, attribute or modifier;
for a structure field, a constructor or a `where` or `let rec` helper, its own
line), and no declaration of that name is in the files the change modifies,
renames or deletes, as they are at the base. A private declaration (one marked
`private`, such as a field or a structure's constructor; in a `module` file,
also one that is neither marked `public` nor in a `public section`, a `where` or
`let rec` helper unless its declaration exposes its body, which an instance's
helpers count as not doing, and the constructor of a structure with a private
field) is the same only as one of its own file: another file's private
declaration of that name is another declaration. An anonymous instance, whose
name Lean generates, is known by its namespace and header. A wanted statement
(`theorem_wanted`, `def_wanted`, `proof_wanted`, `instance_wanted`) elaborates
to a private placeholder, so it is not the declaration that proves it later. So
a change that only documents, tags or edits an existing declaration does not
report it, nor does one that moves a public declaration between those files, but
one that proves a wanted statement reports the proof. A finding that `runLinter`
prints without a position (a declaration without a source range, such as a
structure's `mk.injEq`) is placed on the nearest enclosing declaration of the
changed files that has one, under the same rule. `runLinter` imports the modules
with their private declarations, so it lints those as well.

    python3 scripts/check_env_linters.py --base origin/main [--report-only]

Exit 1 if a finding is kept (0 with --report-only), 0 if none, 2 if the files do
not build or the linter does not run. In GitHub Actions each kept finding also
annotates its line and the job summary counts them.
"""

from __future__ import annotations

import argparse
import bisect
import re
import subprocess
import sys
import tempfile
from collections import Counter
from collections.abc import Iterable, Iterator
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from bump.pinned_bump import _strip_lean_comments_and_strings
from lean_changes import (ROOT, AggregatorError, ChangedFile, add_common_arguments, aggregators,
                          annotation, base_text, changed_files, deleted_files, guarded, in_actions,
                          inert, relative, write_summary)

ENTRY = re.compile(r"^(?P<file>\S.*?\.lean):(?P<line>\d+):(?P<col>\d+): error: (?P<text>.*)$")
UNPLACED = re.compile(r"^#check (?P<text>.*)$")
HEADER = re.compile(r"^/- The `(?P<linter>[^`]+)` linter reports:")
# A module's name, as Lean prints it (with «» where needed), as `ChangedFile.lean_module` spells it.
MODULE = re.compile(r"^-- (?P<module>(?:«[^«»]*»|[^\s«])+)$")
# `runLinter` prints one of these when it has linted its module.
FINISHED = re.compile(r"^-- (?:Found \d+ errors? in|Linting passed for) ")


@dataclass(frozen=True)
class Finding:
    """A finding on `declaration`, at a 1-based line and column, or with no position.

    `private` is whether the linters printed the declaration's name as private (`name✝`).
    """

    declaration: str
    linter: str
    message: str
    module: str | None = None
    path: str | None = None
    line: int | None = None
    col: int | None = None
    private: bool = False


DECLARATION = re.compile(r"@?(?P<name>(?:«[^«»\n]*»|[^\s«])+)\s*(?P<rest>.*)", re.DOTALL)


def declaration_name(text: str) -> tuple[str, str, bool]:
    """Split `@Name.of.decl✝ the warning` into the user-facing name, the warning, and whether
    the name is private (Lean prints a private name with `✝`)."""
    match = DECLARATION.match(text)
    if match is None:
        return "", text, False
    private = "✝" in match.group("name")
    name = re.sub(r"✝[⁰¹²³⁴⁵⁶⁷⁸⁹]*", "", match.group("name"))
    return name.replace("«", "").replace("»", ""), match.group("rest"), private


def parse_run_linter(text: str, cwd: Path = ROOT) -> list[Finding]:
    """The findings that `runLinter` prints, with their linter and module."""
    findings: list[Finding] = []
    linter = "environment linter"
    module: str | None = None
    current: tuple[re.Match[str], list[str], bool] | None = None

    def finish() -> None:
        if current is None:
            return
        match, body, placed = current
        text = "\n".join([match.group("text"), *body]).strip()
        if not placed:
            text = text.removesuffix("-/").strip()
        name, message, private = declaration_name(text)
        message = message.removeprefix("/-").strip() if not placed else message
        if placed:
            findings.append(Finding(name, linter, message, module,
                                    relative(match.group("file"), cwd),
                                    int(match.group("line")), int(match.group("col")), private))
        else:
            findings.append(Finding(name, linter, message, module, private=private))

    for line in text.splitlines():
        if header := HEADER.match(line):
            finish()
            current = None
            linter = header.group("linter")
        elif match := ENTRY.match(line):
            finish()
            current = (match, [], True)
        elif match := UNPLACED.match(line):
            finish()
            current = (match, [], False)
        elif module_line := MODULE.match(line):
            finish()
            current = None
            module = module_line.group("module")
        elif not line.strip() or line.startswith(("-- ", "/-")):
            finish()
            current = None
        elif current is not None:
            current[1].append(line)
    finish()
    return list(dict.fromkeys(findings))


# Lean source scanning: enough to name the declarations of a file, not a parser.
COMPONENT = r"(?:«[^«»\n]+»|[^\W\d][\w'!?]*)"
NAME = rf"{COMPONENT}(?:\.{COMPONENT})*"
MODIFIERS = r"(?:private|protected|public|noncomputable|nonrec|partial|unsafe|scoped|local|meta)"
# A `module` file starts with this keyword (comments are blanked by then).
MODULE_HEADER = re.compile(r"\s*module\b")
# Batteries' wanted statements, each a private placeholder `def` of its name.
WANTED_KINDS = ("theorem_wanted", "def_wanted", "proof_wanted", "instance_wanted")
# How the index keys a wanted statement, apart from the declaration that proves it later.
WANTED = "wanted:"
DECLARATION_KINDS = ("theorem", "lemma", "def", "abbrev", "instance", "structure", "class",
                     "inductive", "opaque", "axiom", "example", *WANTED_KINDS,
                     "irreducible_def", "alias")
COMMAND = re.compile(
    r"^[ \t]*(?:set_option[ \t]+\S+[ \t]+\S+[ \t]+in\s+)*(?P<attributes>(?:@\[[^\]]*\]\s*)*)"
    rf"(?P<modifiers>(?:{MODIFIERS}\s+)*)"
    rf"(?P<kind>namespace|section|end|mutual|{'|'.join(DECLARATION_KINDS)})\b",
    re.MULTILINE)
# The kinds whose body can declare `where` and `let rec` helpers, named `<declaration>.<helper>`.
HELPER_KINDS = ("theorem", "lemma", "def", "abbrev", "instance", "opaque", "irreducible_def")
# A `where` helper's line: attributes, then its name.
HELPER = re.compile(rf"[ \t]*(?:@\[[^\]]*\][ \t]*)*(?P<name>{NAME})(?=[\s:({{\[⦃|]|$)")
# Words that can start a line among `where` helpers without declaring one.
NOT_HELPERS = frozenset({"termination_by", "decreasing_by", "deriving", "where", "with"})
LET_REC = re.compile(rf"\blet[ \t]+rec[ \t]+(?P<name>{NAME})")
NAME_RE = re.compile(NAME)
# Words that cannot name a declaration of a `let rec`.
KEYWORDS = frozenset({"let", "have", "show", "from", "fun", "match", "with", "if", "then", "else",
                      "do", "by", "at", "in", "calc", "suffices", "return", "for", "where", "rec",
                      "mut", "try", "catch", "finally", "unless", "open", "deriving",
                      "termination_by", "decreasing_by", "nomatch", "nofun"})
OPENERS, CLOSERS = "([{⟨⦃", ")]}⟩⦄"
# What may stand between the start of a declaration's range and its keyword.
PREFIX = re.compile(rf"\s+|@\[[^\]]*\]|{MODIFIERS}\b|set_option\s+\S+\s+\S+\s+in\b")
NAME_AT = re.compile(rf"\s*(?P<name>{NAME})")
# An instance's name, after an optional priority; an anonymous instance has none.
INSTANCE_NAME = re.compile(r"\s*(?:\(priority\s*:=[^)]*\)\s*)?(?P<name>" + NAME
                           + r")(?=[\s:(\[{⦃]|\.\{)")
FIELD = re.compile(rf"^[ \t]+(?:(?P<visibility>private|protected)[ \t]+)?"
                   rf"(?P<names>{NAME}(?:[ \t]+{NAME})*)"
                   r"[ \t]*(?:::|[:({\[⦃])", re.MULTILINE)
CONSTRUCTOR = re.compile(rf"^[ \t]*\|[ \t]*(?P<name>{NAME})", re.MULTILINE)


def clean(text: str) -> str | None:
    """`text` with comments and strings blanked (offsets kept), or `None` if it does not lex."""
    sentinel = "\nLEAN_CHANGES_SENTINEL"
    code = _strip_lean_comments_and_strings(text + sentinel)
    return code[: -len(sentinel)] if code.endswith(sentinel) else None


def unquote_name(name: str) -> str:
    return name.replace("«", "").replace("»", "")


@dataclass
class SourceIndex:
    """The declarations of one Lean file: full names and the lines that declare them.

    An anonymous instance, whose name Lean generates, is keyed by `instance <namespace>:
    <header>` instead, with its header's whitespace collapsed.
    """

    code: str | None
    line_starts: list[int] = field(default_factory=list)
    names_at: dict[int, set[str]] = field(default_factory=dict)
    line_of: dict[str, int] = field(default_factory=dict)
    private_names: set[str] = field(default_factory=set)

    @property
    def names(self) -> set[str]:
        return set(self.line_of)

    @property
    def public_names(self) -> set[str]:
        return set(self.line_of) - self.private_names

    def add(self, name: str, line: int, private: bool = False) -> None:
        self.names_at.setdefault(line, set()).add(name)
        self.line_of.setdefault(name, line)
        if private:
            self.private_names.add(name)

    def line_at(self, offset: int) -> int:
        return bisect.bisect_right(self.line_starts, offset)

    def declaration_line(self, line: int) -> int:
        """The line that declares the declaration whose range starts on `line`."""
        if self.code is None or not 1 <= line <= len(self.line_starts):
            return line
        pos = self.line_starts[line - 1]
        while (match := PREFIX.match(self.code, pos)) and match.end() > pos:
            pos = match.end()
        return self.line_at(pos)


def top_level(code: str, start: int, stop: int) -> Iterator[tuple[int, str]]:
    """The offsets and characters of `code[start:stop]` outside brackets."""
    depth = 0
    for offset in range(start, stop):
        char = code[offset]
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0:
            yield offset, char


def is_word_at(code: str, offset: int, word: str) -> bool:
    """Whether `word` stands alone at `offset`, not inside a longer identifier."""
    end = offset + len(word)
    return (code.startswith(word, offset)
            and (offset == 0 or not (code[offset - 1].isalnum() or code[offset - 1] in "_'.!?"))
            and (end >= len(code) or not (code[end].isalnum() or code[end] in "_'!?")))


def helpers(code: str, start: int, stop: int) -> list[tuple[str, int]]:
    """The `where` and `let rec` helpers that `code[start:stop]`, a declaration, declares, each
    named, as Lean names it, after the helpers whose values hold it (`go.inner` for a
    `let rec inner` in the value of a `where` helper `go`), with the offset of its name.

    `where` declares helpers after a body (`:= ...`, or match alternatives `| ...`), and
    structure fields when it comes straight after the signature (`instance : C where x := 0`);
    only the first are helpers, and a `let rec` in a field's value is the declaration's own.
    Fields can be followed by a second `where` with helpers, as a body can.
    """
    body = False
    where = None
    for offset, char in top_level(code, start, stop):
        if code.startswith(":=", offset):
            body = True
        elif char == "|" and not code[code.rfind("\n", 0, offset) + 1:offset].strip():
            body = True
        elif char == "w" and is_word_at(code, offset, "where"):
            if body:
                where = offset
                break
            # The fields' `where`: their values count as a body, so a later `where` starts
            # helpers.
            body = True
    if where is None:
        return let_recs(code, start, stop)
    found = let_recs(code, start, where)
    named = where_helpers(code, where + len("where"), stop)
    for number, (name, offset) in enumerate(named):
        # A helper's value runs to the line of the next one.
        end = code.rfind("\n", 0, named[number + 1][1]) + 1 if number + 1 < len(named) else stop
        found.append((name, offset))
        found += let_recs(code, offset + len(name), end, (name,))
    return found


def let_recs(code: str, start: int, stop: int,
             outer: tuple[str, ...] = ()) -> list[tuple[str, int]]:
    """The `let rec` helpers in `code[start:stop]`, which is in the value of the helpers
    `outer`, each named after those and the `let rec`s whose values hold it, as Lean names them
    (`a.b` for a `let rec b` in the value of a `let rec a`), with the offset of its name."""
    found: list[tuple[str, int]] = []
    pos = start
    while match := LET_REC.search(code, pos, stop):
        region_end = min(let_rec_end(code, match, stop), stop)
        # `let rec p ... := v, q ... := w` declares `p` and `q`: each runs to the next.
        decls = [(match.group("name"), match.start("name"), match.end()),
                 *let_rec_siblings(code, match.end(), region_end)]
        for number, (decl, offset, decl_start) in enumerate(decls):
            decl_end = decls[number + 1][1] if number + 1 < len(decls) else region_end
            name = (*outer, decl)
            found.append((".".join(name), offset))
            found += let_recs(code, decl_start, decl_end, name)
        pos = max(region_end, match.end())
    return found


def let_rec_siblings(code: str, start: int, stop: int) -> list[tuple[str, int, int]]:
    """The declarations after the first of a `let rec` whose declarations `code[start:stop]`
    holds after the first's name: each name after a `,` outside brackets in a value, with the
    offset of the name and of its end, when binders and `:` or `:=` follow it. A comma before
    a value's `:=`, as in `∀ x, P x`, never separates two."""
    found = []
    in_value = False
    for offset, char in top_level(code, start, stop):
        if code.startswith(":=", offset):
            in_value = True
        elif char == "," and in_value:
            decl = let_decl_name(code, offset + 1, stop)
            if decl is not None:
                found.append(decl)
                in_value = False
    return found


def let_decl_name(code: str, start: int, stop: int) -> tuple[str, int, int] | None:
    """The name that starts the declaration of a `let rec` at `start`, if one does: a name that
    is not a keyword, binders (names or bracketed groups), then `:` or `:=` (not `::`)."""
    name = NAME_AT.match(code, start, stop)
    if name is None or name.group("name") in KEYWORDS:
        return None
    pos, depth = name.end(), 0
    while pos < stop:
        char = code[pos]
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
            if depth < 0:
                return None
        elif depth == 0 and not char.isspace():
            if char == ":":
                if code.startswith("::", pos):
                    return None
                return name.group("name"), name.start("name"), name.end()
            binder = NAME_RE.match(code, pos, stop)
            if binder is None or binder.group(0) in KEYWORDS:
                return None
            pos = binder.end()
            continue
        pos += 1
    return None


def let_rec_end(code: str, match: re.Match[str], stop: int) -> int:
    """Where the value of the `let rec` that `match` found ends, before the body that it scopes
    over: at the first `;` on its line outside brackets, or else after the lines below it that
    are indented deeper than its `let`."""
    line_start = code.rfind("\n", 0, match.start()) + 1
    column = match.start() - line_start
    line_end = code.find("\n", match.end(), stop)
    if line_end < 0:
        line_end = stop
    for offset, char in top_level(code, match.end(), line_end):
        if char == ";":
            return offset
    end = line_end
    pos = line_end + 1
    while pos < stop:
        next_end = code.find("\n", pos, stop)
        if next_end < 0:
            next_end = stop
        text = code[pos:next_end]
        if text.strip():
            if len(text) - len(text.lstrip()) <= column:
                break
            end = next_end
        pos = next_end + 1
    return end


def where_helpers(code: str, start: int, stop: int) -> list[tuple[str, int]]:
    """The helpers after a `where` that ends at `start`: the names that start a line at the
    column of the first one (deeper lines are their bodies)."""
    found = []
    column = None
    line_start = start
    while line_start < stop:
        line_end = code.find("\n", line_start, stop)
        if line_end < 0:
            line_end = stop
        match = HELPER.match(code, line_start, line_end)
        if match and match.group("name") not in NOT_HELPERS:
            # The column of the line's first token, an attribute or the name.
            first = len(code[line_start:line_end]) - len(code[line_start:line_end].lstrip())
            if column is None:
                column = first
            if first == column:
                found.append((match.group("name"), match.start("name")))
        line_start = line_end + 1
    return found


def index_source(text: str) -> SourceIndex:
    """Scan `text` for its declarations, tracking `namespace`, `section` and `end`."""
    code = clean(text)
    index = SourceIndex(code)
    if code is None:
        return index
    index.line_starts = [0] + [i + 1 for i, char in enumerate(code) if char == "\n"]
    is_module = MODULE_HEADER.match(code) is not None
    # Lean's scopes, innermost last: each one's namespace component (if it opens one), whether
    # it is public, as in a `public section` or a scope inside one (Lean's scopes inherit
    # `isPublic`), and whether it exposes its definitions' bodies, as in an
    # `@[expose] public section` (they inherit attributes too). As `addScopes` does,
    # `namespace A.B` and `section A.B` open one scope per component, and `end A.B` closes as
    # many.
    scopes: list[tuple[list[str], bool, bool]] = []
    commands = list(COMMAND.finditer(code))
    for number, command in enumerate(commands):
        kind = command.group("kind")
        rest = command.end()
        stop = commands[number + 1].start() if number + 1 < len(commands) else len(code)
        name_match = NAME_AT.match(code, rest, stop)
        name = name_match.group("name") if name_match else None
        modifiers = command.group("modifiers").split()
        exposes = re.search(r"\bexpose\b", command.group("attributes")) is not None
        hides = re.search(r"\bno_expose\b", command.group("attributes")) is not None
        public_scope = bool(scopes) and scopes[-1][1]
        exposed_scope = bool(scopes) and scopes[-1][2]
        components = name.split(".") if name else []
        if kind == "namespace":
            scopes.extend(([unquote_name(part)], public_scope, exposed_scope)
                          for part in components or [""])
            continue
        if kind in ("section", "mutual"):
            public = public_scope or "public" in modifiers
            exposed = exposed_scope or exposes
            opened = len(components) if kind == "section" and components else 1
            scopes.extend(([], public, exposed) for _ in range(opened))
            continue
        if kind == "end":
            del scopes[len(scopes) - min(len(scopes), max(len(components), 1)):]
            continue
        prefix = [part for components, _, _ in scopes for part in components]
        line = index.line_at(command.start("kind"))
        # As Lean decides (`Visibility.isInferredPublic`): a declaration marked `private` is
        # private; in a `module` file, so is one that is neither marked `public` nor in a
        # `public section`.
        private = "private" in modifiers or (
            is_module and "public" not in modifiers and not public_scope)

        def full(declared: str) -> str:
            declared = unquote_name(declared)
            if declared.startswith("_root_."):
                return declared.removeprefix("_root_.")
            return ".".join([*prefix, declared])

        if kind == "class" and name == "inductive":
            name_match = NAME_AT.match(code, name_match.end(), stop)
            name = name_match.group("name") if name_match else None
            kind = "inductive"
        if kind == "alias":
            names = re.findall(NAME, code[rest:stop].split(":=", 1)[0])
            for declared in names:
                if declared != "_":
                    index.add(full(declared), line, private)
            continue
        if kind == "instance":
            name_match = INSTANCE_NAME.match(code, rest, stop)
            name = name_match.group("name") if name_match else None
            if name is None:
                # Lean names it from its type: key it by its namespace and header instead.
                end = next((offset for offset, char in top_level(code, rest, stop)
                            if code.startswith(":=", offset) or is_word_at(code, offset, "where")),
                           stop)
                header = " ".join(code[rest:end].split())
                index.add(f"instance in {'.'.join(prefix) or '_root_'}: {header}", line, private)
                continue
        if kind == "example" or name is None:
            continue
        declared = full(name)
        if kind in WANTED_KINDS:
            # A wanted statement matches only a wanted statement: the theorem that proves it,
            # under the same name, is new code. Each is a private placeholder, but moving one
            # to another changed file adds nothing, so it matches across those files.
            index.add(f"{WANTED}{declared}", line)
            continue
        index.add(declared, line, private)
        body = code[name_match.end():stop] if name_match else ""
        if kind in ("structure", "class"):
            # The constructor is `mk` unless one is named (`make ::`), and private if it is
            # marked so. A field marked `private` is private, and in a `module` file it makes
            # the constructor private too; elsewhere it does not.
            constructor, constructor_private, any_private_field = f"{declared}.mk", False, False
            where = re.search(r"\bwhere\b", body)
            if where:
                offset = name_match.end() + where.end()
                for fields in FIELD.finditer(code, offset, stop):
                    for part in fields.group("names").split():
                        if code[fields.end() - 2: fields.end()] == "::":
                            constructor = f"{declared}.{unquote_name(part)}"
                            constructor_private = fields.group("visibility") == "private"
                        else:
                            field_private = private or fields.group("visibility") == "private"
                            any_private_field |= field_private
                            index.add(f"{declared}.{unquote_name(part)}",
                                      index.line_at(fields.start("names")), field_private)
            index.add(constructor, line,
                      private or constructor_private or (is_module and any_private_field))
        elif kind == "inductive":
            for constructor in CONSTRUCTOR.finditer(code, name_match.end(), stop):
                index.add(f"{declared}.{unquote_name(constructor.group('name'))}",
                          index.line_at(constructor.start("name")), private)
        elif kind in HELPER_KINDS:
            # In a `module` file a `where` or `let rec` helper is public only if its
            # declaration is and exposes its body: an `abbrev`, or a definition marked
            # `@[expose]` or in an `@[expose]` section, unless it is marked `@[no_expose]`, but
            # never a theorem's. An instance of a class of propositions does not expose its
            # body, and the index cannot tell such a class from the source, so an instance's
            # helpers count as private: that can only report a moved helper as new, never
            # hide a new declaration.
            exposed = (kind == "abbrev" or exposes or exposed_scope) and not hides and \
                kind not in ("theorem", "lemma", "instance")
            helper_private = private or (is_module and not exposed)
            for helper, offset in helpers(code, name_match.end(), stop):
                index.add(f"{declared}.{unquote_name(helper)}", index.line_at(offset),
                          helper_private)
    return index


def enclosing(name: str) -> Iterable[str]:
    """`name` and its prefixes, longest first."""
    parts = name.split(".")
    for end in range(len(parts), 0, -1):
        yield ".".join(parts[:end])


@dataclass
class BaseNames:
    """The declarations of the files that a change modifies, renames or deletes, at the base."""

    # The names that each modified or renamed file declares at the base, by its path at HEAD.
    by_file: dict[str, set[str]] = field(default_factory=dict)
    # The public names that any of those files, or a deleted one, declares at the base.
    public: set[str] = field(default_factory=set)

    def add(self, index: SourceIndex, path: str | None = None) -> None:
        """Add a base file's declarations; `path` is its path at HEAD, unless it is deleted."""
        if path is not None:
            self.by_file.setdefault(path, set()).update(index.names)
        self.public |= index.public_names

    def existed(self, path: str, name: str, private: bool) -> bool:
        """Whether a declaration of `name`, at HEAD in `path`, was there at the base.

        A private declaration is the same one only if its own file declared it: another file's
        private declaration of that name is another declaration. A public one may have moved
        from another of the files.
        """
        return name in self.by_file.get(path, ()) or (not private and name in self.public)


@dataclass
class Placement:
    """Where a finding is reported, and whether its declaration is one the change adds."""

    path: str
    line: int
    col: int | None
    added: bool


def place(finding: Finding, files: dict[str, ChangedFile], indexes: dict[str, SourceIndex],
          base: BaseNames) -> Placement | None:
    """Where `finding` belongs among the changed files, or `None` if it is elsewhere."""

    def existed(path: str, names: set[str]) -> bool:
        index = indexes[path]
        return any(base.existed(path, name, name in index.private_names
                                or (name == finding.declaration and finding.private))
                   for name in names)

    if finding.path is not None:
        file = files.get(finding.path)
        if file is None:
            return None
        index = indexes[file.path]
        line = index.declaration_line(finding.line)
        # The declaration's own name when the file declares it. Otherwise, as for an anonymous
        # instance, whose name Lean generates, the names that the file declares on its line.
        if finding.declaration in index.line_of:
            names = {finding.declaration}
        else:
            names = {finding.declaration, *index.names_at.get(line, ())}
        new = line in file.added_lines and not existed(file.path, names)
        return Placement(file.path, finding.line, finding.col, new)
    # No position: the nearest enclosing declaration that a changed file declares.
    for path, file in files.items():
        if finding.module is not None and file.lean_module != finding.module:
            continue
        index = indexes[path]
        for candidate in enclosing(finding.declaration):
            line = index.line_of.get(candidate)
            if line is None:
                continue
            new = line in file.added_lines and not existed(path, {finding.declaration, candidate})
            return Placement(path, line, None, new)
    return None


def read_source(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


@guarded
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    add_common_arguments(parser)
    args = parser.parse_args()

    changed = changed_files(args.base)
    if not changed:
        print("No Lean file of the production libraries is added or modified.")
        return 0
    files = {file.path: file for file in changed}
    print(f"Checking the declarations of {len(changed)} changed Lean file(s) with runLinter.")
    outputs = []
    try:
        with aggregators(changed) as targets, tempfile.TemporaryDirectory() as tmp:
            if not targets:
                return 0
            build = subprocess.run(["lake", "build", *targets], cwd=ROOT, capture_output=True,
                                   text=True)
            if build.returncode != 0:
                print(inert(build.stdout + build.stderr), file=sys.stderr)
                print("The changed files do not build.", file=sys.stderr)
                return 2
            for target in targets:
                library = target.split(".", 1)[0]
                # Batteries' local linters then lint only the changed modules. The others,
                # docBlame and simpNF among them, lint every module of the package that the
                # aggregator imports; their findings elsewhere are dropped below.
                only = Path(tmp, f"{library}.txt")
                only.write_text("".join(f"{file.lean_module}\n" for file in changed
                                        if file.library == library and file.lean_module))
                result = subprocess.run(
                    ["lake", "exe", "runLinter", "--no-build", f"--only-modules={only}", target],
                    cwd=ROOT, capture_output=True, text=True)
                output = result.stdout + result.stderr
                if result.returncode not in (0, 1) or not any(
                        FINISHED.match(line) for line in output.splitlines()):
                    print(inert(output), file=sys.stderr)
                    print(f"runLinter did not run on {target}.", file=sys.stderr)
                    return 2
                outputs.append(output)
    except AggregatorError as error:
        print(inert(str(error)), file=sys.stderr)
        return 2

    indexes = {path: index_source(read_source(path)) for path in files}
    base = BaseNames()
    for file in changed:
        if file.base_path and (text := base_text(args.base, file.base_path)) is not None:
            base.add(index_source(text), file.path)
    for path in deleted_files(args.base):
        if (text := base_text(args.base, path)) is not None:
            base.add(index_source(text))

    findings = list(dict.fromkeys(f for output in outputs for f in parse_run_linter(output)))
    kept: list[tuple[Finding, Placement]] = []
    existing = elsewhere = 0
    unplaced: list[Finding] = []
    changed_modules = {file.lean_module for file in changed}
    for finding in findings:
        placement = place(finding, files, indexes, base)
        if placement is None:
            if finding.path is None and finding.module in changed_modules:
                unplaced.append(finding)
            else:
                elsewhere += 1
        elif placement.added:
            kept.append((finding, placement))
        else:
            existing += 1
    print(f"runLinter reported {len(findings)} finding(s): {len(kept)} on declarations the "
          f"change adds, {existing} on declarations it keeps, {elsewhere} in modules it does "
          f"not change, {len(unplaced)} without a position in a changed module that could not "
          "be placed.")
    for finding in unplaced:
        print(inert(f"  not placed: {finding.linter}: {finding.declaration} {finding.message}"))
    level = "warning" if args.report_only else "error"
    for finding, placement in kept:
        message = finding.message if finding.path is not None else (
            f"{finding.declaration} {finding.message}")
        if in_actions():
            print(annotation(level, placement.path, placement.line, finding.linter, message,
                             placement.col))
        print(inert(f"{placement.path}:{placement.line}:{placement.col or 1}: "
                    f"{finding.linter}: {finding.declaration} {finding.message}"))
    if kept or unplaced:
        counts = Counter(finding.linter for finding, _ in kept)
        rows = "".join(f"| `{linter}` | {count} |\n" for linter, count in counts.most_common())
        note = (f"\n{len(unplaced)} finding(s) without a position in a changed module could not "
                "be placed on a declaration; see the job log.\n" if unplaced else "")
        write_summary(f"### Environment-linter findings on added declarations\n\n"
                      f"| Linter | Findings |\n|---|---:|\n{rows}{note}\n")
    if kept:
        print(f"{len(kept)} finding(s) on added declarations. Fix them, or where a finding is "
              "wrong, mark the declaration `@[nolint <linter>]`.")
        return 0 if args.report_only else 1
    print("No environment-linter finding on the added declarations.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
