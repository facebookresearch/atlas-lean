#!/usr/bin/env python3
"""Collapse the v2 declaration dump onto wiki articles.

    scripts/extract_v2_lean_dependencies.py DUMP.jsonl[.gz] OUTPUT.json [--registry REGISTRY.json --names NAMES]

The dump (from scripts/dump_v2_dependencies.lean, which the Pages build runs
after building the libraries) lists, for every constant in the v2 modules, the v2 constants its
type and value use. Articles are exactly the Lean names the wiki's articles
credit, one per statement page, as Autoform reads them (a reference is no
article), and, for a page an earlier sync wrote with only a module and a name,
the declaration the Lean index gives it, as lean-facts resolves it; so
source-level commands and compiled constants
cannot disagree about projections, wrappers, wanted declarations, or docstrings. An
article's statement dependencies are the articles its type reaches through
non-article constants (private helpers, auxiliary declarations, undocumented
definitions), together with what its value reaches when it is a definition (its
body) or an inductive type (its constructors' types). A theorem's proof
dependencies are those its value reaches the same way, minus the statement
ones. Mutually recursive definitions and mutual inductive types depend on each
other, which a dependency DAG can't show, so statement edges inside such a group
are left out and the group is listed under "mutual". A declaration a statement
page's row lists as a duplicate (`sync_wiki.duplicate_names`), the article's
result stated again, has no page. For any other article the way stops at it as
at the article, which a use of it reaches, so an article that uses only the
duplicate depends on the article. For its own article it is part of the
article, as a non-article constant would be: the article depends on what the
duplicate uses, and never on itself (own_duplicates). Nothing is written when a
page stands for a duplicate, when two private constants of the dump take the
name of a duplicate or of its article, or when the dump lacks one of them that
the Lean sources still declare. When the Lean no longer declares one of them, a
warning names both, and a use of the duplicate counts for no page: the way
still stops at it (resolve_aliases). The build adds the result to the
articles' Depends on lists; it is never committed.

With --registry, the dump must have been made with NAMES, the Mathlib
declarations wiki pages credit (`sync_wiki.py mathlib-names`, passed to
scripts/dump_v2_dependencies.lean), and the script also writes REGISTRY.json:
for each article, the credited Mathlib declarations its statement or its proof
names itself, with no constant between (bridge edges; a definition's body and an
inductive type's constructors count as its statement). The credited
declarations it reaches only through other constants, non-article v2 constants
or Mathlib declarations no page credits, which the dump follows by the same
rules, give no bridge: the registry lists them apart, by kind (`left_out`), and
no page gets them. For each credited declaration found, the registry gives its
module, its kind and the credited declarations it reaches by those rules,
through its proof as through its statement (Mathlib edges); the names the dump
did not find in a Mathlib module (`missing`), among them those that are v2
constants (`project`); and what it was made from (`inputs`: the digest of NAMES,
of the dump and of the duplicates the rows list with their articles, and
Mathlib's revision in lake-manifest.json), in a format of its own
(REGISTRY_FORMAT). Every project row of the dump must carry its lists of
credited declarations, nested as the dump writes them; the dump's rows for
credited names never replace the project's rows, and every name of NAMES must
have exactly one: otherwise nothing is written. OUTPUT.json is the same with or
without it. Both files are written only once both are made, each whole.
"""

from __future__ import annotations

import functools
import gzip
import hashlib
import json
import os
import re
import secrets
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BLUEPRINT = ROOT / "blueprint"
LIBRARIES = frozenset({"MathlibExt", "CSLibExt", "PhyslibExt", "Domains", "WantedExt"})
# The key of `missing_articles` for absent targets whose names start with no library name.
UNPREFIXED = "unprefixed"
# A definition is its body and an inductive type its constructors, so their values are part of the statement
# (`abbrev`, and `instance` of a class of data, compile to `def`; an `instance` of a proposition compiles to
# `theorem`). Lean cannot unfold a theorem's proof or an `opaque` body, so no statement can depend on them: those
# values give proof dependencies only.
STATEMENT_VALUE = frozenset({"def", "inductive"})


DUMP_FORMAT = {"dump": "atlas-v2-dependencies", "format": 5, "closure": "statement-and-all-uses"}
# The format of the registry --registry writes, apart from the dump's: since 6, it records the duplicates lists it was
# made for (`inputs.aliases_sha256`), as its bridges depend on them while the extraction beside it may not, and every
# consumer checks them against its checkout's rows (sync_wiki.registry_problems).
REGISTRY_FORMAT = 6
# The lists of credited declarations every project row of such a dump carries; a definition's or an inductive
# type's row carries `mathlib_state` too. Each `_direct` list holds the names its expressions name themselves, and is
# part of the list that reaches through other constants from the same expressions; what an expression reaches through
# what constants state is part of what it reaches through everything they use.
CREDIT_LISTS = ("mathlib_type", "mathlib_type_used", "mathlib_value", "mathlib_type_direct", "mathlib_value_direct")
CHAINS = (("mathlib_type_direct", "mathlib_type"), ("mathlib_type", "mathlib_type_used"))
# A definition's body and an inductive type's constructors are part of what it states.
STATED_VALUE_CHAINS = (("mathlib_value_direct", "mathlib_state"), ("mathlib_state", "mathlib_value"))
# What a row for a credited name the dump found carries, besides its lists (the project's lists but the direct ones).
FOUND_TEXT = ("module", "kind")
FOUND_FLAGS = ("proposition", "structure", "class")
FOUND_LISTS = ("mathlib_type", "mathlib_type_used", "mathlib_value")
# The kinds the dump's kindOf writes, and the keys of a missing name's row: a row has these or a found one's.
KINDS = frozenset({"theorem", "def", "axiom", "opaque", "inductive", "constructor", "recursor", "quot"})
MISSING_KEYS = frozenset({"name", "registered", "missing", "module_given", "project"})


def read_dump(path: Path, framed: bool = False) -> tuple[dict[str, dict], dict[str, dict], dict[str, dict]]:
    """The dump's rows for the project's constants and, apart, those for credited Mathlib names (`registered`):
    a credited name that is also a project constant has one row of each kind, and neither replaces the other. A
    dump made with a names list (*framed*) is one whole stream: a header on its first line, a footer on its last,
    each once and neither both, and only rows between them, a row's `registered` literally true if there; its header
    and footer come back apart. A dump made without one is read as it always was, empty values passed over."""
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as handle:
        lines = [json.loads(line) for line in handle]

    def frame(row: object, key: str) -> bool:
        return isinstance(row, dict) and key in row and ({"dump", "end"} - {key}).isdisjoint(row)

    framing: dict[str, dict] = {}
    body = list(enumerate(lines, 1))
    if framed:
        if len(lines) < 2 or not frame(lines[0], "dump") or not frame(lines[-1], "end"):
            raise ValueError("the dump does not open with its header and close with its footer")
        framing, body = {"header": lines[0], "end": lines[-1]}, body[1:-1]
    rows: dict[str, dict] = {}
    registered: dict[str, dict] = {}
    for number, row in body:
        if not row and not framed:
            continue
        if not isinstance(row, dict) or not ({"dump", "end"} & row.keys() or isinstance(row.get("name"), str)):
            raise ValueError(f"line {number} of the dump is no row")
        if "dump" in row or "end" in row:
            if framed:
                raise ValueError(f"line {number} of the dump is a second header or footer")
            continue
        if framed and (not row["name"] or row.get("registered", True) is not True):
            raise ValueError(f"line {number} of the dump is no row: a row has a name, and `registered` is true if "
                             "there")
        table = registered if row.get("registered") else rows
        if row["name"] in table:
            raise ValueError(f"the dump has two {'credited' if table is registered else 'project'} rows for "
                             f"{row['name']}")
        table[row["name"]] = row
    return rows, registered, framing


def row_problems(rows: dict[str, dict], found: set[str]) -> list[str]:
    """What in the project rows of a dump made with a names list is not as the current format writes it: each list
    of CREDIT_LISTS (and `mathlib_state` for a definition or an inductive type) must be there, as a list of names
    the dump found, and each must hold the one before it in its chain: what a type names itself, what it reaches
    through what constants state, what it reaches through all they use (CHAINS); for a definition or an inductive
    type, what its value names itself, what it reaches through what constants state, what it reaches through all
    they use (STATED_VALUE_CHAINS), and for any other row, what its value names itself within what it reaches. Read
    with a default, a row of an older format would reach nothing, and a direct use would read as one through other
    constants, or as no edge at all."""
    def names(value: object) -> bool:
        return isinstance(value, list) and all(isinstance(item, str) for item in value)

    problems = []
    for name, row in sorted(rows.items()):
        if row.get("kind") not in KINDS:
            problems.append(f"the dump's row for {name} has no kind of declaration the dump writes")
        elif row["kind"] not in STATEMENT_VALUE and "mathlib_state" in row:
            problems.append(f"the dump's row for {name} lists `mathlib_state`, but the value of a {row['kind']} is "
                            "no part of its statement")
        for key in CREDIT_LISTS + (("mathlib_state",) if row.get("kind") in STATEMENT_VALUE else ()):
            if not names(row.get(key)):
                problems.append(f"the dump's row for {name} has no list of names `{key}`")
            elif unfound := sorted(set(row[key]) - found):
                problems.append(f"the dump's row for {name} lists {unfound[:3]} under `{key}`, which it did not find")
        stated = row.get("kind") in STATEMENT_VALUE
        for inner, outer in CHAINS + (STATED_VALUE_CHAINS if stated else (("mathlib_value_direct", "mathlib_value"),)):
            held, holder = row.get(inner), row.get(outer)
            if names(held) and names(holder) and (outside := sorted(set(held) - set(holder))):
                problems.append(f"the dump's row for {name} lists {outside[:3]} under `{inner}` but not under "
                                f"`{outer}`")
    return problems


def registered_problems(registered: dict[str, dict], project: set[str], given: dict[str, bool]) -> list[str]:
    """What in the dump's rows for credited names is not as the current format writes it. A found row names its
    Mathlib module and a kind the dump writes, says whether it is a proposition (a theorem always is), a structure (an
    inductive type at most) and a class, and lists the credited declarations it reaches (FOUND_LISTS, and
    `mathlib_state` exactly for a definition or an inductive type), each a list of found names, nested as row_problems
    has them; it is no constant of the project. A missing row has no other keys than MISSING_KEYS: whether the names
    list gave its module, as the list does (*given*), and `project` exactly when the name is a constant of the
    project (*project*, whose own row it then stands beside)."""
    def names(value: object) -> bool:
        return isinstance(value, list) and all(isinstance(item, str) for item in value)

    found = {name for name, row in registered.items() if "missing" not in row}
    problems = []
    for name, row in sorted(registered.items()):
        about = f"the dump's row for the credited name {name}"
        if "missing" in row:
            if row["missing"] is not True or not row.keys() <= MISSING_KEYS or \
                    not isinstance(row.get("module_given"), bool) or row.get("project", True) is not True:
                problems.append(f"{about} is malformed: a missing name's row says `missing`, whether the list gave its "
                                "module (`module_given`) and `project` if so, and nothing a found row says")
            elif name in given and row["module_given"] is not given[name]:
                problems.append(f"{about} says the names list {'gave' if row['module_given'] else 'did not give'} its "
                                f"module, but the list {'does not' if row['module_given'] else 'does'}")
            elif ("project" in row) is not (name in project):
                problems.append(f"{about} {'says' if 'project' in row else 'does not say'} the name is a constant of "
                                f"the project, which the dump's own rows {'do not' if name not in project else 'do'}")
            continue
        if not row.keys().isdisjoint(MISSING_KEYS - {"name", "registered"}):
            problems.append(f"{about} is both found and missing")
            continue
        if name in project:
            problems.append(f"{about} is found in Mathlib, but the dump has a row for it as a constant of the project")
        module = row.get("module")
        if not isinstance(module, str) or not (module == "Mathlib" or module.startswith("Mathlib.")):
            problems.append(f"{about} names no Mathlib module")
        if row.get("kind") not in KINDS:
            problems.append(f"{about} has no kind of declaration the dump writes")
        problems += [f"{about} does not say whether it is a `{key}`" for key in FOUND_FLAGS
                     if not isinstance(row.get(key), bool)]
        if row.get("kind") == "theorem" and row.get("proposition") is not True:
            problems.append(f"{about} is a theorem whose type is not a proposition")
        if row.get("structure") is True and row.get("kind") != "inductive":
            problems.append(f"{about} is a structure but no inductive type")
        stated = row.get("kind") in STATEMENT_VALUE
        if not stated and "mathlib_state" in row:
            problems.append(f"{about} lists `mathlib_state`, but the value of a {row.get('kind')} is no part of its "
                            "statement")
        for key in FOUND_LISTS + (("mathlib_state",) if stated else ()):
            if not names(row.get(key)):
                problems.append(f"{about} has no list of names `{key}`")
            elif unfound := sorted(set(row[key]) - found):
                problems.append(f"{about} lists {unfound[:3]} under `{key}`, which it did not find")
        for inner, outer in (("mathlib_type", "mathlib_type_used"),) + ((("mathlib_state", "mathlib_value"),)
                                                                      if stated else ()):
            held, holder = row.get(inner), row.get(outer)
            if names(held) and names(holder) and (outside := sorted(set(held) - set(holder))):
                problems.append(f"{about} lists {outside[:3]} under `{inner}` but not under `{outer}`")
    return problems


def file_problem(files: dict[str, Path], outputs: tuple[str, ...],
                 folders: dict[str, Path] | None = None) -> str | None:
    """Why *files*, by label, cannot be read and written as given: an output inside one of the *folders* of inputs (by
    label, resolved), that is a symbolic link, dangling or not, which installing a file in its place would replace with
    a regular file, or that is there but is no regular file (a folder, say); or two that are one file, by their paths,
    through a symbolic link, or as two hard links of it (one device and inode)."""
    for label in outputs:
        for where, folder in (folders or {}).items():
            if files[label].resolve().is_relative_to(folder.resolve()):
                return f"{label}, {files[label]}, is inside {where}, whose files are inputs; write it elsewhere"
        if files[label].is_symlink():
            return f"{label}, {files[label]}, is a symbolic link; give the path of the file itself"
        if files[label].exists() and not files[label].is_file():
            return f"{label}, {files[label]}, is there but is no regular file; an output is a regular file or absent"
    seen: dict[tuple, str] = {}
    for label, path in files.items():
        keys = [("path", path.resolve())]
        if path.exists():
            keys.append(("file", path.stat().st_dev, path.stat().st_ino))
        if clash := next((seen[key] for key in keys if key in seen), None):
            return f"{clash} and {label} are one file, {path}; give each its own"
        seen.update((key, label) for key in keys)
    return None


class UndoError(OSError):
    """An output could not take its place, and putting back the ones that had failed too: the outputs may be new and
    old mixed. *kept* holds, by output, the copy of its earlier bytes, left beside it."""

    def __init__(self, error: BaseException, kept: dict[Path, Path]) -> None:
        super().__init__(str(error))
        self.kept = kept


def write_whole(outputs: dict[Path, str]) -> None:
    """Write the files together, each whole: all go to temporary files beside them first, and a copy of each output
    they replace is kept beside it; then each takes its output's place. If one cannot, those that did are undone, each
    earlier output put back and each new one removed, so the outputs, regular files, are either all new or all as they
    were (were the undoing to fail, the kept copies stay beside them, and UndoError names them). The temporary files
    take names no file has; an
    output that is a symbolic link or no regular file, and two outputs that are one file (file_problem), are refused
    before anything is written."""
    if problem := file_problem({str(path): path for path in outputs}, tuple(str(path) for path in outputs)):
        raise ValueError(problem)

    def scratch(path: Path, role: str) -> Path:
        while True:
            candidate = path.with_name(f".{path.name}.{secrets.token_hex(6)}.{role}")
            try:
                candidate.open("x").close()
                return candidate
            except FileExistsError:
                continue

    staged: dict[Path, Path] = {}
    kept: dict[Path, Path] = {}
    installed: list[Path] = []
    try:
        for path, text in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            staged[path] = scratch(path, "partial")
            staged[path].write_text(text, encoding="utf-8")
        for path in outputs:
            if path.is_file():
                kept[path] = scratch(path, "previous")
                shutil.copy2(path, kept[path])
        try:
            for path in outputs:
                staged[path].replace(path)
                installed.append(path)
        except BaseException:
            try:
                for path in reversed(installed):
                    if path in kept:
                        os.replace(kept[path], path)
                    else:
                        os.unlink(path)
            except Exception as error:
                # The copies of the replaced outputs not put back stay beside them, for a person to put back.
                left = {path: kept.pop(path) for path in installed if path in kept and kept[path].exists()}
                raise UndoError(error, left) from error
            raise
    finally:
        for leftover in (*staged.values(), *kept.values()):
            leftover.unlink(missing_ok=True)


def read_names(path: Path) -> list[str]:
    """The credited Mathlib names of a `sync_wiki.py mathlib-names` file, one per line before an optional tab."""
    return [line.split("\t")[0] for line in path.read_text().splitlines() if line.strip()]


def given_modules(path: Path) -> dict[str, bool]:
    """Whether each line of a names file gives its name's module: a name, a tab and a module, as the dump reads it."""
    return {line.split("\t")[0]: len(line.split("\t")) == 2 for line in path.read_text().splitlines() if line.strip()}


def names_digest(names: list[str]) -> str:
    """The digest of a list of credited names, sorted, one per line: what `sync_wiki.py` recomputes from the
    annotations alone, whatever modules a checkout has."""
    return hashlib.sha256("".join(f"{name}\n" for name in sorted(names)).encode("utf-8")).hexdigest()


def file_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def mathlib_revision() -> str | None:
    """Mathlib's revision in lake-manifest.json, which pins the declarations the dump read."""
    manifest = ROOT / "lake-manifest.json"
    if not manifest.is_file():
        return None
    packages = json.loads(manifest.read_text()).get("packages", [])
    return next((package.get("rev") for package in packages if package.get("name") == "mathlib"), None)


def publish_private_targets(rows: dict[str, dict], manifest: set[str]) -> dict[str, dict]:
    """Key private constants that the roadmap publishes by their source names.

    In a `module` file a declaration outside `public section` without
    `public` is private, and Batteries elaborates `theorem_wanted` and
    `def_wanted` to private placeholders. The dump lists such constants as
    `_private.<module>.0.<name>` while the roadmap names them `<name>`;
    unmatched, every wanted article had no dependencies.
    """

    renamed: dict[str, str] = {}
    for name, row in rows.items():
        prefix = f"_private.{row['module']}.0."
        if row.get("private") and name.startswith(prefix):
            public = name[len(prefix) :]
            if public in manifest and public not in rows:
                renamed[name] = public
    if not renamed:
        return rows
    return {
        renamed.get(name, name): {
            **row,
            "type": [renamed.get(use, use) for use in row["type"]],
            "value": [renamed.get(use, use) for use in row["value"]],
        }
        for name, row in rows.items()
    }


# A conservative ASCII subset of Lean 4.36.0 (611c117b) `Name.toString`'s ordinary
# identifier components. A leading letter excludes `_root_`, `_private`, `_hyg`,
# `_inaccessible`, and other internal names. This is not a Lean Name decoder.
_QUOTED_NAME_TOOLCHAIN = "leanprover/lean4:v4.36.0"
_ORDINARY_COMPONENT = r"[A-Za-z][A-Za-z0-9_]*"
_ORDINARY_AUTHORED = re.compile(
    rf"(?:{_ORDINARY_COMPONENT}|«{_ORDINARY_COMPONENT}»)(?:\.(?:{_ORDINARY_COMPONENT}|«{_ORDINARY_COMPONENT}»))*"
)


def compiled_spelling(authored: str) -> str | None:
    """The one canonical spelling for an ordinary name with redundant source quotes, if supported."""
    if "«" not in authored or _ORDINARY_AUTHORED.fullmatch(authored) is None:
        return None
    return ".".join(part[1:-1] if part.startswith("«") else part for part in authored.split("."))


def join_missing_quoted_articles(rows: dict[str, dict], missing: set[str], manifest: set[str],
                                 listed: dict[str, str], registered: dict[str, dict],
                                 source_index) -> dict[str, dict]:
    """Try the authored-to-compiled fallback only after stock exact and private resolution."""
    candidates = [(compiled, authored) for authored in sorted(missing)
                  if (compiled := compiled_spelling(authored)) is not None and compiled in rows]
    if not candidates:
        return rows
    try:
        toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    except FileNotFoundError:
        return rows
    if toolchain != _QUOTED_NAME_TOOLCHAIN:
        return rows

    rename: dict[str, str] = {}
    for compiled, authored in candidates:
        if compiled in manifest or compiled in rename:
            raise ValueError(f"competing article spellings for {compiled}")
        rename[compiled] = authored

    destinations = set(rename.values())
    for name in manifest - destinations:
        if compiled_spelling(name) in rename:
            raise ValueError(f"competing article spelling for a quoted target: {name}")
    for name in listed.keys() | set(listed.values()) | registered.keys():
        if name in rename or name in destinations or compiled_spelling(name) in rename:
            raise ValueError(f"quoted-name fallback overlaps a duplicate or registry endpoint: {name}")

    index = source_index()
    for names in (index.declarations, index.duplicates):
        for name in names:
            if name in rename or (name not in destinations and compiled_spelling(name) in rename):
                raise ValueError(f"competing source spelling for a quoted article: {name}")
    for compiled, authored in rename.items():
        sources = index.occurrences(authored)
        row = rows[compiled]
        if (len(sources) != 1 or sources[0].private or row.get("private") is not False or
                sources[0].path.with_suffix("").as_posix().replace("/", ".") != row["module"]):
            raise ValueError(f"cannot bind {compiled} to the unique public source owner of {authored}")

    result: dict[str, dict] = {}
    for name, row in rows.items():
        if compiled_spelling(name) in rename:
            raise ValueError(f"competing compiled spelling for a quoted target: {name}")
        if row.get("private"):
            prefix = f"_private.{row['module']}.0."
            if (suffix := name.removeprefix(prefix)) != name and (
                    suffix in rename or suffix in destinations or compiled_spelling(suffix) in rename):
                raise ValueError(f"quoted-name fallback overlaps a private row: {name}")
        authored = rename.get(name, name)
        changed = authored != name
        for field in ("type", "value"):
            for use in row[field]:
                if use in destinations:
                    raise ValueError(f"{name} has a dangling {field} reference to quoted target {use}")
                changed |= use in rename
        result[authored] = ({**row, "name": authored,
                             **{field: [rename.get(use, use) for use in row[field]]
                                for field in ("type", "value")}} if changed else row)
    return result


def article_manifest() -> set[str]:
    """The Lean names the wiki's articles state, one per statement page Autoform's own loader reads: the
    declaration the page's row credits (its Lean link to this project with role `states`, or its only one with no
    role, unless the page is stated elsewhere), as `sync_wiki.page_owner` reads it for `lean-facts` and the cards,
    the row joined to its page as `sync_wiki.subject_path` reads it for them. A reference on the row, such as a
    `uses` link, is no article, so a dependency through that declaration still reaches what it uses. A row an
    earlier sync wrote with only a module and a name (`sync_wiki.legacy_pair`) stands for the declaration the Lean
    index gives it (`sync_wiki.legacy_lean_name`), as for lean-facts; the index is read only when a page Autoform
    reads has such a row. Rows Autoform would read otherwise, or not at all (`sync_wiki.credit_problems`), and two
    pages standing for one declaration once such rows are resolved (`sync_wiki.owner_problems`), and credit over a held
    marker (`sync_wiki.held_conflicts`), raise ValueError: no article is left out unsaid."""

    from autoform_cli.graph import load_graph

    if __package__:
        from . import sync_wiki
    else:
        import sync_wiki

    files = {links: sync_wiki.read_rows(links.read_text(encoding="utf-8"))
             for links in sorted((BLUEPRINT / "links").glob("*.jsonl"))}
    problems = sync_wiki.credit_problems(files) + sync_wiki.pageless_rows(files)
    if problems:
        raise ValueError(f"{len(problems)} annotation problems, so no article manifest: " + "; ".join(problems[:20]))
    graph = load_graph(BLUEPRINT)
    pages = {Path(node.path).resolve() for node in graph.nodes.values() if Path(node.path).name != "README.md"}
    names, legacy = set(), []
    for rows in files.values():
        for row in rows:
            if sync_wiki.subject_path(row) not in pages:
                continue
            owner, name, _ = sync_wiki.page_owner(row)
            if owner == "atlas":
                names.add(name)
            elif owner == "none" and sync_wiki.legacy_pair(row) is not None:
                legacy.append(row["extensions"][sync_wiki.OWN])
    index = lean_index() if legacy else None
    problems = (sync_wiki.owner_problems(files, index) if legacy else []) + sync_wiki.held_conflicts(files, index)
    if problems:
        raise ValueError(f"{len(problems)} declarations with several pages or credit over a held marker, so no "
                         "article manifest: " + "; ".join(problems[:20]))
    if legacy:
        names |= {resolved for own in legacy if (resolved := sync_wiki.legacy_lean_name(own, index))}
    return names


def article_aliases() -> dict[str, str]:
    """The declarations the wiki's rows list as duplicates (`sync_wiki.duplicate_names`), each with the declaration
    its row credits: the same result stated again, with no page of its own, so that a use of one is a use of that
    article. The rows are read as the registry's consumers read them (`sync_wiki.listed_duplicates`), and a list
    `sync_wiki.duplicate_markers` refuses without the Lean index raises ValueError, as no use may be counted for an
    article it does not state. The rows are read without the index: a row an earlier sync wrote with only a module
    and a name has no `object`, so a list on it is refused, as one on a row whose declaration only the links folder's
    defaults give, and the declaration such a row stands for, which only the index gives, is among article_manifest's
    names, which resolve_aliases checks the aliases against; whether the Lean has each name is for the dump, and the
    Lean sources, to say."""

    if __package__:
        from . import sync_wiki
    else:
        import sync_wiki

    aliases, problems = sync_wiki.listed_duplicates({links: sync_wiki.read_rows(links.read_text(encoding="utf-8"))
                                                     for links in sorted((BLUEPRINT / "links").glob("*.jsonl"))})
    if problems:
        raise ValueError(f"{len(problems)} duplicates lists to fix, so no article manifest: "
                         + "; ".join(problems[:20]))
    return aliases


def private_collisions(rows: dict[str, dict], names: set[str]) -> dict[str, list[str]]:
    """The names of *names* that two or more private constants of the dump (*rows*) would be published as (see
    publish_private_targets), the dump having no public constant of that name, each with those constants: declarations
    of different modules that one source name cannot tell apart."""
    found: dict[str, list[str]] = {}
    for name, row in rows.items():
        prefix = f"_private.{row['module']}.0."
        if row.get("private") and name.startswith(prefix) and (public := name[len(prefix):]) in names \
                and public not in rows:
            found.setdefault(public, []).append(name)
    return {public: sorted(constants) for public, constants in found.items() if len(constants) > 1}


def resolve_aliases(listed: dict[str, str], manifest: set[str], rows: dict[str, dict], declared,
                    collisions: dict[str, list[str]] | None = None
                    ) -> tuple[dict[str, str | None], list[str], list[str]]:
    """The duplicates (*listed*, see article_aliases) the extraction and the Mathlib layer's bridge count, each with its
    article, or None for one whose article the Lean no longer declares: the way stops at it, and its uses count for no
    page; then what stops them, and what they warn about. Given the articles (*manifest*, see article_manifest), the
    dump's project rows (*rows*, a private one by its source name), *declared*, which says whether the Lean sources
    declare a name (None when nothing can tell), and *collisions* (see private_collisions), an error is: a page standing
    for a duplicate, as a row an earlier sync wrote with a module and a name can; an article not among the articles; a
    duplicate or an article that two private constants take; and one with no compiled row that the Lean declares, or
    for which nothing can tell, as the dump is then incomplete, whatever the other one is. A warning names a duplicate,
    or an article, or both, that the Lean no longer declares, with the other: the duplicate is then left out, as no
    constant uses it, or stops the way with no article. A Lean change that renames or deletes a declaration so fails no
    build, and the sync lists the stale entry for an editor (sync_wiki.stale_duplicates)."""
    collisions = collisions or {}
    alias: dict[str, str | None] = {}
    problems, warnings = [], []
    for name, article in sorted(listed.items()):
        about = f"the wiki lists {name} as a duplicate of {article}, but"
        if name in manifest:
            problems.append(f"{about} a page stands for {name}")
        elif article not in manifest:
            problems.append(f"{about} {article} is not among the articles, so a use of {name} could count for no page")
        elif shared := [one for one in (name, article) if one in collisions]:
            problems += [f"{about} the compiled dependency dump has several private constants named {one}, which one "
                         f"name cannot tell apart: {', '.join(collisions[one])}" for one in shared]
        elif not (missing := [one for one in (name, article) if one not in rows]):
            alias[name] = article
        elif incomplete := {one: source for one in missing if (source := declared(one)) is not False}:
            # Each end the dump lacks is judged on its own: one the Lean may still declare stops the build, whatever
            # the other end is.
            for one, source in incomplete.items():
                why = ("the Lean sources declare it" if source else
                       "nothing here tells whether the Lean still declares it")
                problems.append(f"{about} the compiled dependency dump has no row for {one}, and {why}: make the dump "
                                "again")
        elif len(missing) == 2:
            warnings.append(f"the Lean no longer declares {name}, which the wiki lists as a duplicate of {article}, "
                            f"nor {article}: the entry counts for nothing; drop it from the row's `duplicates`")
        elif missing == [name]:
            warnings.append(f"the Lean no longer declares {name}, which the wiki lists as a duplicate of {article}: "
                            "the entry counts for nothing; drop it from the row's `duplicates`")
        else:
            warnings.append(f"the Lean no longer declares {article}, whose page lists {name} as a duplicate: a use of "
                            f"{name} counts for no page; relink the page or drop the entry")
            alias[name] = None
    return alias, problems, warnings


def aliases_digest(aliases: dict[str, str]) -> str:
    """The digest of the duplicates the rows list, each with its article (article_aliases): each article, sorted, with
    its duplicates, sorted, as compact JSON with every character past ASCII escaped, which spells any lists one way
    only, whatever their strings hold (a tab, a line feed, a lone surrogate). These are the lists a registry records
    it was made for, which a consumer computes again from its checkout's rows (sync_wiki.registry_problems). A
    `duplicates` edit can change the bridges and leave the extraction as it was, so its digest cannot show it."""
    lists: dict[str, list[str]] = {}
    for name, article in aliases.items():
        lists.setdefault(article, []).append(name)
    encoded = json.dumps(sorted((article, sorted(names)) for article, names in lists.items()), separators=(",", ":"))
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()


def lean_index():
    """The Lean index of the project's sources, as lean-facts reads it."""
    from autoform_cli.lean import index_project

    return index_project(BLUEPRINT.parent, exclude_roots=("v1", "Atlas"))


def expression_uses(row: dict | None, statement: bool) -> list[str]:
    """The constants *row*'s expressions use: with *statement*, what it states (its type, and its value when that is
    part of what it states); otherwise everything, its type and its value."""
    if not row:
        return []
    if statement and row.get("kind") not in STATEMENT_VALUE:
        return row["type"]
    return row["type"] + row["value"]


def frontiers(rows: dict[str, dict], articles: set[str], statement: bool = False,
              direct=None, alias: dict[str, str | None] | None = None) -> dict[str, frozenset[str]]:
    """For every non-article constant, the articles reachable through non-articles.

    With *direct*, a function of a constant's name, the constants reached are instead what *direct* gives for
    each non-article on the way (the Mathlib declarations it names, say), and articles only stop the way.

    With *alias*, which maps a duplicate (see resolve_aliases) to its article, or to None when the article is gone, a
    duplicate stops the way, and a set lists the duplicate itself where the way reaches it: what it gives depends on
    whose way it is (see through_aliases). Each duplicate also gets the set its own uses reach, as a non-article.

    With *statement*, only what a constant states counts: its type, and its value only when that value is
    part of what it states (a definition's body, an inductive type's constructors). A hidden theorem's proof
    then reaches nothing, so an article whose statement uses that theorem depends on what the theorem says,
    not on how it is proved.

    Mutually recursive non-articles reach the same articles, so the non-article graph is first cut into
    strongly connected components (Tarjan's algorithm): a component is finished only after every
    component it uses, and all its members get the union of what any of them reaches. The result does not
    depend on the order in which the constants are visited.
    """

    def uses(name: str) -> list[str]:
        return expression_uses(rows.get(name), statement)

    alias = alias or {}
    memo: dict[str, frozenset[str]] = {}
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    for root in rows:
        if root in articles or root in alias or root in index:
            continue
        index[root] = low[root] = len(index)
        stack.append(root)
        on_stack.add(root)
        work = [(root, iter(uses(root)))]
        while work:
            node, children = work[-1]
            child = next(children, None)
            if child is not None:
                if child in articles or child in alias:
                    continue
                if child not in index:
                    index[child] = low[child] = len(index)
                    stack.append(child)
                    on_stack.add(child)
                    work.append((child, iter(uses(child))))
                elif child in on_stack:
                    low[node] = min(low[node], index[child])
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[node])
            if low[node] != index[node]:
                continue
            component: list[str] = []
            while True:
                member = stack.pop()
                on_stack.discard(member)
                component.append(member)
                if member == node:
                    break
            members = set(component)
            reached: set[str] = set()
            for member in component:
                if direct is not None:
                    reached |= set(direct(member))
                for use in uses(member):
                    if use in alias:
                        reached.add(use)
                    elif use in articles:
                        if direct is None:
                            reached.add(use)
                    elif use not in members:
                        reached |= memo[use]
            for member in component:
                memo[member] = frozenset(reached)
    # What each duplicate's own uses reach, for its own article, which it is part of (see through_aliases).
    for name in alias:
        if name in rows:
            reached = set(direct(name)) if direct is not None else set()
            for use in uses(name):
                if use in alias or (use in articles and direct is None):
                    reached.add(use)
                elif use not in articles:
                    reached |= memo.get(use, frozenset())
            memo[name] = frozenset(reached)
    return memo


def through_aliases(name: str, reached: frozenset[str], through: dict[str, frozenset[str]],
                    alias: dict[str, str | None], articles: bool = True) -> frozenset[str] | set[str]:
    """What *reached*, a set frontiers gives with *alias*, gives article *name*. A duplicate of another article stands
    for that article (with *articles*; for nothing otherwise, as articles then only stop the way), and one whose
    article is gone for nothing. One of *name*'s own is part of it, as a non-article: it stands for what it reaches
    itself, its set in *through*, each read once, so a cycle through it ends. The caller drops *name* itself."""
    if not alias or alias.keys().isdisjoint(reached):
        return reached
    found: set[str] = set()
    seen: set[str] = set()
    pending = [reached]
    while pending:
        for target in pending.pop():
            if target not in alias:
                found.add(target)
            elif (article := alias[target]) is None:
                continue
            elif article == name:
                if target not in seen:
                    seen.add(target)
                    pending.append(through.get(target, frozenset()))
            elif articles:
                found.add(article)
    return found


def own_duplicates(name: str, uses: list[str], rows: dict[str, dict], alias: dict[str, str | None],
                   statement: bool) -> tuple[list[str], list[str]]:
    """*uses*, an expression of article *name*, with each duplicate of *name*'s own it names (see resolve_aliases)
    replaced by what the duplicate uses (see expression_uses, with *statement*), each once; then the duplicates so
    replaced. A duplicate states its article's result, so what it names, the article names: for its own article it is
    no stop but part of the article. Another of *name*'s own that such a duplicate names stays among the uses, for the
    caller to follow as a hidden constant (see through_aliases): the article reaches what that one uses, but names
    none of it. A duplicate of another article stays in *uses*."""
    if not alias or name not in alias.values():
        return uses, []
    kept: list[str] = []
    replaced: list[str] = []
    for use in uses:
        if use not in alias or alias[use] != name:
            kept.append(use)
        elif use not in replaced:
            replaced.append(use)
            kept.extend(expression_uses(rows.get(use), statement))
    return kept, replaced


def mutual_groups(edges: dict[str, set[str]]) -> list[list[str]]:
    """The groups of two or more articles whose statement edges reach each other (Tarjan's algorithm)."""
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    groups: list[list[str]] = []
    for root in sorted(edges):
        if root in index:
            continue
        work = [(root, iter(sorted(edges[root])))]
        index[root] = low[root] = len(index)
        stack.append(root)
        on_stack.add(root)
        while work:
            node, children = work[-1]
            child = next(children, None)
            if child is not None:
                if child not in index:
                    index[child] = low[child] = len(index)
                    stack.append(child)
                    on_stack.add(child)
                    work.append((child, iter(sorted(edges.get(child, ())))))
                elif child in on_stack:
                    low[node] = min(low[node], index[child])
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[node])
            if low[node] == index[node]:
                group = []
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    group.append(member)
                    if member == node:
                        break
                if len(group) > 1:
                    groups.append(sorted(group))
    return sorted(groups)


# The kind lean-facts writes for a credited Mathlib declaration, from the dump's compiled kind.
MATHLIB_KINDS = {"theorem": "theorem", "def": "def", "axiom": "axiom", "opaque": "opaque", "inductive": "inductive"}


def mathlib_kind(row: dict) -> str:
    if row.get("class"):
        return "class"
    if row.get("structure"):
        return "structure"
    return MATHLIB_KINDS.get(row.get("kind", ""), row.get("kind", ""))


def registry(rows: dict[str, dict], articles: set[str], registered: dict[str, dict],
             alias: dict[str, str | None] | None = None) -> dict:
    """The bridge and Mathlib edges of the credited Mathlib declarations; see the module docstring. A row's
    `mathlib_type` and `mathlib_state` (a definition's body, an inductive type's constructors) list the credited
    declarations what it states reaches, `mathlib_value` those everything it uses reaches, and
    `mathlib_type_direct` and `mathlib_value_direct` those its type and its value name themselves. An article's
    bridge's kind is decided first, a statement one when the statement reaches the declaration at all, and the bridge
    is kept only when the statement, or the proof, names the declaration itself; the others are listed apart
    (`left_out`), by kind. A duplicate (*alias*, see frontiers) stops any other article's way as its article does, so
    that no article reaches through it what its article's own edges give, nor, its article gone, what it reaches
    itself. For its own article it is part of the article (see own_duplicates): what it reaches, the article reaches,
    and what it names, where the article names the duplicate itself, the article names, so that it bridges too; one
    the article reaches otherwise, through a hidden constant or through another duplicate, gives only what is left
    out, as a hidden constant does."""
    alias = alias or {}
    found = {name: row for name, row in registered.items() if not row.get("missing")}

    def direct(name: str, statement: bool, table: dict[str, dict] = rows) -> list[str]:
        row = table.get(name) or {}
        if statement:
            return row.get("mathlib_type", []) + (row.get("mathlib_state", []) if row.get("kind") in STATEMENT_VALUE
                                                 else [])
        # A proof that passes through a constant reaches everything it uses: its type as much as its value.
        return row.get("mathlib_type_used", []) + row.get("mathlib_value", [])

    through_statement = frontiers(rows, articles, statement=True, direct=lambda name: direct(name, True), alias=alias)
    through = frontiers(rows, articles, direct=lambda name: direct(name, False), alias=alias)

    def names(name: str, statement: bool) -> list[str]:
        # What a constant's expressions name themselves: those it states, or all it uses (see expression_uses).
        row = rows.get(name) or {}
        if statement and row.get("kind") not in STATEMENT_VALUE:
            return row.get("mathlib_type_direct", [])
        return row.get("mathlib_type_direct", []) + row.get("mathlib_value_direct", [])

    def collapse(name: str, uses: list[str], own: list[str], named: list[str], memo: dict[str, frozenset[str]],
                 statement: bool) -> tuple[set[str], set[str]]:
        # What article *name*'s expression *uses* reaches, given what it reaches through Mathlib itself (*own*), and
        # what it names, given the names it has (*named*), with those of the duplicates of its own it names itself.
        kept, duplicates = own_duplicates(name, uses, rows, alias, statement)
        reached, naming = set(own), set(named)
        for duplicate in duplicates:
            reached |= set(direct(duplicate, statement))
            naming |= set(names(duplicate, statement))
        for use in kept:
            # Another article stops the way, and so does its duplicate; one of the article's own that a duplicate it
            # names names is followed as a hidden constant.
            if use not in articles and (use not in alias or alias[use] == name):
                reached |= through_aliases(name, memo.get(use, frozenset()), memo, alias, articles=False)
        return reached & found.keys(), naming

    bridges, left_out = {}, {}
    for name in sorted(articles):
        row = rows[name]
        if row["kind"] in STATEMENT_VALUE:
            # A definition's body and an inductive type's constructors are part of what it states.
            statement, stated = collapse(name, row["type"] + row["value"], direct(name, True),
                                         row["mathlib_type_direct"] + row["mathlib_value_direct"], through_statement,
                                         True)
            proof, proved = set(), set()
        else:
            statement, stated = collapse(name, row["type"], row.get("mathlib_type", []), row["mathlib_type_direct"],
                                         through_statement, True)
            proof, proved = collapse(name, row["value"], row.get("mathlib_value", []), row["mathlib_value_direct"],
                                     through, False)
            proof -= statement
        # A statement or a proof bridges only to what it names itself; what it reaches only through other constants,
        # the project's or Mathlib's, gives no edge.
        kept = {"statement": statement & stated, "proof": proof & proved}
        dropped = {"statement": statement - kept["statement"], "proof": proof - kept["proof"]}
        if kept["statement"] or kept["proof"]:
            bridges[name] = {kind: sorted(kept[kind]) for kind in ("statement", "proof")}
        if dropped["statement"] or dropped["proof"]:
            left_out[name] = {kind: sorted(dropped[kind]) for kind in ("statement", "proof")}
    mathlib = {}
    for name, row in sorted(found.items()):
        statement = set(direct(name, True, found)) & found.keys()
        # As for an article, a definition's or an inductive type's value is part of its statement: no proof edges.
        proof = set() if row.get("kind") in STATEMENT_VALUE else (set(row.get("mathlib_value", [])) & found.keys())
        proof -= statement
        statement.discard(name)
        proof.discard(name)
        mathlib[name] = {"module": row["module"], "kind": mathlib_kind(row),
                         "proposition": row["proposition"], "statement": sorted(statement),
                         "proof": sorted(proof)}
    groups = mutual_groups({name: set(entry["statement"]) for name, entry in mathlib.items()})
    for group in groups:
        for name in group:
            mathlib[name]["statement"] = [use for use in mathlib[name]["statement"] if use not in group]
    return {"bridges": bridges, "left_out": left_out, "mathlib": mathlib, "mutual": groups,
            "missing": sorted(name for name, row in registered.items() if row.get("missing")),
            "project": sorted(name for name, row in registered.items() if row.get("missing") and row.get("project")),
            # Missing names whose row named no module: the dump looked for them only in the modules it imported.
            "unplaced": sorted(name for name, row in registered.items()
                               if row.get("missing") and not row.get("project") and not row.get("module_given"))}


def main() -> int:
    args = sys.argv[1:]
    options: dict[str, str] = {}
    for flag in ("--registry", "--names"):
        if flag in args:
            at = args.index(flag)
            if at + 1 >= len(args):
                args = []
                break
            options[flag] = args[at + 1]
            args = args[:at] + args[at + 2:]
    if len(args) != 2 or ("--registry" in options) != ("--names" in options):
        print(__doc__.strip(), file=sys.stderr)
        return 2
    registry_output = Path(options["--registry"]) if "--registry" in options else None
    names_file = Path(options["--names"]) if "--names" in options else None
    # Each file its own, and each output a file of its own: one that is the other output or an input, by its path,
    # through a symbolic link or as a hard link, would overwrite it, and one that is a symbolic link would be replaced.
    files = {"DUMP": Path(args[0]), "OUTPUT.json": Path(args[1]), "REGISTRY.json": registry_output, "NAMES": names_file}
    files = {label: path for label, path in files.items() if path is not None}
    if problem := file_problem(files, tuple(label for label in ("OUTPUT.json", "REGISTRY.json") if label in files)):
        print(f"error: {problem}", file=sys.stderr)
        return 2
    try:
        manifest = article_manifest()
        listed = article_aliases()
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    try:
        project_rows, registered, framing = read_dump(Path(args[0]), framed=names_file is not None)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    if names_file is not None:
        # Only a dump that says it follows the registry's rules, at this checkout's Mathlib, and that is whole.
        header, end = framing["header"], framing["end"]
        if {key: header.get(key) for key in DUMP_FORMAT} != DUMP_FORMAT or type(header["format"]) is not int:
            print(f"error: {args[0]} is not a dump made with a names list in the current format; make it again "
                  "with scripts/dump_v2_dependencies.lean and the list", file=sys.stderr)
            return 1
        if header.get("mathlib_rev") != mathlib_revision():
            print(f"error: the dump was made at Mathlib {header.get('mathlib_rev')}, but this checkout pins "
                  f"{mathlib_revision()}", file=sys.stderr)
            return 1
        counts = (end.get("rows"), end.get("names"), header.get("names"))
        if end["end"] is not True or any(type(count) is not int for count in counts) or \
                counts != (len(project_rows), len(registered), len(registered)):
            print(f"error: {args[0]} is cut or mixed: its footer does not close it with the counts of its rows",
                  file=sys.stderr)
            return 1
        # The registry speaks for exactly the names the wiki credits: a name without its row, or a row for a
        # name not asked for, means the dump was made from another list.
        requested = read_names(names_file)
        if sorted(set(requested)) != sorted(requested) or set(requested) != registered.keys():
            unanswered, unasked = sorted(set(requested) - registered.keys()), sorted(registered.keys() - set(requested))
            print(f"error: the dump answers another list of credited names than {names_file} (without a row: "
                  f"{unanswered[:5]}; not asked for: {unasked[:5]}); it must be made with that list", file=sys.stderr)
            return 1
        problems = registered_problems(registered, set(project_rows), given_modules(names_file))
        if problems:
            for problem in problems[:10]:
                print(f"error: {problem}", file=sys.stderr)
            print(f"error: {len(problems)} problems in the rows {args[0]} has for credited names; make it again with "
                  "scripts/dump_v2_dependencies.lean and the list", file=sys.stderr)
            return 1
        # Every project row as the current format writes it, checked before either output is written.
        problems = row_problems(project_rows, {name for name, row in registered.items() if "missing" not in row})
        if problems:
            for problem in problems[:10]:
                print(f"error: {problem}", file=sys.stderr)
            print(f"error: {len(problems)} problems in the rows of {args[0]}, which are not all in the current "
                  "format; make it again with scripts/dump_v2_dependencies.lean and the list", file=sys.stderr)
            return 1
    # A private duplicate or article is published by its source name only when one constant has it.
    collisions = private_collisions(project_rows, listed.keys() | set(listed.values()))
    # The credited Mathlib declarations' rows serve only the registry: OUTPUT.json is the same without them.
    rows = publish_private_targets(project_rows, manifest | listed.keys())
    sources = functools.cache(lean_index)
    missing = manifest - rows.keys()
    if any("«" in name for name in missing):
        try:
            rows = join_missing_quoted_articles(rows, missing, manifest, listed, registered, sources)
        except ValueError as error:
            print(f"error: {error}", file=sys.stderr)
            return 1
        except OSError as error:
            from autoform_cli.lean import index_failure_message

            print(f"error: {index_failure_message(error)}", file=sys.stderr)
            return 1
        missing -= rows.keys()
    # A use of a duplicate counts as a use of its article, which only the compiled rows of both can show; the Lean
    # sources, read only for a row the dump lacks, tell a deleted declaration from an incomplete dump.
    alias, problems, warnings = resolve_aliases(listed, manifest, rows, lambda name: name in sources().declarations,
                                                collisions)
    for warning in warnings:
        print(f"warning: {warning}", file=sys.stderr)
    if problems:
        for problem in problems[:20]:
            print(f"error: {problem}", file=sys.stderr)
        print(f"error: {len(problems)} declarations listed as duplicates whose uses could not count as uses of their "
              "articles; make the dump again, or fix the lists", file=sys.stderr)
        return 1
    missing = sorted(missing)
    if missing:
        for name in missing[:20]:
            print(f"warning: roadmap Lean target is absent from the compiled dependency dump: {name}", file=sys.stderr)
        print(f"warning: {len(missing)} roadmap targets have no compiled dependency row", file=sys.stderr)
    articles = manifest & rows.keys()
    # Statements reach through what hidden constants state; proofs through everything they use.
    reach_statement = frontiers(rows, articles, statement=True, alias=alias)
    reach = frontiers(rows, articles, alias=alias)

    def collapse(name: str, uses: list[str], through: dict[str, frozenset[str]], statement: bool) -> set[str]:
        found: set[str] = set()
        # The article's own duplicates are part of it: what they use, it uses.
        for use in own_duplicates(name, uses, rows, alias, statement)[0]:
            if use in alias and alias[use] != name:
                # A duplicate of another article stands for that article; one whose article is gone, for none.
                found |= {alias[use]} - {None}
            elif use in articles:
                found.add(use)
            else:
                # A hidden constant, or one of the article's own duplicates that a duplicate it names names.
                found |= through_aliases(name, through.get(use, frozenset()), through, alias)
        found.discard(name)
        return found

    result = {}
    for name in sorted(articles):
        row = rows[name]
        if row["kind"] in STATEMENT_VALUE:
            statement, proof = collapse(name, row["type"] + row["value"], reach_statement, True), set()
        else:
            statement = collapse(name, row["type"], reach_statement, True)
            proof = collapse(name, row["value"], reach, False) - statement
        result[name] = {
            "module": row["module"],
            "statement": sorted(statement),
            "proof": sorted(proof),
        }
    groups = mutual_groups({name: set(entry["statement"]) for name, entry in result.items()})
    for group in groups:
        for name in group:
            result[name]["statement"] = [use for use in result[name]["statement"] if use not in group]
    output = Path(args[1])
    # A target with no compiled row has no module to name its library, so its own name has to. A name outside
    # the libraries' namespaces (`CategoryTheory.foo`) is kept under UNPREFIXED, so `lean-facts` still sees it.
    missing_by_library = {
        library: [name for name in missing if name.split(".")[0] == library]
        for library in sorted(LIBRARIES)
    }
    unplaced = [name for name in missing if name.split(".")[0] not in LIBRARIES]
    missing_by_library[UNPREFIXED] = unplaced
    if unplaced:
        print(f"warning: {len(unplaced)} targets without a compiled row name no library: {unplaced[:5]}", file=sys.stderr)
    outputs = {output: json.dumps({"missing_articles": missing_by_library, "mutual": groups, "articles": result},
                                  ensure_ascii=False, sort_keys=True) + "\n"}
    found = None
    if registry_output is not None:
        found = registry(rows, articles, registered, alias)
        found["inputs"] = {"names_sha256": names_digest(read_names(names_file)),
                           "dump_sha256": file_digest(Path(args[0])), "aliases_sha256": aliases_digest(listed),
                           "mathlib_rev": mathlib_revision(),
                           "requested": len(registered), "format": REGISTRY_FORMAT,
                           "extraction_sha256": hashlib.sha256(outputs[output].encode("utf-8")).hexdigest()}
        outputs[registry_output] = json.dumps(found, ensure_ascii=False, sort_keys=True) + "\n"
    # Both made, then both written: a failure above leaves neither, and so does one while writing.
    try:
        write_whole(outputs)
    except UndoError as error:
        print(f"error: {error}; putting the earlier outputs back failed too, so they may be new and old mixed: their "
              "earlier bytes are kept in " + ", ".join(f"{copy} (for {path})" for path, copy in error.kept.items()),
              file=sys.stderr)
        return 1
    except OSError as error:
        print(f"error: {error}; the outputs are as they were", file=sys.stderr)
        return 1
    if found is not None:
        for name in found["missing"]:
            why = "a declaration of this project" if name in found["project"] else \
                "not a constant of a Mathlib module the build imports"
            print(f"warning: the wiki credits the Mathlib declaration {name}, which is {why}", file=sys.stderr)
        def tally(table: str, kind: str) -> int:
            return sum(len(entry[kind]) for entry in found[table].values())

        print(f"{len(found['mathlib'])} credited Mathlib declarations, {len(found['missing'])} missing, "
              f"{tally('bridges', 'statement') + tally('bridges', 'proof')} bridge edges "
              f"({tally('bridges', 'statement')} statement, {tally('bridges', 'proof')} proof), "
              f"{tally('left_out', 'statement') + tally('left_out', 'proof')} more reached only through other "
              f"constants left out ({tally('left_out', 'statement')} statement, {tally('left_out', 'proof')} proof), "
              f"{sum(len(e['statement']) + len(e['proof']) for e in found['mathlib'].values())} Mathlib edges "
              f"-> {registry_output}")
    edges = sum(len(entry["statement"]) + len(entry["proof"]) for entry in result.values())
    print(
        f"{len(rows)} constants, {len(articles)} compiled articles, {len(missing)} without a compiled row, "
        f"{edges} article edges -> {output}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
