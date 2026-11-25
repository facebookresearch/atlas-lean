#!/usr/bin/env python3
"""Lay out ATLAS wiki pages from the Lean sources: the library scripts/sync_wiki.py imports.

ATLAS v2 is the root Lake package: every public MathlibExt, CSLibExt,
PhyslibExt, Domains and WantedExt declaration with a docstring becomes one article whose
statement is that docstring. Theorems are proved and definitions defined unless their
module contains `sorry`; `theorem_wanted` entries are stated results waiting
for a proof, and `def_wanted` entries stay unstated, because Autoform counts a
stated definition as defined.

scripts/taxonomy.json is the wiki's editorial structure: its regions, the
subjects inside them, each subject's fields and subfields, and where each Lean
module or directory sits among them, under what title. Lean paths do not decide
where an article appears.

The wiki's pages are committed: sync_wiki.py seeded them once from generate()
and adds pages for new declarations, and nothing here writes a file.
"""

from __future__ import annotations

import json
import re
import sys
import textwrap
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

from autoform_cli.lean import index_project
from autoform_cli.markdown import article_parts, link_targets, outside_fences
from autoform_cli.status import DEFINITION_DECLARATIONS

ROOT = Path(__file__).resolve().parent.parent
VAULT = ROOT / "blueprint"
ROADMAP = VAULT / "roadmap"
SOURCES = VAULT / "sources"
PAGE_MAP = VAULT / "pages.json"
MAX_CHILDREN = 20  # `autoform audit` reports containers above 24.
# A `navigation: module` page may hold as many articles as the explorer maps.
MAX_MODULE_CHILDREN = 120
# Headings with a meaning on Autoform pages; a module section never takes one.
RESERVED_HEADINGS = {"contents", "depends on", "mathematical overview", "proof depends on", "sources"}
# The words around internal ids in a citation that names no work: "concept `jis_sem_…`; source statements `jis_…`".
ID_WORDS = {"and", "block", "clause", "concept", "from", "frozen", "lines", "required", "source", "sources", "statement", "statements"}

TAXONOMY = ROOT / "scripts" / "taxonomy.json"
TAXONOMY_SCHEMA = "atlas-wiki-taxonomy/v1"
# Where a module the taxonomy does not place yet appears, so it is visible until someone places it.
UNPLACED = {
    "slug": "not-yet-classified",
    "title": "Not yet classified",
    "description": "Topics added since this subject's fields were last revised.",
    "subfields": [],
}

# Library -> top-level directory -> subject when the names differ. The taxonomy places
# almost every module; these subjects hold only the modules it does not place yet.
LIBRARIES = {
    "MathlibExt": {
        "AlgebraicTopology": "Topology",
        "Algorithms": "ComputerScience",
        "Complexity": "TheoryOfComputation",
        "Computability": "TheoryOfComputation",
        "ControlTheory": "Analysis",
        "Data": "ComputerScience",
        "Interpolation": "Analysis",
        "Languages": "ComputerScience",
        "ModelTheory": "Logic",
        "Quantum": "QuantumInformation",
    },
    "CSLibExt": {
        "Algorithms": "ComputerScience",
        "AutomatedReasoning": "Logic",
        "Bioinformatics": "Biology",
        "Coding": "InformationTheory",
        "Complexity": "TheoryOfComputation",
        "Computability": "TheoryOfComputation",
        "Crypto": "ComputerScience",
        "Databases": "ComputerScience",
        "Foundations": "ComputerScience",
        "InformationRetrieval": "ComputerScience",
        "Languages": "ComputerScience",
        "Logics": "Logic",
        "MachineLearning": "ComputerScience",
        "Parallel": "ComputerScience",
        "Planning": "ComputerScience",
        "Privacy": "ComputerScience",
        "Security": "ComputerScience",
        "Specs": "ComputerScience",
        "Tactic": "ComputerScience",
        "Testing": "ComputerScience",
    },
    "PhyslibExt": {
        "Basic": "Physics",
        "Biomechanics": "Physics",
        "BiomedicalImaging": "Physics",
        "Biophysics": "Physics",
        "Circuits": "Physics",
        "ClassicalMechanics": "Physics",
        "CondensedMatter": "StatisticalMechanics",
        "Elasticity": "Physics",
        "Electromagnetism": "Physics",
        "Electronics": "Physics",
        "Engineering": "Physics",
        "FluidDynamics": "Physics",
        "HeatTransfer": "Physics",
        "Instrumentation": "Physics",
        "Mechanics": "Physics",
        "Numerical": "Physics",
        "Quantum": "Physics",
        "QuantumMechanics": "Physics",
        "Reliability": "Physics",
        "SpaceAndTime": "Physics",
        "SpaceSystems": "Physics",
        "StatisticalMechanics": "StatisticalMechanics",
        "Statistics": "Physics",
        "Units": "Physics",
    },
    "Domains": {"MaterialsScience": "Physics", "OperationsResearch": "Economics",
                "Transport": "Economics", "Urban": "Economics"},
    "WantedExt": {"Complexity": "TheoryOfComputation", "Computation": "TheoryOfComputation", "ModelTheory": "Logic"},
}
# Declarations inside a `mutual` block are indented; `declaration_lines` takes indented matches only there, or
# where the Lean index puts a declaration.
V2_DECLARATION = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe|public|nonrec|scoped)\s+)*)"
    r"(?P<kw>theorem_wanted|def_wanted|theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\b"
    r"\s*(?P<name>[^\s:(\[{]*)"
)
WANTED = {"theorem_wanted": "theorem", "def_wanted": "def"}
# A bold name may hold a lone asterisk, as in "A\* search" or "$c_0^*$"; it ends at the first "**".
BOLD_TITLE = re.compile(r"^\*\*(?P<title>(?:[^*]|\*(?!\*))+)\*\*")
ARTICLE_ID = re.compile(r"^article_id: (af_[0-9a-f]{24})$", re.M)
COMMENT_DELIMITER = re.compile(r"/-|-/")
LINK_SYNTAX = re.compile(r"\[([^\]\n]*)\]\(([^)\n]*)\)")
LINK_TARGET = re.compile(r"(?:[a-z][a-z0-9+.-]*:|#)\S*|[^\s()]+\.(?:md|html)(?:#\S*)?")
MATH_SPAN = re.compile(
    r"(?s)(?<!\\)(?P<dollars>\${1,2}).*?(?<!\\)(?P=dollars)|\\\(.*?\\\)|\\\[.*?\\\]"
)
# Arithmatex renders $$...$$ as display math only when it is a paragraph of its own;
# a formula on lines of its own gets one.
DISPLAY_MATH = re.compile(r"\s*^[ \t]*(\$\$(?:\\.|(?!\$\$)[^\\])+?\$\$)[ \t]*$\s*", re.M | re.S)


@dataclass
class Target:
    book: str
    idx: int
    title: str
    slug: str
    location: str
    description: str
    declaration: str
    lean: str | None
    statement: bool
    proof: bool
    names: list[str]
    citations: list[str] = field(default_factory=list)
    module: tuple[str, ...] = ()
    # The `# ` heading of the module docstring, if any.
    module_title: str = ""
    # The doc heading, named section and namespace the declaration sits under.
    sections: tuple[str, str, str] = ("", "", "")
    path: Path = Path()
    # The 1-based line of the declaration in its module, 0 when unknown.
    line: int = 0
    depends: list[Target] = field(default_factory=list)
    proof_depends: list[Target] = field(default_factory=list)


@dataclass
class Container:
    title: str
    slug: str
    children: list[Container | Target]
    prose: str = ""
    path: Path = Path()
    navigation: str | None = None
    # One section title per child, for a module page whose source has sections.
    groups: list[str] | None = None


# MkDocs serves a folder's README.md as its index.md, and a case-insensitive disk
# holds readme.md and README.md as one file, so no page takes either name.
RESERVED_SLUGS = frozenset({"index", "readme"})


def slugify(text: str, limit: int = 48) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    return slug[:limit].rstrip("-") or "untitled"


def link_text(text: str) -> str:
    return text.replace("[", "\\[").replace("]", "\\]")


def chunk(title: str, slug: str, children: list, ranges: bool = True) -> Container:
    """Nest children under parts so that no container exceeds MAX_CHILDREN.

    A part is named by its first and last child, from one to the other; a list
    in dependency order names its parts by number, since such a name would read
    as a range of titles.
    """
    if len(children) <= MAX_CHILDREN:
        return Container(title, slug, children)
    size = MAX_CHILDREN
    while -(-len(children) // size) > MAX_CHILDREN:
        size *= MAX_CHILDREN
    parts = [children[start : start + size] for start in range(0, len(children), size)]
    nested = []
    for number, part in enumerate(parts, 1):
        if len(part) > 1 and ranges:
            name = f"{part[0].title} to {part[-1].title}"
        else:
            name = f"Part {number} of {len(parts)}"
        page = chunk(name, f"part-{number:02d}", part, ranges)
        page.navigation = "transparent"
        nested.append(page)
    return Container(title, slug, nested)


def safe_math_markdown(text: str) -> str:
    """Keep TeX comparisons from opening raw-HTML tags inside site cards, and plain-text
    math that reads as Markdown link syntax, such as [x^{λ+δ}](a_δ f), from becoming a link."""

    out, at = [], 0
    for span in MATH_SPAN.finditer(text):
        out += [not_a_link(text[at : span.start()]), re.sub(r"<(?=[A-Za-z_\\])", r"\\lt ", span.group())]
        at = span.end()
    return "".join(out) + not_a_link(text[at:])


def not_a_link(text: str) -> str:
    """Keep [text](target) a link only when the target is a URL, a fragment or a page. A backslash
    can't escape it: \\[ and \\( open math here, so the parenthesis becomes an entity."""
    return LINK_SYNTAX.sub(lambda m: m.group() if LINK_TARGET.fullmatch(m.group(2)) else f"[{m.group(1)}]&#40;{m.group(2)})", text)


# Where something other than code may start: a block comment, a line comment, a string, a character, a raw string.
_LEXEME = re.compile(r'/-|--|"|\'|(?<![\w\'!?])r#*"')
# The same, with the braces that open and close a term embedded in an interpolated string.
_LEXEME_IN_TERM = re.compile(r'/-|--|"|\'|(?<![\w\'!?])r#*"|[{}]')
_STRING_TAIL = re.compile(r'(?:[^"\\]|\\.)*"', re.S)
_CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\\n'])'")
_BLOCK = re.compile(r"/-|-/")
# The tokens after which a string is interpolated, as Lean's grammar has them: `s!`, `m!` and `f!`, and
# `throwError`, `throwErrorAt <term>`, `dbg_trace` and `trace[...]`; whitespace and comments may separate them
# from the string. Other `name!` macros, such as `panic!`, take an ordinary string.
_INTERPOLATING = re.compile(
    r"(?<![\w'.!?])(?:[smf]!|throwError|dbg_trace|trace\[[^\]\n]*\]|throwErrorAt\s+(?:[^\s()\"]+|\([^()]*\)))\s*$")


def _blank(text: str) -> str:
    return re.sub(r"[^\n]", " ", text)


def code_only(text: str) -> str:
    """The Lean source with every comment and literal blanked out, keeping its lines and columns.

    It reads the source as Lean's lexer does: block comments nest, so a docstring that shows a documented
    example stays one comment; a line comment runs to the end of its line; string literals, raw strings and
    character literals may span lines and hide comment markers and declaration-looking text; a prime that
    ends a name (`h'`) starts no character literal; and the terms embedded in an interpolated string
    (`s!"…{term}…"`) are code, which stays, with their own strings and braces.
    """
    out: list[str] = []
    n = len(text)

    def read_so_far(significant: int = 1000) -> str:
        # What is read so far, back to `significant` characters that are not blank, with each blank run (blanked
        # comments included) shortened to one space: trivia of any length keeps the tokens before a string.
        pieces, count = [], 0
        for piece in reversed(out):
            pieces.append(piece)
            count += len(piece) - piece.count(" ") - piece.count("\n") - piece.count("\t")
            if count >= significant:
                break
        return re.sub(r"\s+", " ", "".join(reversed(pieces)))

    def code(i: int, in_term: bool) -> int:
        # Code from i: to the end, or, in a term embedded in a string, past the brace that closes it.
        depth = 0
        lexemes = _LEXEME_IN_TERM if in_term else _LEXEME
        while i < n:
            match = lexemes.search(text, i)
            if match is None:
                out.append(text[i:])
                return n
            start, lexeme = match.start(), match.group()
            out.append(text[i:start])
            if lexeme in "{}":
                out.append(lexeme)
                if lexeme == "}":
                    if depth == 0:
                        return start + 1
                    depth -= 1
                else:
                    depth += 1
                i = start + 1
                continue
            if lexeme == "/-":
                count, end = 1, n
                for mark in _BLOCK.finditer(text, start + 2):
                    count += 1 if mark.group() == "/-" else -1
                    if count == 0:
                        end = mark.end()
                        break
            elif lexeme == "--":
                end = text.find("\n", start)
                end = n if end < 0 else end
            elif lexeme == '"':
                if _INTERPOLATING.search(read_so_far()):
                    i = interpolated(start)
                    continue
                tail = _STRING_TAIL.match(text, start + 1)
                end = tail.end() if tail else n
            elif lexeme == "'":
                char = None if start and (text[start - 1].isalnum() or text[start - 1] in "_'!?") else _CHAR.match(text, start)
                if char is None:
                    out.append("'")
                    i = start + 1
                    continue
                end = char.end()
            else:  # a raw string, r"..." or r#"..."# with as many closing hashes as opening ones
                close = '"' + "#" * (len(lexeme) - 2)
                end = text.find(close, match.end())
                end = n if end < 0 else end + len(close)
            out.append(_blank(text[start:end]))
            i = end
        return n

    def interpolated(start: int) -> int:
        # An interpolated string from its opening quote: its text is blanked, its embedded terms are code.
        i = segment = start + 1
        out.append(" ")
        while i < n:
            c = text[i]
            if c == "\\":
                i += 2
            elif c == '"':
                out.append(_blank(text[segment:i + 1]))
                return i + 1
            elif c == "{":
                out.append(_blank(text[segment:i]) + "{")
                i = segment = code(i + 1, True)
            else:
                i += 1
        out.append(_blank(text[segment:n]))
        return n

    code(0, False)
    return "".join(out)


def without_comments(text: str) -> str:
    """The Lean source without its comments and literals (blanked, so that no two tokens join)."""
    return code_only(text)


def code_lines(lines: list[str]) -> list[str]:
    """The lines with every comment and literal blanked out (see code_only), keeping their number and columns."""
    return code_only("\n".join(lines)).split("\n")


def attribute_opening(lines: list[str], end: int) -> int | None:
    """The line where the attribute `@[...]` that closes on line `end` opens, when it spans several lines.

    A multi-line attribute, such as `@[to_additive` followed by the additive declaration's own docstring and
    a closing `]`, sits between a declaration and its docstring. Its brackets balance only at its first line,
    which starts with `@[`; a line whose brackets balance without that start ends something else.
    """
    if not lines[end].rstrip().endswith("]"):
        return None
    depth = 0
    for start in range(end, -1, -1):
        depth += lines[start].count("]") - lines[start].count("[")
        if depth <= 0:
            return start if depth == 0 and lines[start].lstrip().startswith("@[") else None
    return None


def docstring_before(lines: list[str], number: int) -> str | None:
    """The `/-- ... -/` docstring attached to the declaration on line `number`.

    Only the comment that closes just above the declaration counts, found by
    matching nested `/-` and `-/` as Lean does: a `/-!` heading or a plain
    comment there means the declaration has no docstring, and the search must
    not run past it to an earlier docstring.
    """
    end = number - 1
    while end >= 0:
        if not lines[end].strip() or lines[end].lstrip().startswith("@["):
            end -= 1
            continue
        opening = attribute_opening(lines, end)
        if opening is None:
            break
        end = opening - 1
    if end < 0 or not lines[end].rstrip().endswith("-/"):
        return None
    depth = 0
    for start in range(end, -1, -1):
        for match in reversed(list(COMMENT_DELIMITER.finditer(lines[start]))):
            depth += 1 if match.group() == "-/" else -1
            if depth == 0:
                if not lines[start].startswith("/--", match.start()):
                    return None
                block = "\n".join(lines[start : end + 1])
                return textwrap.dedent(block[match.start() + 3 : block.rindex("-/")]).strip() or None
    return None


def humanize(name: str) -> str:
    text = " ".join(re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", name.replace("_", " ")).split())
    return text[:1].upper() + text[1:]


def topic_title(name: str) -> str:
    """Implementation workflow suffixes are provenance, not mathematical titles."""
    return humanize(name.removesuffix("Wanted"))


def load_taxonomy() -> dict:
    taxonomy = json.loads(TAXONOMY.read_text(encoding="utf-8"))
    if taxonomy.get("schema") != TAXONOMY_SCHEMA:
        raise SystemExit(f"{TAXONOMY.relative_to(ROOT)}: expected schema {TAXONOMY_SCHEMA}")
    return taxonomy


def placement(module: tuple[str, ...], placements: dict) -> tuple[str, dict] | None:
    """The taxonomy entry for a module: its own, else that of its nearest placed directory."""
    for end in range(len(module), 0, -1):
        key = "/".join(module[:end])
        if key in placements:
            return key, placements[key]
    return None


def names_a_work(citation: str) -> bool:
    """Whether a citation says more than internal ids such as concept `jis_sem_…`, which name no work a reader can find."""
    if not re.search(r"`[^`]*\bjis_\w+`", citation):
        return True
    words = re.findall(r"[A-Za-z]{3,}", re.sub(r"`[^`]*`", " ", citation))
    return any(word.lower() not in ID_WORDS for word in words)


def split_docstring(doc: str) -> tuple[str, list[str]]:
    """Separate the mathematical statement from its citations and Lean-side notes."""
    statement, citations = [], []
    for paragraph in re.split(r"\n\s*\n", doc):
        if re.match(r"(?i)proves `?wanted`? entr", paragraph.strip()):
            continue
        cite = re.search(r"(?m)^Sources?:\s*", paragraph)
        if cite:
            statement.append(paragraph[: cite.start()].strip())
            citation = " ".join(paragraph[cite.end() :].split())
            if names_a_work(citation):
                citations.append(citation)
        else:
            statement.append(paragraph.strip())
    text = "\n\n".join(part for part in statement if part)
    return (text, citations) if text else (doc, [])


def first_words(text: str, limit: int = 60) -> str:
    sentence = re.split(r"(?<=[.!?])\s", " ".join(text.split()), maxsplit=1)[0].rstrip(".")
    return sentence if len(sentence) <= limit else sentence[:limit].rsplit(" ", 1)[0] + "..."


_MODULE_HEADER = re.compile(r"^\s*module\s*$")
_SCOPE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:public|private|noncomputable|meta)\s+)*)(?P<kind>section|namespace|mutual|end)\b"
    r"[ \t]*(?P<name>(?:«[^»\n]*»|[^\s«])*)")


def name_components(name: str) -> list[str] | None:
    """The components of a dotted Lean name, a quoted one («…») kept whole with its quotes; None if a quote is
    left open."""
    components, current, quoted = [], "", False
    for char in name:
        if char == "«":
            quoted = True
        elif char == "»":
            quoted = False
        if char == "." and not quoted:
            components.append(current)
            current = ""
        else:
            current += char
    components.append(current)
    return None if quoted else components


def scope_states(lines: list[str]) -> list[tuple[tuple[str, ...], bool]] | None:
    """For each line, the namespace in force (its components) and whether the innermost scope is public, that
    is, a `public section` or inside one (a nested `section`, `namespace` or `mutual` keeps the visibility around
    it). As in Lean, a dotted name opens or closes one scope per component: `namespace A.B` opens two, which
    `end B` and `end A`, or `end A.B`, close; only namespaces add to names.

    A quoted component («Auxiliary.Scope») counts as one. None when the scopes do not balance (an `end` with
    nothing to close) or a quote is left open; module_private_lines then fails open."""
    scopes: list[tuple[str | None, bool]] = []  # each open scope: its namespace component (None if none), public
    states: list[tuple[tuple[str, ...], bool]] = []
    for line in code_lines(lines):
        scope = _SCOPE.match(line)
        if scope:
            kind, name = scope.group("kind"), scope.group("name")
            components = name_components(name) if name and kind != "mutual" else [""]
            if components is None or line[scope.end():].startswith("«"):  # a quote left open
                return None
            if kind == "end":
                if len(scopes) < len(components):
                    return None
                del scopes[len(scopes) - len(components):]
            else:
                inherited = scopes[-1][1] if scopes else False
                public = inherited or (kind == "section" and "public" in scope.group("mods").split())
                scopes.extend((component if kind == "namespace" else None, public) for component in components)
        states.append((tuple(component for component, _ in scopes if component is not None), bool(scopes and scopes[-1][1])))
    return states


def module_private_lines(lines: list[str]) -> frozenset[int]:
    """The (0-based) lines where a declaration is private by module visibility: in a file that opens with
    `module`, outside every `public section` (see scope_states). A declaration written `public` or `private`
    says so itself.

    It fails open: in a file that is no module, or whose scopes scope_states cannot follow, no line is private,
    so a misread keeps a declaration rather than losing it.
    """
    code = code_lines(lines)
    first = next((line for line in code if line.strip()), "")
    if not _MODULE_HEADER.match(first):
        return frozenset()
    states = scope_states(lines)
    if states is None:
        return frozenset()
    return frozenset(number for number, (_, public) in enumerate(states) if not public)


def visible(match: re.Match, number: int, module_private: frozenset[int]) -> bool:
    """Whether a declaration line declares something public: neither written `private` nor private by module
    visibility (see module_private_lines). A wanted command is always kept: Batteries makes each one a private
    placeholder anyway, so its visibility says nothing about the statement it asks for."""
    mods = match.group("mods").split()
    if "private" in mods:
        return False
    return "public" in mods or match.group("kw") in WANTED or number not in module_private


def section_labels(lines: list[str]) -> list[tuple[str, str, str]]:
    """The doc heading, named section and namespace in force at each line.

    The first `/-!` block is the module docstring, which describes the whole
    file, so its headings do not divide the declarations below it.
    """
    heading, sections, namespaces, labels = "", [], [], []
    in_doc = header = False
    seen_doc = False
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("/-!"):
            in_doc, header, seen_doc = True, not seen_doc, True
        if in_doc and not header:
            match = re.match(r"(?:/-!\s*)?#{1,3}\s+(.+?)\s*(?:-/)?$", stripped)
            if match:
                heading = match.group(1)
        if in_doc and stripped.endswith("-/"):
            in_doc = False
        opened = re.match(r"(section|namespace)(?:\s+(\S+))?\s*$", line)
        if opened:
            (sections if opened.group(1) == "section" else namespaces).append(opened.group(2) or "")
        closed = re.match(r"end(?:\s+(\S+))?\s*$", line)
        if closed:
            name = closed.group(1) or ""
            if sections and sections[-1] == name:
                sections.pop()
            elif namespaces and namespaces[-1] == name:
                namespaces.pop()
        labels.append((heading, sections[-1] if sections else "", namespaces[-1] if namespaces else ""))
    return labels


def module_groups(items: list[Target]) -> list[str] | None:
    """Section titles for a module page: doc headings, else named sections, else namespaces."""
    for position in range(3):
        values = [item.sections[position] for item in items]
        if len({value for value in values if value}) < 2:
            continue
        # An unlabeled declaration after a labeled one would read as part of
        # the section above it; only a leading run may be unlabeled.
        first = next(index for index, value in enumerate(values) if value)
        if not all(values[first:]):
            continue
        titles = [value if position == 0 else humanize(value.split(".")[-1]) if value else "" for value in values]
        if any(title.lower() in RESERVED_HEADINGS for title in titles):
            return None
        return titles
    return None


def declaration_head(code: list[str], number: int):
    """The declaration match of code line *number*, or None. A head that stops after its keyword, its name on the
    next line (`public theorem_wanted` and then `foo : ...`), is read with that line joined to it."""
    match = V2_DECLARATION.match(code[number])
    if match is None or match.group("name") or code[number][match.end():].strip():
        return match
    following = next((line for line in code[number + 1:] if line.strip()), "")
    return V2_DECLARATION.match(code[number].rstrip() + " " + following.strip())


def declaration_heads(lines: list[str]):
    """(line number, match) for every declaration head in the source, at any indentation, read with comments and
    literals blanked out and with names continued on the next line (see declaration_head)."""
    code = code_lines(lines)
    for number in range(len(code)):
        match = declaration_head(code, number)
        if match:
            yield number, match


def declaration_lines(lines: list[str], indexed: frozenset[int] | set[int] = frozenset()):
    """(line number, match) for each declaration line: unindented, indented inside a `mutual` block, or indented
    on a line where the Lean index found a declaration (`indexed` holds 1-based line numbers), as under
    `open ... in` or in an indented section. Lines are read with their comments and literals blanked out, so
    text in a comment, docstring or string never counts, nor opens or closes a `mutual` block."""
    in_mutual = False
    code = code_lines(lines)
    for number, line in enumerate(code):
        stripped = line.strip()
        if stripped == "mutual":
            in_mutual = True
            continue
        if in_mutual and stripped == "end":
            in_mutual = False
            continue
        match = declaration_head(code, number)
        if match and (in_mutual or not line[:1].isspace() or number + 1 in indexed):
            yield number, match


def module_heading(text: str) -> str:
    """The `# ` heading of a module's docstring, or "" if it has none."""
    heading = re.search(r"/-!\s*#[ \t]+([^\n]+)", text)
    return heading.group(1).removesuffix("-/").strip() if heading else ""


def load_library(library: str, index, taxonomy: dict, titles: dict | None = None) -> tuple[list[Target], dict]:
    """A library's articles. ``titles`` maps (file, name as written) to (title, docstring opening) pairs: a
    declaration whose docstring starts with that opening takes the title, unless a sibling in its file has it."""
    located = {
        (declaration.path, declaration.line): declaration
        for declaration in index.declarations.values()
        if declaration.path.parts[:1] == (library,)
    }
    indexed_lines: dict[Path, set[int]] = defaultdict(set)
    for path, line in located:
        indexed_lines[path].add(line)
    targets: list[Target] = []
    summary = {"public": 0, "documented": 0, "instances": 0, "subjects": set(), "unsubjected": [], "unindexed": []}
    named_by_docstring: set[int] = set()
    used_titles: dict[Path, set[str]] = defaultdict(set)
    for path in sorted((ROOT / library).rglob("*.lean")):
        relative = path.relative_to(ROOT)
        text = path.read_text()
        lines = text.splitlines()
        has_sorry = re.search(r"\bsorry\b", without_comments(text)) is not None
        module = relative.with_suffix("").parts
        module_title = module_heading(text)
        placed = placement(module, taxonomy["placements"])
        subject = placed[1]["to"].split("/")[0] if placed else LIBRARIES[library].get(module[1], module[1])
        if subject not in taxonomy["subjects"]:
            # A folder upstream just added waits for a subject; its modules get no pages until then, but the coverage
            # counts their declarations like any other.
            summary["unsubjected"].append(relative.as_posix())
            module_private = module_private_lines(lines)
            for number, match in declaration_lines(lines, indexed_lines[relative]):
                if not visible(match, number, module_private):
                    continue
                summary["public"] += 1
                if match.group("kw") == "instance":
                    summary["instances"] += 1
                elif docstring_before(lines, number) is not None:
                    summary["documented"] += 1
            continue
        labels = section_labels(lines)
        module_private = module_private_lines(lines)
        for number, match in declaration_lines(lines, indexed_lines[relative]):
            # A private declaration, written so or private by module visibility, gets no page and no count; a
            # page an editor already gave one keeps it, since its declaration still exists.
            if not visible(match, number, module_private):
                continue
            summary["public"] += 1
            if match.group("kw") == "instance":
                summary["instances"] += 1
                continue
            doc = docstring_before(lines, number)
            if doc is None:
                continue
            summary["documented"] += 1
            keyword, written = match.group("kw"), match.group("name")
            short = written.split(".")[-1]
            found = located.get((relative, number + 1))
            if found is None:
                # The Lean index lacks it (a name declared in two modules, which the index leaves unselected): no
                # page under a name reconstructed from the source; the declarations sync reports it for an editor.
                summary["unindexed"].append(f"{relative.as_posix()}:{number + 1} {written}")
                continue
            if found.keyword in WANTED:
                # Stated without a proof. A wanted definition stays unstated,
                # because Autoform counts a stated definition as defined.
                declaration, lean = WANTED[found.keyword], found.name
                statement, proof = found.keyword == "theorem_wanted", False
            else:
                declaration, lean = found.keyword, found.name
                is_data = declaration in DEFINITION_DECLARATIONS
                statement = not (is_data and has_sorry)
                proof = not is_data and not has_sorry
            statement_text, citations = split_docstring(doc)
            bold = BOLD_TITLE.match(statement_text)
            if bold:
                named_by_docstring.add(len(targets))
            # A bold name can wrap; a title must stay on its heading line.
            title = " ".join(bold.group("title").split()).rstrip(".") if bold else humanize(short) or first_words(statement_text)
            if not bold and titles:
                opened = " ".join(doc.split())
                for name, opening in titles.get((relative.as_posix(), match.group("name")), []):
                    if opened.startswith(opening) and name.casefold() not in used_titles[relative]:
                        title = name
                        named_by_docstring.add(len(targets))
                        break
            used_titles[relative].add(title.casefold())
            summary["subjects"].add(subject)
            body = "\n".join(
                "\\" + row if row.lstrip().startswith("#") else row
                for row in DISPLAY_MATH.sub(r"\n\n\1\n\n", statement_text).strip().splitlines()
            )
            targets.append(
                Target(
                    book=library,
                    idx=len(targets),
                    title=title.replace("[", "(").replace("]", ")"),
                    slug=slugify(humanize(short) or title, 40),
                    location=subject,
                    description=safe_math_markdown(body),
                    declaration=declaration,
                    lean=lean,
                    statement=statement,
                    proof=proof,
                    names=[lean],
                    citations=citations,
                    module=module,
                    module_title=module_title,
                    sections=labels[number],
                    line=number + 1,
                )
            )
    # A module with one article is usually named after its result: the taxonomy's title for it, if it has one.
    per_module: dict[tuple[str, ...], list[Target]] = defaultdict(list)
    for target in targets:
        per_module[target.module].append(target)
    for module, items in per_module.items():
        if len(items) == 1 and items[0].idx not in named_by_docstring:
            placed = placement(module, taxonomy["placements"])
            own = placed is not None and placed[0] == "/".join(module)
            items[0].title = placed[1]["title"] if own else humanize(module[-1])
    return targets, summary


def page_title(heading: str) -> str | None:
    """A module docstring's heading as a page title, code marks dropped; None if it holds math or a Lean name."""
    if "$" in heading or any("." in span for span in re.findall(r"`([^`]*)`", heading)):
        return None
    title = heading.replace("`", "")
    return title if 0 < len(title) <= 90 and title[0].isupper() else None


def articles(node: Container | Target) -> list[Target]:
    return [node] if isinstance(node, Target) else [child for child in walk(node) if isinstance(child, Target)]


def strongly_connected(nodes: list[int], uses: list[Counter]) -> list[set[int]]:
    """The strongly connected groups of ``nodes`` under ``uses`` (Tarjan), groups that use no others first."""
    inside = set(nodes)
    index: dict[int, int] = {}
    low: dict[int, int] = {}
    stack: list[int] = []
    groups: list[set[int]] = []
    for root in nodes:
        if root in index:
            continue
        index[root] = low[root] = len(index)
        stack.append(root)
        work = [(root, iter([used for used in uses[root] if used in inside]))]
        while work:
            node, edges = work[-1]
            for used in edges:
                if used not in index:
                    index[used] = low[used] = len(index)
                    stack.append(used)
                    work.append((used, iter([other for other in uses[used] if other in inside])))
                    break
                if used in stack:
                    low[node] = min(low[node], index[used])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[node])
                if low[node] == index[node]:
                    group = set()
                    while not group or node not in group:
                        group.add(stack.pop())
                    groups.append(group)
    return groups


def dependency_order(nodes: list, lead: tuple = ()) -> list:
    """Siblings in reading order: each after the siblings its articles use.

    A sibling uses another when one of its articles depends, in statement or
    proof, on one of the other's. Single articles that a sibling page uses lead,
    with those in ``lead``, then the pages, then the other articles, so the list
    that shows them never puts an article between two sub-pages. A single that
    uses a page, or a single that does, follows the pages instead. Ties keep the
    given order; within a cycle, the sibling that uses the least of it goes first.
    """
    owner = {id(target): position for position, node in enumerate(nodes) for target in articles(node)}
    uses: list[Counter] = [Counter() for _ in nodes]
    for position, node in enumerate(nodes):
        for target in articles(node):
            for other in (*target.depends, *target.proof_depends):
                used = owner.get(id(other), position)
                if used != position:
                    uses[position][used] += 1
    pages = [position for position, node in enumerate(nodes) if isinstance(node, Container)]
    chosen = {id(node) for node in lead}
    leading: set[int] = set()
    frontier = [used for page in pages for used in uses[page] if isinstance(nodes[used], Target)]
    frontier += [position for position, node in enumerate(nodes) if id(node) in chosen and isinstance(node, Target)]
    while frontier:
        position = frontier.pop()
        if position not in leading:
            leading.add(position)
            frontier += [used for used in uses[position] if isinstance(nodes[used], Target)]
    blocked = {position for position in leading if any(used in pages for used in uses[position])}
    while more := {position for position in leading - blocked if any(used in blocked for used in uses[position])}:
        blocked |= more
    leading -= blocked

    def ordered(group: list[int]) -> list[int]:
        rest, result = list(group), []
        while rest:
            inside = set(rest)
            waiting = {position: sum(count for used, count in uses[position].items() if used in inside) for position in rest}
            pick = next((position for position in rest if not waiting[position]), None)
            if pick is None:
                # A cycle: the first group that uses nothing else left, and in it the sibling that uses the least of it.
                cycles = [group for group in strongly_connected(rest, uses) if all(used in group for position in group for used in uses[position] if used in inside)]
                cycle = min(cycles, key=lambda group: min(rest.index(position) for position in group))
                pick = min((position for position in rest if position in cycle),
                           key=lambda position: sum(count for used, count in uses[position].items() if used in cycle))
            result.append(pick)
            rest.remove(pick)
        return result

    singles = [position for position, node in enumerate(nodes) if isinstance(node, Target)]
    order = ordered([p for p in singles if p in leading]) + ordered(pages) + ordered([p for p in singles if p not in leading])
    return [nodes[position] for position in order]


def directory_pages(targets: list[Target], depth: int) -> list:
    """The directories and modules below a placed path, as pages, the way the Lean lays them out."""
    root: dict = {"dirs": {}, "modules": defaultdict(list)}
    for target in targets:
        node = root
        parts = target.module[depth:] or target.module[-1:]
        for part in parts[:-1]:
            node = node["dirs"].setdefault(part, {"dirs": {}, "modules": defaultdict(list)})
        node["modules"][parts[-1]].append(target)

    def build(node: dict, at: tuple[str, ...]) -> list:
        children: list = []
        for name in sorted(node["dirs"]):
            # As in Mathlib, Foo.lean beside Foo/ introduces the directory: its heading titles the page and its articles lead it.
            umbrella = (ROOT / Path(*at, name)).with_suffix(".lean")
            title = page_title(module_heading(umbrella.read_text())) if umbrella.is_file() else None
            own = node["modules"].pop(name, [])
            children.append(chunk(title or topic_title(name), slugify(humanize(name)), own + build(node["dirs"][name], (*at, name)), ranges=False))
        for name in sorted(node["modules"]):
            items = node["modules"][name]
            if len(items) == 1:
                children.append(items[0])
                continue
            title = page_title(items[0].module_title) or topic_title(name)
            children.append(module_page(title, items, module_groups(items)))
        return dependency_order(children)

    return build(root, targets[0].module[:depth])


def module_page(title: str, items: list[Target], groups: list[str] | None) -> Container:
    """One page of declarations in source order."""
    if len(items) <= MAX_MODULE_CHILDREN:
        page = Container(title, slugify(title), items, groups=groups)
    else:
        page = chunk(title, slugify(title), items)
    page.navigation = "module"
    return page


def topic_node(title: str, members: dict[str, list[Target]]) -> Container | Target:
    """A topic: the declarations of its modules, or the pages of a placed directory.

    Placements that share a field and a title arrive here together; that is how
    a WantedExt statement file joins the development it belongs to.
    """
    order = list(LIBRARIES)
    keys = sorted(members, key=lambda key: (order.index(key.split("/")[0]), key))
    if all(len(key.split("/")) == len(target.module) for key in keys for target in members[key]):
        # Modules follow the modules they use; declarations keep their source order.
        keys = [group.title for group in dependency_order([Container(key, key, members[key]) for key in keys])]
        items = [target for key in keys for target in members[key]]
        if len(items) == 1:
            return items[0]
        return module_page(title, items, module_groups(items) if len(keys) == 1 else None)
    children = dependency_order([page for key in keys for page in directory_pages(members[key], len(key.split("/")))])
    if len(children) == 1 and isinstance(children[0], Container):
        children[0].title, children[0].slug = title, slugify(title)
        return children[0]
    return chunk(title, slugify(title), namesake_first(title, children), ranges=False)


def same_title(a: str, b: str) -> bool:
    return a.replace("–", "-").casefold() == b.replace("–", "-").casefold()


def module_pieces(page: Container) -> list:
    """A page's children; for a module page merged from several modules, a page per module, as a directory shows them."""
    if page.navigation != "module" or not all(isinstance(child, Target) for child in page.children):
        return page.children
    modules: dict[tuple[str, ...], list[Target]] = defaultdict(list)
    for target in page.children:
        modules[target.module].append(target)
    if len(modules) == 1:
        return page.children
    return [
        items[0] if len(items) == 1 else module_page(page_title(items[0].module_title) or topic_title(module[-1]), items, module_groups(items))
        for module, items in modules.items()
    ]


def namesake_first(title: str, children: list) -> list:
    """A child page titled like its parent is the parent's own material: its pages lead the parent's, if they fit on it."""
    own = [node for node in children if isinstance(node, Container) and same_title(node.title, title)]
    if not own:
        return children
    pieces = [piece for node in own for piece in module_pieces(node)]
    led = dependency_order(pieces + [node for node in children if all(node is not other for other in own)], lead=tuple(pieces))
    return namesake_first(title, led) if len(led) <= MAX_CHILDREN else children


def subject_tree(subject: str, targets: list[Target], taxonomy: dict) -> Container:
    """A subject's fields, subfields and topics, as the taxonomy places its modules."""
    entry = taxonomy["subjects"][subject]
    topics: dict[tuple[str, str], dict[str, list[Target]]] = defaultdict(lambda: defaultdict(list))
    for target in targets:
        placed = placement(target.module, taxonomy["placements"])
        if placed:
            key, spot = placed
            topics[(spot["to"], spot["title"])][key].append(target)
        else:
            key = "/".join(target.module)
            topics[(f"{subject}/{UNPLACED['slug']}", topic_title(target.module[-1]))][key].append(target)
    at: dict[str, list] = defaultdict(list)
    for (to, title), members in topics.items():
        at[to.split("/", 1)[1]].append(topic_node(title, members))

    def page(spec: dict, children: list) -> Container:
        node = chunk(spec["title"], spec["slug"], namesake_first(spec["title"], children), ranges=False)
        node.prose = spec["description"]
        return node

    fields = []
    for spec in [*entry["fields"], UNPLACED]:
        inner = []
        # The taxonomy orders fields and subfields; topics follow the topics they use, then their titles.
        for sub in spec["subfields"]:
            members = dependency_order(sorted(at.pop(f"{spec['slug']}/{sub['slug']}", []), key=lambda node: node.title.casefold()))
            if members:
                inner.append(page(sub, members))
        inner += dependency_order(sorted(at.pop(spec["slug"], []), key=lambda node: node.title.casefold()))
        if inner:
            fields.append(page(spec, inner))
    if at:
        raise SystemExit(f"{TAXONOMY.relative_to(ROOT)}: {subject} places topics in unknown fields {sorted(at)}")
    return Container(entry["title"], subject, fields, prose=entry["description"])


def link_v2(targets: list[Target], dependencies: dict) -> None:
    """Add Lean dependency edges between v2 articles from sources/v2/lean-dependencies.json."""
    by_name = {target.lean: target for target in targets if target.lean}

    def find(name: str) -> Target | None:
        return by_name.get(name)

    for name, entry in dependencies.items():
        target = find(name)
        if target is None:
            continue
        seen = {id(other) for other in target.depends + target.proof_depends}
        for kind, bucket in (("statement", target.depends), ("proof", target.proof_depends)):
            for dependency in entry[kind]:
                other = find(dependency)
                if other is not None and other is not target and id(other) not in seen:
                    bucket.append(other)
                    seen.add(id(other))


def assign_paths(node: Container, directory: Path, kept: dict[str, Path] | None = None) -> None:
    """Paths for a page's children. Siblings that share a slug are numbered, but a
    declaration that stays in its folder keeps its file name (``kept``, by Lean
    name), so reordering siblings never hands its URL to another."""
    node.path = directory / "README.md"
    taken: set[str] = set(RESERVED_SLUGS)
    staying: set[int] = set()
    for child in node.children:
        before = (kept or {}).get(page_key(child)) if isinstance(child, Target) else None
        if before and before.parent == directory and before.stem not in taken and re.fullmatch(re.escape(child.slug) + r"(?:-\d+)?", before.stem):
            child.slug = before.stem
            taken.add(child.slug)
            staying.add(id(child))
    for child in node.children:
        if id(child) not in staying:
            base, number = child.slug, 1
            while child.slug in taken:
                number += 1
                child.slug = f"{base}-{number}"
            taken.add(child.slug)
        if isinstance(child, Container):
            assign_paths(child, directory / child.slug, kept)
        else:
            child.path = directory / f"{child.slug}.md"


def rel(source: Path, target: Path) -> str:
    """Relative link from one vault file to another."""
    common = 0
    for left, right in zip(source.parent.parts, target.parts):
        if left != right:
            break
        common += 1
    up = len(source.parent.parts) - common
    return "/".join([".."] * up + list(target.parts[common:]))


def frontmatter(fields: list[tuple[str, str]], previous: str | None) -> str:
    match = ARTICLE_ID.search(previous or "")
    lines = ([f"article_id: {match.group(1)}"] if match else []) + [f"{key}: {value}" for key, value in fields]
    return "---\n" + "\n".join(lines) + "\n---\n\n" if lines else ""


def listed(children: list) -> list:
    """A page's children in the order its list shows them.

    Render turns a bullet that links one of the page's own articles into the
    article's card, so an article among the sub-pages would split their list:
    articles after the first sub-page follow the last one. A leading run of
    articles, an umbrella's or namesake's own, still leads.
    """
    first = next((index for index, child in enumerate(children) if isinstance(child, Container)), len(children))
    rest = children[first:]
    return children[:first] + [child for child in rest if isinstance(child, Container)] + [child for child in rest if isinstance(child, Target)]


def render_container(node: Container, previous: str | None, extra: str = "") -> str:
    vault_path = node.path.relative_to(VAULT)
    lines = [f"# {node.title}", ""]
    if node.prose:
        lines += [node.prose.replace("SOURCES/", rel(vault_path, Path("sources")) + "/"), ""]
    if extra:
        lines += [extra, ""]
    # Mathematical introductions and region labels are authored curation.
    # Regenerating the inventory must not erase them or infer them from paths.
    introduction = re.search(r"(?ms)^## Mathematical overview\n(.*?)(?=^## |\Z)", previous or "")
    if introduction:
        heading = re.search(r"(?m)^# (.+)$", previous or "")
        if heading:
            lines[0] = "# " + heading.group(1)
        text = introduction.group(1).strip()
        if text:
            lines += ["## Mathematical overview", "", text, ""]
        lines += ["## Contents", ""]
    level = "###" if introduction else "##"

    def link(child: Container | Target) -> str:
        return f"- [{link_text(child.title)}]({rel(vault_path, child.path.relative_to(VAULT))})"

    if node.children and all(isinstance(child, Container) and child.navigation == "transparent" for child in node.children):
        # Pagination parts read as sections of this page, not as pages to open.
        # Each heading still links its part, which keeps the part, and so the
        # depth of its children, in the site navigation built from these links.
        for part in node.children:
            heading = f"[{link_text(part.title)}]({rel(vault_path, part.path.relative_to(VAULT))})"
            lines += [f"{level} {heading}", "", *(link(child) for child in listed(part.children)), ""]
        lines.pop()
    elif node.groups:
        current = None
        for group, child in zip(node.groups, node.children):
            if group and group != current:
                if lines[-1] != "":
                    lines.append("")
                lines += [f"{level} {group}", ""]
            current = group or current
            lines.append(link(child))
    else:
        lines += [link(child) for child in listed(node.children)]
    fields = [("navigation", node.navigation)] if node.navigation else []
    header = (previous or "").split("---", 2)
    if len(header) == 3 and not header[0].strip():
        area = re.search(r"(?m)^area:\s*(.+)$", header[1])
        if area:
            fields.append(("area", area.group(1).strip()))
    return frontmatter(fields, previous) + "\n".join(lines) + "\n"


def render_target(target: Target, previous: str | None) -> str:
    vault_path = target.path.relative_to(VAULT)
    fields = [("declaration", target.declaration)]
    # Autoform reads a cited article as one that links its source; a citation in plain text claims no origin.
    if any(link_targets(citation) for citation in target.citations):
        fields.append(("origin", "cited"))
    if target.statement:
        fields.append(("statement", "formalized"))
    if target.proof:
        fields.append(("proof", "formalized"))
    if target.lean:
        fields.append(("lean", target.lean))
    lines = [f"# {target.title}", "", target.description, "", "## Depends on", ""]
    if target.depends:
        lines += [f"- [{link_text(o.title)}]({rel(vault_path, o.path.relative_to(VAULT))})" for o in target.depends]
    else:
        lines.append("This node has no prerequisites.")
    if target.proof_depends:
        lines += ["", "## Proof depends on", ""]
        lines += [
            f"- [{link_text(o.title)}]({rel(vault_path, o.path.relative_to(VAULT))})" for o in target.proof_depends
        ]
    if target.citations:
        lines += ["", "## Sources", ""] + [f"- {citation}" for citation in target.citations]
    return frontmatter(fields, previous) + "\n".join(lines) + "\n"


def walk(node: Container):
    yield node
    for child in node.children:
        if isinstance(child, Container):
            yield from walk(child)
        else:
            yield child


def library_navigation_section(text: str) -> str:
    """Keep authored library links; refuse ambiguous headings rather than erase them."""
    parts = article_parts(text)
    if any(section.title != "Library navigation" for section in parts.sections):
        raise ValueError("Coverage authored sections belong under ## Library navigation, with lower-level headings")
    if len(parts.sections) > 1:
        raise ValueError("Coverage has more than one Library navigation section")

    def check_unparsed_heading(line: str) -> str:
        # A setext heading or one hidden by a comment stays in the preamble.
        if line.strip().lstrip("#").strip().casefold() == "library navigation":
            raise ValueError("Coverage must use a visible ## Library navigation heading")
        return line

    outside_fences(parts.statement, check_unparsed_heading)
    return f"## Library navigation\n\n{parts.sections[0].body}\n" if parts.sections else ""


def render_coverage(rows: list[tuple[str, str, str]], library_navigation: str = "") -> str:
    lines = [
        "---",
        "kind: coverage",
        "status: in-progress",
        "---",
        "",
        "# ATLAS coverage",
        "",
        "Each documented public declaration of the ATLAS v2 libraries, instances aside, gets one",
        "roadmap article, which `scripts/sync_wiki.py declarations` writes from its docstring; a",
        "declaration the Lean index does not select waits for an editor. The counts below are of",
        "documented non-instance declarations, so they include any whose article that sync has",
        "yet to write. The standalone `Atlas/` developments are not decomposed yet,",
        "and the archived v1 release is not part of the wiki. Progress percentages and target",
        "counts cover only the decomposed rows below; they are not repository-wide coverage.",
        "",
        "| Area | Coverage | Evidence |",
        "| --- | --- | --- |",
    ]
    lines += [f"| {area} | {coverage} | {evidence} |" for area, coverage, evidence in rows]
    if library_navigation:
        lines += ["", library_navigation.rstrip("\n")]
    return "\n".join(lines) + "\n"


def render_roadmap_root(taxonomy: dict, subjects: list[str], previous: str | None) -> str:
    lines = ["# ATLAS roadmap"]
    for region, members in regions(taxonomy, subjects).items():
        lines += ["", f"## {region}", ""]
        lines += [f"- [{taxonomy['subjects'][subject]['title']}]({subject}/README.md)" for subject in members]
    for library, description in (
        ("Domains", "Application-specific models and their roadmaps."),
        ("CSLibExt", "Computer-science developments and their roadmaps."),
        ("PhyslibExt", "Physics developments and their roadmaps."),
    ):
        lines += ["", f"## {library}", "", description, "",
                  f"- [Browse {library}](../coverage/README.md#{library.lower()})"]
    return frontmatter([], previous) + "\n".join(lines) + "\n"


def regions(taxonomy: dict, subjects: list[str]) -> dict[str, list[str]]:
    """Each region's subjects that hold articles, in the taxonomy's order."""
    out = {region: [subject for subject in members if subject in subjects] for region, members in taxonomy["regions"].items()}
    placed = {subject for members in out.values() for subject in members}
    if set(subjects) - placed:
        out["Other subjects"] = [subject for subject in subjects if subject not in placed]
    return {region: members for region, members in out.items() if members}


def page_entry(text: str, label: str | None = None) -> dict[str, str]:
    """What a regeneration keeps from a page: its article id, and its Lean name or, without one, its label from page_key."""
    header = text.split("---", 2)
    if len(header) != 3 or header[0].strip():
        return {}
    entry = {}
    article = ARTICLE_ID.search(header[1])
    if article:
        entry["article_id"] = article.group(1)
    lean = re.search(r"(?m)^lean: (\S+)$", header[1])
    if lean:
        entry["lean"] = lean.group(1)
    elif label:
        entry["label"] = label
    return entry


def render_page_map(files: dict[Path, str], labels: dict[Path, str] | None = None) -> str:
    """blueprint/pages.json: the entry of every generated page that has one, by its path in the roadmap, a line each.

    labels holds the page_key of each page without a Lean name, which the page itself does not show.
    """
    labels = labels or {}
    entries = {
        path.relative_to(ROADMAP).as_posix(): page_entry(text, labels.get(path))
        for path, text in files.items()
        if path.is_relative_to(ROADMAP)
    }
    lines = [f"{json.dumps(path, ensure_ascii=False)}: {json.dumps(entry, ensure_ascii=False, sort_keys=True)}"
             for path, entry in sorted(entries.items()) if entry]
    return "{\n" + ",\n".join(lines) + "\n}\n"


def committed_pages() -> dict[Path, dict[str, str]]:
    """Each page's entry in blueprint/pages.json, as the last regeneration left it."""
    if not PAGE_MAP.is_file():
        return {}
    return {ROADMAP / path: entry for path, entry in json.loads(PAGE_MAP.read_text()).items()}


def ids_by_lean() -> dict[str, str]:
    """Article ids by Lean name, so a page that moves keeps its id."""
    found: dict[str, set[str]] = defaultdict(set)
    for entry in committed_pages().values():
        if "article_id" in entry and "lean" in entry:
            found[entry["lean"]].add(entry["article_id"])
    return {name: next(iter(ids)) for name, ids in found.items() if len(ids) == 1}


def page_key(target: Target) -> str | None:
    """How regeneration finds a declaration's current page: its Lean name, or else its library, module and title."""
    if target.lean:
        return target.lean
    return f"{target.book}, {'.'.join(target.module)}\n{target.title}" if target.module else None


def pages_by_lean() -> dict[str, Path]:
    """The current page of each declaration, by page_key, so a declaration that stays in its folder keeps its file name."""
    found: dict[str, set[Path]] = defaultdict(set)
    for path, entry in committed_pages().items():
        key = entry.get("lean") or entry.get("label")
        if key:
            found[key].add(path)
    return {key: next(iter(paths)) for key, paths in found.items() if len(paths) == 1}


def generate(titles: dict | None = None, dependency_file: Path | None = None, rendered: list | None = None, index=None,
             unindexed: list | None = None) -> dict[Path, str]:
    """Every page, by path, with blueprint/pages.json; ``titles`` as load_library takes them, and the Lean
    dependency edges from ``dependency_file`` (default sources/v2/lean-dependencies.json) when it exists.
    Every article's Target is added to ``rendered`` when given, and each documented declaration the Lean index
    lacks, as `path:line name`, to ``unindexed``; ``index`` is the project's, when already built."""
    # The archived v1 release and the standalone code under Atlas/ are not part of
    # the wiki, and both declare many v2 names again. Autoform selects neither
    # declaration of a name declared twice, so indexing them would leave those
    # articles unlinked.
    index = index or index_project(ROOT, exclude_roots=("v1", "Atlas"))
    files: dict[Path, str] = {}
    # A page keeps the article id it had at its path, which is all the renderers take from the page before.
    ids_at = {path: entry["article_id"] for path, entry in committed_pages().items() if "article_id" in entry}
    previous = lambda path: f"---\narticle_id: {ids_at[path]}\n---\n" if path in ids_at else None  # noqa: E731
    known_ids = ids_by_lean()
    kept = pages_by_lean()
    v2_coverage = []
    taxonomy = load_taxonomy()
    v2_loaded = {library: load_library(library, index, taxonomy, titles) for library in LIBRARIES}
    v2_by_subject: dict[str, list[Target]] = defaultdict(list)
    for targets, _ in v2_loaded.values():
        for target in targets:
            v2_by_subject[target.location].append(target)
    subjects = sorted(v2_by_subject)
    unplaced = sorted({"/".join(t.module) for ts in v2_by_subject.values() for t in ts if not placement(t.module, taxonomy["placements"])})
    if unplaced:
        print(f"note: {len(unplaced)} modules have no place in {TAXONOMY.relative_to(ROOT)} yet, so their subjects list them "
              f"as not yet classified: {', '.join(unplaced[:5])}{', ...' if len(unplaced) > 5 else ''}", file=sys.stderr)
    unsubjected = sorted(path for _, summary in v2_loaded.values() for path in summary["unsubjected"])
    if unsubjected:
        print(f"note: {len(unsubjected)} modules are in folders with no subject in {TAXONOMY.relative_to(ROOT)} or "
              f"generate_wiki.LIBRARIES, so they get no pages yet: {', '.join(unsubjected[:5])}"
              f"{', ...' if len(unsubjected) > 5 else ''}", file=sys.stderr)
    if unindexed is not None:
        unindexed.extend(sorted(entry for _, summary in v2_loaded.values() for entry in summary["unindexed"]))
    # Dependencies come first: they order the topics.
    dependency_file = dependency_file or SOURCES / "v2" / "lean-dependencies.json"
    dependency_data = None
    if dependency_file.is_file():
        dependency_data = json.loads(dependency_file.read_text())
        link_v2(
            [target for targets, _ in v2_loaded.values() for target in targets],
            dependency_data["articles"],
        )
    trees = []
    for subject in subjects:
        tree = subject_tree(subject, v2_by_subject[subject], taxonomy)
        assign_paths(tree, ROADMAP / subject, kept)
        trees.append(tree)
    every_v2 = Container("v2", "v2", trees)
    lean_counts = Counter(node.lean for node in walk(every_v2) if isinstance(node, Target) and node.lean)
    for node in walk(every_v2):
        if node is not every_v2:
            render = render_container if isinstance(node, Container) else render_target
            prior = previous(node.path)
            # A declaration keeps its id by Lean name, whatever page held its path before.
            if isinstance(node, Target) and lean_counts[node.lean] == 1 and node.lean in known_ids:
                prior = f"article_id: {known_ids[node.lean]}\n"
            files[node.path] = render(node, prior)
            if rendered is not None and render is render_target:
                rendered.append(node)
    for library, (_, summary) in v2_loaded.items():
        v2_coverage.append(
            (
                f"v2 / {library}",
                "DECOMPOSED",
                f"[{summary['documented']} documented public non-instance declarations](../roadmap/README.md) "
                f"across {len(summary['subjects'])} subjects; {summary['instances']} instances and "
                f"{summary['public'] - summary['instances'] - summary['documented']} undocumented public non-instance "
                "declarations are not articles.",
            )
        )
    coverage = v2_coverage + [
        ("v2 tests (MathlibExtTest, CSLibExtTest, PhyslibExtTest, DomainsTest)", "OUT", "Tests and diagnostics rather than mathematical results."),
        # No file counts: the Pages build leaves Atlas/ out of its checkout.
        ("Atlas/StatisticalMechanics", "MAPPED", "Standalone Lean files; no roadmap articles yet."),
        ("Atlas/FC", "MAPPED", "Standalone Lean files; no roadmap articles yet."),
        ("Atlas/CPythonListsort", "OUT", "Maintained as its own Autoform blueprint inside Atlas/CPythonListsort."),
    ]
    root = ROADMAP / "README.md"
    files[root] = render_roadmap_root(taxonomy, subjects, previous(root))
    # The map draws one region per area, with its subjects inside.
    atlas = {"schema": "autoform-atlas/v1", "areas": regions(taxonomy, subjects)}
    files[VAULT / "atlas.json"] = json.dumps(atlas, indent=2, ensure_ascii=False) + "\n"
    coverage_path = VAULT / "coverage" / "README.md"
    navigation = library_navigation_section(coverage_path.read_text(encoding="utf-8")) if coverage_path.is_file() else ""
    files[coverage_path] = render_coverage(coverage, navigation)
    labels = {node.path: page_key(node) for node in walk(every_v2) if isinstance(node, Target) and not node.lean}
    files[PAGE_MAP] = render_page_map(files, labels)
    return files
