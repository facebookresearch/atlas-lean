#!/usr/bin/env python3
"""Keep the ATLAS wiki's committed pages and the Lean in step.

    python scripts/sync_wiki.py import TITLES.jsonl DEPENDENCIES.json   seed blueprint/ once from the Lean docstrings
    python scripts/sync_wiki.py lean-facts DEPENDENCIES.json            the Lean's facts, at build; never committed
    python scripts/sync_wiki.py declarations                            new declarations' pages, after an upstream merge

The wiki owns every page's text: titles, statements, sources, prose and the page
tree under blueprint/roadmap/. Each article's annotation in blueprint/links/
(literature-links, read by Autoform) ties it to its Lean declaration and holds its
article id and origin. The Lean owns what lean-facts adds on the build's checkout:
an article's `## Depends on` and `## Proof depends on`, from the dependency dump,
and its annotation's kind and status, from the Lean sources.

declarations gives each declaration with a docstring and no page a page from its
docstring, beside its module's other pages and listed on their page in source
order, and marks it as taken from the docstring. A module with no pages yet gets
the folders and folder pages generate_wiki lays out where scripts/taxonomy.json
places it, and its topmost new folder joins its parent's list. A deprecated
declaration gets no page: upstream is retiring it, and the wiki may have dropped
its page. Nor does a held declaration (see held_name): its page stays unlinked
until the Lean is fixed, and the run lists it as held; a marker it cannot use
is an error, and the run then writes nothing. It lists pages whose
declaration is gone and docstrings that changed since the last run
(scripts/wiki-sync.json keeps their digests), and changes no article that
exists. Its first run records the digests only. The source-derived
area catalog and coverage summary are refreshed with the same source snapshot.
A folder page is edited within only when it is simple (see simple_page): a page
with no listed neighbour then ends the folder page's own list, ahead of "Related
topics" or "Sources", joins a section of that list only beside its module's
pages, and else starts one under its module's title, after all that the last
section holds. On any other page, it goes at the end, after a blank line, and is
reported for an editor to place; if the page has raw HTML or a code fence, it is
left out and reported as an error. A folder the wiki has keeps its layout and each
topic its folder (see kept_layout), and a folder page split into parts lists what
its parts list when both pages are simple; any other part list is reported. Each
edit is checked before it is written (see verify_edit): Autoform's check of what
the site may publish must pass on the page, as render would otherwise show it as
typed, with no link, and the text it publishes is rendered with the site's
Markdown extensions and read as a browser builds it. An edit that would lose a
link, move a heading or its id, or show its new link elsewhere or not at all is
left out and reported too, and a page keeps its line ends and bytes.

import runs once, on a tree whose Lean still holds the wiki's English. TITLES.jsonl
holds checked titles, one {"file", "name", "opening", "title"} per line: a
declaration in that file under that name, whose docstring opens with "opening",
takes the title. DEPENDENCIES.json is the dependency dump the pages were last
ordered by, so every page keeps its path.

Run it with a Python that has Autoform installed (see blueprint-pages.yml).
"""

from __future__ import annotations

import functools
import hashlib
import importlib
import json
import re
import sys
import unicodedata
from collections import Counter, defaultdict
from pathlib import Path

if __package__:
    from . import generate_wiki as wiki
else:
    import generate_wiki as wiki

LINKS = wiki.VAULT / "links"
NAMESPACE = "org.autoform"
# Where an article with no Lean name in the index keeps its module and name, for lean-facts.
OWN = "org.atlas-wiki"
DEFAULTS = {"object": {"type": "lean", "uri": "../.."}}
STATE = wiki.ROOT / "scripts" / "wiki-sync.json"
# The site's build configuration, whose Markdown extensions a folder page is rendered with to check an edit.
SITE = wiki.ROOT / "mkdocs.yml"
LEAN_SECTIONS = ("Depends on", "Proof depends on")
FRONTMATTER = re.compile(r"\A---\n(.*?)\n---\n\n?", re.S)
SECTION = re.compile(r"(?m)^## (.+)$")
# A bold run opening a body, and a stop just after it: "**Title.**", "**Title**." or "**Title**:".
BOLD_LEAD = re.compile(r"\*\*(?P<lead>[^*\n]+)\*\*(?P<stop>[.:]?)")
# A folder page's list item, and a heading that links a part, as generate_wiki writes them.
LIST_LINK = re.compile(r"^- \[.*\]\(([^()\s]+)\)$")
HEADING_LINK = re.compile(r"^#{2,6} \[.*\]\(([^()\s]+)\)$")
# An item that links a page of the folder first, its title, that link and any text after it; and a part's heading, its
# title and link.
OWN_ITEM = re.compile(r"^- \[((?:\\.|[^\\\]])*)\]\((?!\.\./)([^():\s]+)\)(.*)$", re.S)
PART_HEADING = re.compile(r"^ {0,3}#{2,6}[ \t]+\[(.*)\]\((part-\d+/README\.md)\)$")
# A part list's item that the sync copies, and a copy of one: "- [title](page)" and any text after it, on one line,
# with no code or bracket in either text, no "<" that could open HTML and no backslash that could escape a bracket, a
# backtick, a "<" or itself; and a list item of any kind. A part list with a list item that is not simple is left to an
# editor.
PLAIN = r"(?:[^][`<\\\n]|<(?![A-Za-z/!?])|\\(?![][`<\\\n]|$))"
SIMPLE_ITEM = re.compile(rf"- \[((?:{PLAIN}|\\[][])+)\]\(([^][()\s\\<`]+)\)({PLAIN}*)")
# A line of plain text: one that is not indented and opens no other block: no list item, quote, table row, raw HTML,
# fence, heading, setext underline, thematic break, attribute list or link reference definition.
TEXT = re.compile(r"(?![-+*_>|<`~#=:{\s]|\d{1,9}[.)]|\[(?:[^]\\]|\\.)*\]:)")
# A list item of any kind, its marker with the space after it, and a heading below a page's title, as CommonMark has
# them.
LIST_ITEM = re.compile(r" {0,3}(?:[-+*]|\d{1,9}[.)])(?:[ \t]|$)")
HEADING = re.compile(r" {0,3}#{2,6}(?:[ \t]|$)")
# A page of the folder, as an item links it: "NAME.md" or "NAME/README.md", with no dot, slash, fragment, query,
# encoding or math in NAME (see destination).
CHILD = re.compile(r"[^./#?%&$\s]+(?:/README)?\.md")
# The titles of the sections that close a folder page: what they list is not the page's own list.
CLOSING = {"related topics", "sources", "references", "bibliography", "see also", "further reading", "depends on",
           "proof depends on", "mathematical overview"}
PART = re.compile(r"part-\d+")


def split_frontmatter(text: str) -> tuple[dict[str, str], str]:
    match = FRONTMATTER.match(text)
    if not match:
        return {}, text
    fields = dict(line.split(": ", 1) for line in match.group(1).splitlines() if ": " in line)
    return fields, text[match.end():]


def without_sections(body: str, names: tuple[str, ...]) -> str:
    """The body without the `## ` sections named, each running to the next `## ` heading; the rest stays as written."""
    starts = [match.start() for match in SECTION.finditer(body)]
    pieces = [body[start:end] for start, end in zip([0, *starts], [*starts, len(body)])]
    kept = [piece for piece in pieces if not ((heading := SECTION.match(piece)) and heading.group(1).strip() in names)]
    return "".join(kept).rstrip("\n") + "\n"


def plain_title(text: str) -> str:
    """A title as compared with another: bracket style, spacing, case and a closing stop aside."""
    text = unicodedata.normalize("NFC", text).translate(str.maketrans("[]", "()"))
    return " ".join(text.split()).rstrip(".:").casefold()


def without_title_lead(title: str, body: str) -> str:
    """*body* without the bold run it opens with when that restates *title* and ends a sentence or a label, as
    most docstrings open ("**Title.** The statement", "**Title**: the statement"), since the heading already says
    it; else *body* as written. What follows a label starts its sentence, so it gets a capital."""
    match = BOLD_LEAD.match(body)
    if not match or plain_title(match.group("lead")) != plain_title(title):
        return body
    lead = match.group("lead").rstrip()
    stop = lead[-1] if lead.endswith((".", ":")) else match.group("stop")
    rest = body[match.end():]
    # A run the sentence goes on from ("**Title** is ..."), or one with nothing after it before a section.
    if not stop and rest[:1] not in ("", "\n"):
        return body
    rest = rest.lstrip(" \t\n")
    if not rest or rest.startswith("## "):
        return body
    if rest[0].islower():
        if stop != ":":
            return body
        rest = rest[0].upper() + rest[1:]
    return rest


def has_lean_sections(body: str) -> bool:
    """Whether the body holds a section that lean-facts owns."""
    return any(match.group(1).strip() in LEAN_SECTIONS for match in SECTION.finditer(body))


def with_sections(body: str, sections: list[tuple[str, list[str]]]) -> str:
    """The body with the given `## ` sections in place of any it has by those names, before `## Sources`."""
    body = without_sections(body, tuple(name for name, _ in sections))
    block = "".join(f"## {name}\n\n" + "\n".join(lines) + "\n\n" for name, lines in sections)
    sources = re.search(r"(?m)^## Sources$", body)
    if sources:
        return body[: sources.start()] + block + body[sources.start():]
    return body + "\n" + block.rstrip("\n") + "\n"


def links_file(path: Path) -> Path:
    """The annotation file for a page: one per subject, and roadmap.jsonl for the root."""
    parts = path.relative_to(wiki.ROADMAP).parts
    return LINKS / f"{parts[0] if len(parts) > 1 else 'roadmap'}.jsonl"


def subject_path(annotation: dict) -> Path:
    return (LINKS / annotation["subject"][0]["uri"]).resolve()


def lean_name(annotation: dict) -> str | None:
    for end in annotation.get("object", []):
        name = end.get("location", {}).get("declaration")
        if name:
            return name
    return None


def read_annotations() -> dict[Path, list[dict]]:
    return {
        path: [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
        for path in sorted(LINKS.glob("*.jsonl"))
    }


def write_annotations(files: dict[Path, list[dict]]) -> None:
    for path, rows in files.items():
        path.write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows))


def load_titles(path: Path) -> dict[tuple[str, str], list[tuple[str, str]]]:
    titles: dict[tuple[str, str], list[tuple[str, str]]] = defaultdict(list)
    for line in path.read_text().splitlines():
        row = json.loads(line)
        titles[(row["file"], row["name"])].append((row["title"], " ".join(row["opening"].split())))
    return titles


def seed(titles: dict, dependency_file: Path) -> tuple[dict[Path, str], dict[Path, list[dict]]]:
    """The committed pages and annotations, from generate_wiki's pages of the current Lean."""
    targets: list[wiki.Target] = []
    files = wiki.generate(titles, dependency_file, targets)
    by_path = {target.path: target for target in targets}
    pages: dict[Path, str] = {}
    annotations: dict[Path, list[dict]] = defaultdict(list)
    for path, text in sorted(files.items()):
        if path == wiki.PAGE_MAP:
            continue
        if not path.is_relative_to(wiki.ROADMAP):
            pages[path] = text
            continue
        fields, body = split_frontmatter(text)
        target = by_path.get(path)
        if "declaration" in fields and target is None:
            raise SystemExit(f"{path}: generate_wiki rendered an article it did not hand back")
        pages[path] = without_sections(body, LEAN_SECTIONS) if target else body
        annotation: dict = {"subject": [{"type": "generic", "uri": "../" + path.relative_to(wiki.VAULT).as_posix()}]}
        if "lean" in fields:
            annotation["object"] = [{"location": {"declaration": fields["lean"]}}]
        if "article_id" in fields:
            annotation["id"] = fields["article_id"]
        extensions = {}
        ours = {key: fields[key] for key in ("origin", "navigation", "area") if key in fields}
        if ours:
            extensions[NAMESPACE] = ours
        if extensions:
            annotation["extensions"] = extensions
        annotations[links_file(path)].append(annotation)
    return pages, annotations


def run_import(titles_path: Path, dependency_file: Path) -> int:
    pages, annotations = seed(load_titles(titles_path), dependency_file)
    for path, text in pages.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    LINKS.mkdir(exist_ok=True)
    (LINKS / "_defaults.json").write_text(json.dumps(DEFAULTS) + "\n")
    write_annotations(annotations)
    wiki.PAGE_MAP.unlink(missing_ok=True)  # paths are committed now, and ids live in the annotations
    print(f"{len(pages)} pages, {sum(map(len, annotations.values()))} annotations in {len(annotations)} files")
    return 0


def lean_facts_for(name: str | None, own: dict | None, index, sorry) -> tuple[str | None, str | None]:
    """An article's kind and status from the Lean, as generate_wiki read them: a module with `sorry` leaves its
    theorems stated and its definitions unstated; a theorem_wanted is stated, a def_wanted unstated."""
    if name:
        declaration = index.declarations.get(name)
        if declaration is None:
            return None, None
        keyword, has_sorry = declaration.keyword, sorry(declaration.path)
        if keyword in wiki.WANTED:
            return wiki.WANTED[keyword], "stated" if keyword == "theorem_wanted" else None
        if keyword in wiki.DEFINITION_DECLARATIONS:
            return keyword, None if has_sorry else "formalized"
        return keyword, "stated" if has_sorry else "formalized"
    resolved = legacy_lean_name(own, index)
    if resolved:
        return lean_facts_for(resolved, None, index, sorry)
    return None, None


def legacy_lean_name(own: dict | None, index) -> str | None:
    """The Lean name of a page an earlier sync wrote with only a module and a name (no Lean link), read through
    the Lean index: the one declaration of that module whose last name component is that name; None when the
    index has none, or more than one, so no page is ever bound to a declaration by a guess."""
    if not (own and "module" in own and "name" in own):
        return None
    source = Path(*own["module"].split(".")).with_suffix(".lean")
    names = [name for name, declaration in index.declarations.items()
             if getattr(declaration, "path", None) is not None and Path(declaration.path) == source
             and name.split(".")[-1] == own["name"].split(".")[-1]]
    return names[0] if len(names) == 1 else None


def apply_lean_facts(index, dependencies: dict) -> tuple[dict[str, int], list[str]]:
    """Write the Lean's facts into the checkout's pages and annotations, and name each page whose declaration the
    Lean no longer has. Such a page loses its link here, so it builds unlinked: a Lean change that renames or
    deletes a declaration never fails the wiki's build, and `declarations` reports the page for an editor."""
    files = read_annotations()
    counts = {"articles": 0, "unresolved": 0, "edges": 0}
    unlinked: list[str] = []
    stale: list[Path] = []
    sorry_cache: dict[Path, bool] = {}

    def sorry(path: Path) -> bool:
        if path not in sorry_cache:
            source = path if path.is_absolute() else wiki.ROOT / path
            sorry_cache[path] = re.search(r"\bsorry\b", wiki.without_comments(source.read_text())) is not None
        return sorry_cache[path]

    articles: dict[Path, dict] = {}
    for rows in files.values():
        for annotation in rows:
            path = subject_path(annotation)
            if path.name == "README.md":
                continue
            name, own = lean_name(annotation), annotation.get("extensions", {}).get(OWN)
            kind, status = lean_facts_for(name, own, index, sorry)
            if kind is None:
                counts["unresolved"] += 1
                if name:
                    annotation.pop("object", None)
                    unlinked.append(f"{name} ({path.relative_to(wiki.ROADMAP)})")
                # A fact an earlier pass derived no longer holds.
                annotation.pop("kind", None)
                annotation.pop("status", None)
                stale.append(path)
                continue
            annotation["kind"] = kind
            if status:
                annotation["status"] = status
            else:
                annotation.pop("status", None)
            articles[path] = annotation
            counts["articles"] += 1
    by_name = {lean_name(a): path for path, a in articles.items() if lean_name(a)}
    for path, a in articles.items():
        resolved = None if lean_name(a) else legacy_lean_name(a.get("extensions", {}).get(OWN), index)
        if resolved:
            by_name.setdefault(resolved, path)
    # declarations marks a page it wrote with {"from": "docstring"} under OWN; only a page whose declaration the
    # index can't see also keeps its module and name there.
    def find(name: str) -> Path | None:
        return by_name.get(name)

    depends: dict[Path, tuple[list[Path], list[Path]]] = {path: ([], []) for path in articles}
    covered: set[Path] = set()
    for name, entry in dependencies.items():
        path = find(name)
        if path is None:
            continue
        covered.add(path)
        seen = set(depends[path][0] + depends[path][1])
        for kind, bucket in (("statement", depends[path][0]), ("proof", depends[path][1])):
            for dependency in entry[kind]:
                other = find(dependency)
                if other is not None and other != path and other not in seen:
                    bucket.append(other)
                    seen.add(other)
                    counts["edges"] += 1
    titles: dict[Path, str] = {}

    def title(path: Path) -> str:
        if path not in titles:
            heading = re.search(r"(?m)^# (.+)$", path.read_text())
            titles[path] = heading.group(1) if heading else path.stem
        return titles[path]

    for path, (statement, proof) in depends.items():
        if path not in covered and not lean_name(articles[path]):
            # A page with no Lean link and no compiled row: its dependencies are unknown, so no section claims none.
            body = path.read_text()
            if has_lean_sections(body):
                path.write_text(without_sections(body, LEAN_SECTIONS))
            continue
        page = path.relative_to(wiki.VAULT)

        def link(other: Path) -> str:
            return f"- [{wiki.link_text(title(other))}]({wiki.rel(page, other.relative_to(wiki.VAULT))})"

        sections = [("Depends on", [link(other) for other in statement] or ["This node has no prerequisites."])]
        if proof:
            sections.append(("Proof depends on", [link(other) for other in proof]))
        # Both Lean sections are rewritten, so a dependency that is gone leaves no section behind.
        path.write_text(with_sections(without_sections(path.read_text(), LEAN_SECTIONS), sections))
    for path in stale:
        if path.is_file():
            body = path.read_text()
            if has_lean_sections(body):
                path.write_text(without_sections(body, LEAN_SECTIONS))
    write_annotations(files)
    return counts, unlinked


def uncompiled_articles(extracted: dict, index) -> list[str]:
    """The articles the extraction found no compiled row for although the Lean sources still declare them.

    Their pages would list no dependencies, which reads as "no prerequisites", so `lean-facts` fails on them. An
    article whose declaration the sources no longer hold is not one: `apply_lean_facts` unlinks its page.
    """
    missing = {name for names in extracted.get("missing_articles", {}).values() for name in names}
    return sorted(name for name in missing if name in index.declarations)


def pages_without_rows() -> list[Path]:
    """The roadmap pages that no annotation row names. Such a page has no node and no navigation metadata, so it
    would build as a stray page: an editor gives it a row (a folder page takes its sibling folders' navigation)."""
    named = {subject_path(row) for rows in read_annotations().values() for row in rows}
    return sorted(path.resolve() for path in wiki.ROADMAP.rglob("*.md") if path.resolve() not in named)


def run_lean_facts(dependency_file: Path) -> int:
    from autoform_cli.lean import index_project

    if not dependency_file.is_file():
        # Without it every page would build with no dependencies, which looks like a site and isn't one.
        print(f"error: {dependency_file} is missing; the Pages build's dependency dump writes it", file=sys.stderr)
        return 1
    stray = pages_without_rows()
    if stray:
        for path in stray[:20]:
            print(f"error: no annotation row names {path.relative_to(wiki.ROADMAP)}", file=sys.stderr)
        print(f"error: {len(stray)} roadmap pages have no annotation row in {LINKS.relative_to(wiki.ROOT)}",
              file=sys.stderr)
        return 1
    index = index_project(wiki.ROOT, exclude_roots=("v1", "Atlas"))
    extracted = json.loads(dependency_file.read_text())
    dependencies = extracted["articles"]
    uncompiled = uncompiled_articles(extracted, index)
    if uncompiled:
        for name in uncompiled[:20]:
            print(f"error: the Lean sources declare {name}, but the compiled dependency dump has no row for it",
                  file=sys.stderr)
        print(f"error: {len(uncompiled)} articles have no compiled dependency row, so their pages would list no "
              "prerequisites", file=sys.stderr)
        return 1
    if not dependencies:
        print(f"warning: no dependencies in {dependency_file}, so no article lists any", file=sys.stderr)
    counts, unlinked = apply_lean_facts(index, dependencies)
    for page in unlinked:
        print(f"warning: the Lean no longer declares {page}, so the page builds unlinked; "
              "sync_wiki.py declarations lists it for an editor", file=sys.stderr)
    if counts["unresolved"] > len(unlinked):
        print(f"warning: {counts['unresolved'] - len(unlinked)} articles name no declaration the Lean sources hold, "
              "so they get no kind or status", file=sys.stderr)
    print(f"{counts['articles']} articles, {counts['edges']} dependency links")
    return 0


def declaration_key(target) -> str | None:
    """How the sync finds a declaration's page: its Lean name. A declaration the Lean index lacks has none, and
    gets no page (generate_wiki leaves it out and the sync reports it)."""
    return target.lean


def held_name(annotation: dict) -> str | None:
    """The declaration an annotation holds back, from `"held"` under OWN: its page states the mathematics the
    declaration fails to (it is false, vacuous or mis-specified), or the declaration is private, so the page carries no
    Lean link until the Lean is fixed and gets no second page from the declaration's docstring (see docs/BLUEPRINT.md)."""
    own = annotation.get("extensions", {}).get(OWN)
    held = own.get("held") if isinstance(own, dict) else None
    name = held.get("declaration") if isinstance(held, dict) else None
    return name if isinstance(name, str) and name else None


def held_problem(annotation: dict, key: str | None, index) -> str | None:
    """What is wrong with an annotation's held marker, if it has one: it names no declaration, the row is linked
    as well, or the Lean index does not resolve the declaration it names (renamed by its fix, say, or declared twice).
    apply_declarations also reports a held declaration that another row links or holds back."""
    own = annotation.get("extensions", {}).get(OWN)
    if not isinstance(own, dict) or "held" not in own:
        return None
    name = held_name(annotation)
    if name is None:
        return "its held marker names no declaration"
    if key:
        return f"it holds {name} back but is linked to {key}"
    if not declared(name, index):
        return f"it holds {name} back, which the Lean index does not resolve"
    return None


def annotation_key(annotation: dict, index=None) -> str | None:
    """A page's Lean name: its Lean link, or, for a page an earlier sync wrote with a module and a name only, the
    name the Lean index gives it (see legacy_lean_name); None when there is none."""
    name = lean_name(annotation)
    if name or index is None:
        return name
    return legacy_lean_name(annotation.get("extensions", {}).get(OWN), index)


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def docstring_digest(target) -> str:
    """The digest of everything a page takes from its declaration's docstring: the statement and the sources.
    A docstring without sources keeps the digest of its statement alone, as earlier baselines have it."""
    if not target.citations:
        return digest(target.description)
    return digest(target.description + "\n\nSource: " + "\n".join(target.citations))


def documented(key: str, index) -> bool | None:
    """Whether the declaration behind a page key still has a docstring; None when the index does not have it."""
    declaration = index.declarations.get(key)
    path, line = getattr(declaration, "path", None), getattr(declaration, "line", 0)
    source = wiki.ROOT / path if path is not None else None
    if source is None or not line or not source.is_file():
        return None
    lines = source.read_text().splitlines()
    if line - 1 >= len(lines):
        return None
    return wiki.docstring_before(lines, line - 1) is not None


def page_text(target) -> tuple[str, dict[str, str]]:
    """A page from a declaration's docstring, as import wrote one, and its frontmatter facts."""
    target.depends, target.proof_depends = [], []
    fields, body = split_frontmatter(wiki.render_target(target, None))
    heading, _, rest = body.partition("\n\n")
    return without_sections(f"{heading}\n\n{without_title_lead(target.title, rest)}", LEAN_SECTIONS), fields


def listed_links(readme: Path) -> list[str]:
    return [page for block in blocks(readme.read_text()) if (page := own_page(block))]


def destination(page: str) -> str:
    """What a link's destination on a folder page is: "elsewhere" when it has a scheme, of any case, starts with "/" or
    "#", or leaves the folder by a leading chain of "../" with no "." or ".." segment after it; "child" when it is a
    page of the folder (see CHILD); "part" when it is a page of one of its parts, "part-N/" and a child of it; and
    "unclear" for any other, an encoded one or one with a fragment or a query included, which might lead back into the
    folder."""
    if re.match(r"[A-Za-z][A-Za-z0-9+.-]*:|[#/]", page):
        return "elsewhere"
    if re.search(r"[%&$\\]", page):
        return "unclear"
    if CHILD.fullmatch(page):
        return "child"
    if re.fullmatch(rf"part-\d+/{CHILD.pattern}", page):
        return "part"
    rest = re.sub(r"^(?:\.\./)+", "", page)
    return "elsewhere" if rest != page and not {".", ".."} & set(re.split(r"[/#?]", rest)) else "unclear"


def own_page(block: str) -> str | None:
    """The page of its folder that an item of a folder page links first, outside code spans (see without_code), a
    "child" destination (see destination); None for any other block."""
    item = OWN_ITEM.match(without_code(block) or block)
    page = item and block[item.start(2):item.end(2)]
    return page if page and destination(page) == "child" else None


def listed_items(lines: list[str]) -> dict[str, int]:
    """The page that each simple item of a folder page's own list (see own_list and simple_item) links, by the item's
    block; the neighbours a new page is placed by."""
    return {item.group(2): number for number in own_list(lines) if (item := simple_item(lines[number], code=True))}


def listing(text: str) -> list[tuple[str, str]]:
    """A folder page's list items, each with the heading it sits under."""
    heading, items = "", []
    for row in text.split("\n"):
        if re.match(r"#{2,6} ", row):
            heading = row
        elif match := LIST_LINK.match(row):
            items.append((match.group(1), heading))
    return items


def own_list(lines: list[str]) -> dict[int, int]:
    """A folder page's own list, by block: each item that links a page of its folder (see own_page), and the block of
    the heading above it, or -1, so that two sections with one title stay two. A closing section (see CLOSING), by its
    title as the site shows it (see heading_title), and the sections within it hold none of it."""
    heading, own, closing = -1, {}, 0
    for number, row in enumerate(lines):
        if HEADING.match(row):
            heading, level = number, len(row.strip()) - len(row.strip().lstrip("#"))
            if not closing or level <= closing:
                closing = level if heading_title(row).casefold() in CLOSING else 0
        elif own_page(row) and not closing:
            own[number] = heading
    return own


def heading_title(row: str) -> str:
    """A heading's title as the site shows it, its spaces collapsed: "Related  topics" is "Related topics". A title of
    words and plain punctuation is read as written; any other, one with a "#" included, is rendered (see heading_text),
    so that "**Sources**", "`Sources`" and "Sources ##" are "Sources" while "Sources #2" keeps its "#". One the site
    would not publish is read as written."""
    title = row.strip().lstrip("#")
    if re.fullmatch(r"(?:[^\W_]|[\s,.:;'()-])*", title):
        return " ".join(title.split())
    return heading_text(row.strip()) or " ".join(title.split())


def add_to_listing(readme: Path, line: str, before: list[str] = (), after: list[str] = (), section: list[str] = ()) -> str:
    """Add a link line to a folder page. On a simple page (see simple_page): after the item linking the last of *before*
    that its own list (see own_list) holds, else ahead of the item linking the first of *after* that it holds, else at
    the end of the own list, where, if that list runs over sections, it starts a section of its own, at the level of the
    shallowest of them, after all that the last section of that level holds, the sections within it included, under the
    first of the titles in *section* whose heading the edit check passes on (see verify_edit), as one whose id another
    heading has does not. A page with no own list takes it
    ahead of its first section, such as "Related topics", or at its end. Any other page is never edited within: the
    line goes at its end, after a blank line, and "appended" is returned, so that an editor places it. If the page
    could hold raw HTML or a code fence (see uncertain), or the edit fails the check, the page is left as it is and
    "unlisted" is returned. "" otherwise. The page keeps its line ends and every byte it had."""
    text, newline = read_page(readme)
    body = text.rstrip("\n")
    href = re.search(r"\]\(([^()\s]+)\)$", line).group(1)
    if not simple_page(body, code=True):
        if uncertain(body):
            return "unlisted"
        edited = text + "\n" * max(0, 2 - (len(text) - len(body))) + line + "\n"
        if not verify_edit(text, edited, [(line, href, None)]):
            return "unlisted"
        write_page(readme, edited, newline)
        return "appended"
    lines = body.split("\n")
    own = own_list(lines)
    last = max(own, default=-1)
    end = next((i for i in range(last + 1, len(lines)) if HEADING.match(lines[i])), len(lines))
    items = listed_items(lines)
    at = next((items[link] + 1 for link in reversed(before) if link in items), None)
    if at is None:
        at = next((items[link] for link in after if link in items), None)
    new, marker = [line], ""
    if at is None:
        if section and len(set(own.values())) > 1:
            marker = min((re.match(" *(#+)", lines[heading]).group(1) for heading in set(own.values()) if heading >= 0), key=len)
            end = next((i for i in range(last + 1, len(lines))
                        if HEADING.match(lines[i]) and len(re.match(" *(#+)", lines[i]).group(1)) <= len(marker)), len(lines))
            new = [marker, "", line]
        at = last + 1 if own and not marker else end
        if at == end:
            # After all that the last section holds, apart from it unless the line joins the list it ends with.
            while at and not lines[at - 1].strip():
                at -= 1
            joins = own and not marker and LIST_ITEM.match(lines[at - 1])
            new = [""] * bool(at and not joins) + new + [""] * bool(at < len(lines) and lines[at].strip())
    for title in section if marker else [""]:
        rows = [f"{marker} {title}" if marker and row == marker else row for row in new]
        edited_lines = lines[:at] + rows + lines[at:]
        index = at + rows.index(line)
        above = [number for number in range(index) if re.match(r"#{1,6}(?: |$)", edited_lines[number])]
        under = (len(above) - 1, edited_lines[above[-1]] if above else "")
        edited = "\n".join(edited_lines) + text[len(body):]
        if verify_edit(text, edited, [(line, href, under)], added=under if marker else None):
            write_page(readme, edited, newline)
            return ""
    return "unlisted"


def section_titles(target) -> list[str]:
    """The titles the section a new page opens may take, in order: its module's title as generate_wiki gives it, but
    with its code marks kept, when Autoform's check of what the site may publish passes on its heading (see published),
    else its module's name; and its module's name, for a title whose heading id another heading has."""
    name = wiki.topic_title(target.module[-1])
    title = target.module_title if wiki.page_title(target.module_title) else name
    return list(dict.fromkeys([title if published(f"## {title}\n") is not None else name, name]))


def read_page(path: Path) -> tuple[str, str]:
    """A folder page's text, with "\n" line ends, and the line end it was written with: "\r\n" when every line end
    is one, else "\n". A page whose line ends are mixed keeps its "\r"s, which no simple page holds."""
    raw = path.read_bytes().decode("utf-8")
    if "\r\n" in raw and raw.count("\r") == raw.count("\r\n") == raw.count("\n"):
        return raw.replace("\r\n", "\n"), "\r\n"
    return raw, "\n"


def write_page(path: Path, text: str, newline: str) -> None:
    """Write a folder page's text (see read_page) with its line ends."""
    path.write_bytes(text.replace("\n", newline).encode("utf-8"))


@functools.cache
def renderer():
    """The site's Markdown, as MkDocs builds it from SITE: MkDocs' own extensions, toc, tables and fenced_code, then
    those SITE lists, with their settings."""
    import markdown
    import yaml

    class Loader(yaml.SafeLoader):
        pass

    def named(loader, name: str, node):
        module, _, attribute = name.rpartition(".")
        return getattr(importlib.import_module(module), attribute)

    Loader.add_multi_constructor("tag:yaml.org,2002:python/name:", named)
    names, settings = ["toc", "tables", "fenced_code"], {}
    for entry in yaml.load(SITE.read_text(), Loader=Loader).get("markdown_extensions", []):
        name, options = next(iter(entry.items())) if isinstance(entry, dict) else (entry, None)
        names += [name] * (name not in names)
        if options:
            settings[name] = options
    return markdown.Markdown(extensions=names, extension_configs=settings)


# Elements whose content a reader is not shown as markup, or not shown at all: code, raw text, and inert or fallback
# content.
HIDDEN = {"code", "datalist", "iframe", "noembed", "noframes", "noscript", "object", "plaintext", "pre", "script",
          "select", "style", "template", "textarea", "title", "xmp"}


@functools.lru_cache(maxsize=1024)
def published(text: str) -> str | None:
    """The text autoform render publishes for a folder page with *text*, without the header it puts on top: the page as
    Autoform's check of what the site may publish gives it, its comments dropped and its lines as Autoform reads them;
    None when that check finds anything in it, as render then publishes the page as typed, with no link or heading."""
    from autoform_cli.markdown import PAGE_HEADER
    from autoform_cli.ui.publishable import publishable_article

    visible, errors, _ = publishable_article(text)
    return None if errors else visible.removeprefix(PAGE_HEADER)


@functools.lru_cache(maxsize=1024)
def rendered(text: str) -> tuple[tuple, tuple, tuple]:
    """What Markdown text shows as the site renders it (see renderer), its HTML built into the tree a browser builds,
    with scripting on: the hrefs of its links, the level, text and id of each of its headings, and the first link, text
    and heading ordinal (-1 for none) of each of its list items. Nothing within code, raw text or an element that is not
    shown counts: see HIDDEN, and an element with a hidden attribute or a style that hides it, a dialog that is not
    open, and what a details element that is not open holds but for its summary."""
    import html5lib

    md = renderer()
    md.reset()
    tree = html5lib.HTMLParser(namespaceHTMLElements=False).parse(md.convert(text), scripting=True)
    links, headings, items = [], [], []

    def walk(node, item: list | None) -> None:
        for child in node:
            tag = child.tag if isinstance(child.tag, str) else ""
            if (tag in HIDDEN or "hidden" in child.attrib
                    or re.search(r"display\s*:\s*none|visibility\s*:\s*hidden", child.get("style", ""), re.I)
                    or tag == "dialog" and "open" not in child.attrib
                    or node.tag == "details" and "open" not in node.attrib and tag != "summary"):
                continue
            if tag == "a" and child.get("href") is not None:
                links.append(child.get("href"))
                if item is not None and item[0] is None:
                    item[0] = child.get("href")
            if re.fullmatch(r"h[1-6]", tag):
                headings.append((int(tag[1]), " ".join("".join(child.itertext()).split()), child.get("id")))
            if tag == "li":
                entry = [None, " ".join("".join(child.itertext()).split()), len(headings) - 1]
                walk(child, entry)
                items.append(tuple(entry))
            else:
                walk(child, item)

    walk(tree, None)
    return tuple(links), tuple(headings), tuple(items)


def heading(line: str) -> tuple | None:
    """The level, text and id of the one heading that *line* shows alone (see published and rendered), or None."""
    shown = published(line)
    headings = rendered(shown)[1] if shown is not None else ()
    return headings[0] if len(headings) == 1 else None


def heading_text(line: str) -> str | None:
    shown = heading(line)
    return shown[1] if shown else None


def parents(headings: list[tuple]) -> list[int]:
    """The ordinal of each heading's parent, the nearest heading above it of a higher level, or -1 for none."""
    return [next((above for above in range(number - 1, -1, -1) if headings[above][0] < level), -1)
            for number, (level, _, _) in enumerate(headings)]


def verify_edit(before: str, after: str, items: list[tuple[str, str, tuple[int, str] | None]],
                replaced: list[str] = (), added: tuple[int, str] | None = None) -> bool:
    """Whether *after*, a folder page edited from *before*, is published as meant. Autoform's check of what the site may
    publish passes on both (see published), and what each publishes, rendered as the site renders it (see rendered),
    shows: every link *before* shows, but for the hrefs in *replaced*; the headings of *before*, in order, each with its
    level, text and id, under the same parent; *added*, the ordinal and line of a heading the edit adds, with the level,
    text and id its line has alone, so that one whose id another heading's takes, before it or after, is no match, but
    for one that only the page's title, its first line, has before it, whose id then takes the suffix "_1" while the
    title keeps its own; and each of *items*, an item's line and href, with that href and as its line shows alone, in a
    list item under the heading its ordinal and line name, or anywhere if None."""
    pages = [published(text) for text in (before, after)]
    if None in pages:
        return False
    (old_links, old_headings, _), (links, headings, shown) = map(rendered, pages)
    if Counter(old_links) - Counter(replaced) - Counter(links):
        return False
    at = added[0] if added is not None else len(headings)
    if added is not None:
        alone = heading(added[1])
        if at >= len(headings) or alone is None:
            return False
        # A section named as its page: the title, its first line and the one heading before it with its id, keeps
        # that id, so the section's takes "_1" and no id moves.
        titled = (headings[at][:2] == alone[:2] and headings[at][2] == f"{alone[2]}_1" and headings[0][0] == 1
                  and [number for number in range(at) if headings[number][2] == alone[2]] == [0]
                  and re.match(r"#(?: |$)", before.lstrip("\n")))
        if headings[at] != alone and not titled:
            return False
    kept = [number for number in range(len(headings)) if number != at]
    if [headings[number] for number in kept] != list(old_headings):
        return False
    # A kept heading keeps its parent: none falls under the heading the edit adds.
    old = {number: ordinal for ordinal, number in enumerate(kept)}
    new_parents = parents(headings)
    if [old.get(new_parents[number], -1 if new_parents[number] < 0 else None) for number in kept] != parents(old_headings):
        return False
    for line, href, under in items:
        alone = published(line)
        alone = rendered(alone)[2] if alone is not None else ()
        if len(alone) != 1 or alone[0][0] != href:
            return False
        if under is None:
            if Counter(links)[href] <= Counter(old_links)[href]:
                return False
        elif (under[0] >= 0 and (under[0] >= len(headings) or headings[under[0]][1] != heading_text(under[1]))
              or (href, alone[0][1], under[0]) not in shown):
            return False
    return True


def page_heading(text: str) -> str | None:
    match = re.search(r"(?m)^# (.+)$", text)
    return match.group(1) if match else None


def folder_page(readme: Path, body: str, title) -> str:
    """A generated folder page as a run writes it: each item named as its page is titled, where title(path) is a
    page's heading, or None for a page the run doesn't write, such as a deprecated declaration's. An item or part
    heading with no page goes, and so does a heading left with nothing under it."""
    rows = []
    for row in body.split("\n"):
        link = LIST_LINK.match(row) or HEADING_LINK.match(row)
        heading = title((readme.parent / link.group(1)).resolve()) if link else ""
        if heading is None:
            continue
        rows.append(f"- [{wiki.link_text(heading)}]({link.group(1)})" if link and row.startswith("- [") else row)
    return without_empty_headings("\n".join(rows))


def without_empty_headings(text: str) -> str:
    rows = text.split("\n")
    kept = []
    for number, row in enumerate(rows):
        heading = re.match(r"(#{2,6}) ", row)
        if heading:
            rest = rows[number + 1:]
            end = next((i for i, other in enumerate(rest) if re.match(rf"#{{1,{len(heading.group(1))}}} ", other)), len(rest))
            if not any(other.strip() for other in rest[:end]):
                continue
        kept.append(row)
    return re.sub(r"\n{3,}", "\n\n", "\n".join(kept)).strip("\n") + "\n"


def blocks(text: str) -> list[str]:
    """A page's lines, each list item joined with the indented lines that continue it, and each fenced code block and
    each HTML comment that opens a line kept whole, up to the line that closes it, so that nothing in them reads as an
    item or a heading. A comment that opens within a line, as in a code span, hides no line, as in CommonMark."""
    found: list[str] = []
    commented, fence, indent = False, "", 0
    for row in text.split("\n"):
        item = found and LIST_ITEM.match(found[-1])
        continued = bool(item) and row[:1].isspace() and bool(row.strip())
        if found and (commented or fence or continued):
            found[-1] += "\n" + row
        else:
            found.append(row)
        if fence:
            fence = "" if re.match(rf" {{0,{indent + 3}}}{re.escape(fence[0])}{{{len(fence)},}}[ \t]*$", row) else fence
        elif commented:
            commented = "-->" not in row
        else:
            # A marker opens a block at most 3 spaces in, counted from the content of the item it continues, if any.
            indent = len(item.group().expandtabs(4)) if continued else 0
            if opening := re.match(rf" {{0,{indent + 3}}}(`{{3,}}(?=[^`]*$)|~{{3,}}|<!--)", row):
                fence = "" if opening.group(1) == "<!--" else opening.group(1)
                commented = opening.group(1) == "<!--" and "-->" not in row.split("<!--", 1)[1]
    return found


def without_code(row: str, strict: bool = False) -> str | None:
    """*row* with each inline code span made plain text of its length, as CommonMark pairs backtick runs: a run of n
    backticks opens a span that the next run of exactly n closes. None when a run is left open or a backslash comes
    before a backtick, and, if *strict*, when a span holds a bracket or anything else that is not plain (see PLAIN)."""
    if "\\`" in row:
        return None
    runs, out, at = list(re.finditer(r"`+", row)), [], 0
    while runs:
        opening = runs.pop(0)
        closing = next((run for run in runs if len(run.group()) == len(opening.group())), None)
        if closing is None or strict and not re.fullmatch(f"(?:{PLAIN}|`)*", row[opening.end():closing.start()]):
            return None
        out += [row[at:opening.start()], "x" * (closing.end() - opening.start())]
        at, runs = closing.end(), runs[runs.index(closing) + 1:]
    return "".join(out) + row[at:]


def simple_item(block: str, code: bool = False) -> re.Match | None:
    """The match of a simple item (see SIMPLE_ITEM), whose second group is its page; with *code*, also of one whose
    texts hold inline code spans that hide nothing of the link (see without_code), read with them made plain. An
    "unclear" page (see destination) is not simple: it could lead back into the folder."""
    plain = without_code(block, strict=True) if code else block
    item = plain and SIMPLE_ITEM.fullmatch(plain)
    page = item and block[item.start(2):item.end(2)]
    return item if item and page == item.group(2) and destination(page) != "unclear" else None


def simple_page(text: str, code: bool = False) -> bool:
    """Whether every line of a folder page has one of the forms its lists are edited among: a blank line; an ATX
    heading, with a space after its marker, and of level 1 only on the page's first line; a simple item (see
    simple_item, which *code* is passed to); or a line of plain text (see TEXT) with no backtick run left open and no
    "<" that could open HTML outside code spans. No item is next to a line of text, so that no text continues an item
    and no item breaks into text, and no character but "\n" breaks a line, as for Autoform (see published). Such a
    page's lines are its blocks."""
    if re.search("[\r\v\f\x1c-\x1e\x85\u2028\u2029]", text):
        return False
    kinds = []
    for row in text.strip("\n").split("\n"):
        plain = without_code(row)
        if not row.strip():
            kinds.append("")
        elif re.match(r"#{1,6}(?: |$)", row):
            if re.match(r"#(?: |$)", row) and kinds:
                return False
            kinds.append("#")
        elif simple_item(row, code):
            kinds.append("-")
        elif TEXT.match(row) and plain is not None and not re.search(r"<[A-Za-z/!?]", plain):
            kinds.append("text")
        else:
            return False
    return all({kind, following} != {"-", "text"} for kind, following in zip(kinds, kinds[1:]))


def uncertain(text: str) -> bool:
    """Whether a page has a line that could open raw HTML (a comment, a processing instruction, a declaration or CDATA
    included) or a code fence: one that starts, at most 3 spaces in, with "<" or with three backticks or tildes. The
    sync does not read how far such a block runs, so it adds nothing to the page, not even at its end."""
    return any(re.match(r" {0,3}(?:<|`{3}|~{3})", row) for row in text.split("\n"))


def part_entries(text: str) -> list[tuple[str, str, str]] | None:
    """A folder page's entries, as its parent copies them: the title, page and text after it of each list item that
    links a page of its folder, and of an item for each of its parts in place of the items under the part's heading.
    None when such a heading, the page (see simple_page, with no code allowed), or a list item outside the parts that
    is not a simple item linking a page of the folder is not simple, and when a part's heading has a section within it,
    whose items could read as the folder's own."""
    if not simple_page(text):
        return None
    entries, in_part = [], 0
    for block in text.split("\n"):
        part = PART_HEADING.match(block)
        if HEADING.match(block):
            level = len(re.match(" *(#+)", block).group(1))
            if in_part and level > in_part:
                return None
            in_part = level if part else 0
        if part:
            if not re.fullmatch(f"{PLAIN}+", part.group(1)):
                return None
            entries.append((*part.groups(), ""))
        elif not in_part and LIST_ITEM.match(block):
            item = simple_item(block)
            if not item or destination(item.group(2)) != "child":
                return None
            entries.append(item.groups())
    return entries


def with_part_lists(readme: Path, text: str) -> tuple[str, list[str], list[str]]:
    """A folder page whose list is split into parts, with each part's entries as the part's own page lists them, their
    pages taken from the folder page, under the heading that links the part. They replace the items there that link
    the part's pages, "part-N/" and a child of it (see destination), and only those, which must follow one another. On
    a page that is not simple (see simple_page), for a part whose heading, page or items there are not simple with no
    code allowed, whose copy runs over another block, whose heading has a section within it, or whose section has
    "part-N/" anywhere but in the copy, and when the refreshed copy does not render as meant (see verify_edit), the copy
    stays as it is, and the part is returned, by its folder, for an editor. A line of a copy the
    refresh replaces or removes that is none of the part's entries, as when a note was added there, or one more copy
    of a line than the part's entries make, is returned too, with its folder."""
    body = text.rstrip("\n")
    tail = text[len(body):]
    simple = simple_page(body, code=True)
    sections: list[list[str]] = []
    for block in blocks(body):
        if not sections or HEADING.match(block):
            sections.append([])
        sections[-1].append(block)
    changed, unrefreshed, dropped = False, [], []
    for number, section in enumerate(sections):
        part = PART_HEADING.match(section[0])
        if not (part and (readme.parent / part.group(2)).is_file()):
            continue
        folder = Path(part.group(2)).parent.as_posix()
        entries = part_entries((readme.parent / part.group(2)).read_text())
        items = [i for i, block in enumerate(section) if LIST_ITEM.match(block)]
        copied = [i for i in items if (item := simple_item(section[i])) and item.group(2) != part.group(2)
                  and item.group(2).startswith(f"{folder}/") and destination(item.group(2)) == "part"]
        apart = bool(copied) and copied[-1] - copied[0] >= len(copied)
        # A section within the part's, or a link into a part outside the copy, would be left as it is, stale or not.
        inner = sections[number + 1][0] if number + 1 < len(sections) else ""
        nested = bool(inner) and len(re.match(" *(#+)", inner).group(1)) > len(re.match(" *(#+)", section[0]).group(1))
        stray = any(re.search(r"part-\d+/", block) for i, block in enumerate(section[1:], 1) if i not in copied)
        if (not simple or entries is None or not re.fullmatch(f"{PLAIN}+", part.group(1))
                or not all(simple_item(section[i]) for i in items) or apart or nested or stray):
            unrefreshed.append((readme.parent / folder).relative_to(wiki.ROADMAP).as_posix())
            continue
        copy = [(f"- [{title}]({folder}/{page}){rest}", f"{folder}/{page}") for title, page, rest in entries]
        kept = [block for i, block in enumerate(section) if i not in copied]
        lines = [line for line, _ in copy]
        if copied:
            at = copied[0]
        elif copy:
            # No copy yet: one below the heading, a blank line on either side.
            at = 2 if len(kept) > 1 and not kept[1].strip() else 1
            follows = bool(kept[at].strip()) if at < len(kept) else number + 1 < len(sections)
            lines = [""] * (at == 1) + lines + [""] * follows
        else:
            continue
        if kept[:at] + lines + kept[at:] == section:
            continue
        refreshed = [*sections[:number], kept[:at] + lines + kept[at:], *sections[number + 1:]]
        ordinal = sum(bool(re.match(r"#{1,6}(?: |$)", block)) for other in sections[:number] for block in other)
        replaced = [href for i in copied for href in rendered(section[i])[0]]
        old, new = ("\n".join(block for other in page for block in other) + tail for page in (sections, refreshed))
        if verify_edit(old, new, [(line, href, (ordinal, section[0])) for line, href in copy], replaced):
            sections, changed = refreshed, True
            excess = Counter(section[i] for i in copied) - Counter(lines)
            dropped += [f"{(readme.parent / folder).relative_to(wiki.ROADMAP).as_posix()}: {row}" for row in excess.elements()]
        else:
            unrefreshed.append((readme.parent / folder).relative_to(wiki.ROADMAP).as_posix())
    return ("\n".join(block for other in sections for block in other) + tail if changed else text), unrefreshed, dropped


def declared(key: str, index) -> bool:
    """Whether the Lean still declares a page's declaration, documented or not."""
    return key in index.declarations


def deprecated(target) -> bool:
    """Whether a `@[deprecated]` attribute sits on the declaration's line or on the attribute lines
    just above it, the lines docstring_before passes over. The declaration is the one at the target's own
    line, so two declarations of a module that share a last name component are told apart; a target with no
    line is found by that component only when no other declaration of its module shares it."""
    source = wiki.ROOT / Path(*target.module).with_suffix(".lean")
    if not source.is_file():
        return False
    lines = source.read_text().splitlines()
    line = getattr(target, "line", 0)
    if line:
        number = line - 1
    else:
        # Not an identity lookup: a target with no line is a bare test or legacy case, found by its last component
        # only when no other declaration of its module shares it.
        short = target.names[0].split(".")[-1]
        found = [number for number, row in enumerate(wiki.code_lines(lines))
                 if (match := wiki.V2_DECLARATION.match(row)) and match.group("name").split(".")[-1] == short]
        if len(found) != 1:
            return False
        number = found[0]
    if not 0 <= number < len(lines):
        return False
    top = number
    while top > 0:
        if not lines[top - 1].strip() or lines[top - 1].lstrip().startswith("@["):
            top -= 1
            continue
        # A multi-line attribute, such as `@[deprecated foo` and `  (since := "…")]`.
        opening = wiki.attribute_opening(lines, top - 1)
        if opening is None:
            break
        top = opening
    return re.search(r"@\[[^\]]*\bdeprecated\b", "\n".join(lines[top:number + 1])) is not None


def parts(folder: Path) -> list[Path]:
    """A folder, and its parts and theirs, in order: a folder that is not split into parts alone."""
    return [folder, *(part for page in sorted(folder.glob("part-*/README.md")) if PART.fullmatch(page.parent.name)
                      for part in parts(page.parent))]


def kept_layout(folder: Path, created: dict[Path, str]) -> tuple[Path, dict[Path, Path]]:
    """The folder a page goes in that generate_wiki puts in *folder*, and generate_wiki's folder page for each folder
    on the way, by that folder's page. generate_wiki splits a folder of more than MAX_CHILDREN entries into parts,
    numbered afresh as the folder grows; a folder the wiki has keeps its layout instead, so that no page moves.
    generate_wiki's parts are passed over there, whatever their numbers: what it puts in them goes in the folder itself
    if the folder is flat, else in its last part, and a topic keeps its folder, in whichever part holds it."""
    at, laid_out, pages = wiki.ROADMAP, wiki.ROADMAP, {}
    for name in folder.relative_to(wiki.ROADMAP).parts:
        laid_out = laid_out / name
        if not (at / "README.md").is_file():
            # Below a folder the run makes, generate_wiki's layout.
            at = at / name
        elif PART.fullmatch(name):
            continue
        else:
            kept = parts(at)
            at = next((path / name for path in kept if (path / name / "README.md").is_file()
                       or path / name / "README.md" in created), kept[-1] / name)
        pages[at / "README.md"] = laid_out / "README.md"
    return (parts(at)[-1] if (at / "README.md").is_file() else at), pages


def apply_declarations(targets: list, index, generated: dict[Path, str] | None = None,
                       unindexed: list[str] | None = None) -> dict[str, list[str]]:
    """Pages for new declarations, and the report; see the module docstring. ``generated`` holds generate_wiki's
    pages by path, whose folder pages a new page's folder takes when it has none; ``unindexed`` the documented
    declarations the Lean index lacks (`path:line name`), which get no page and are reported for an editor."""
    generated = generated or {}
    # What checks an edit (see verify_edit) is built and run once before anything is written, its caches emptied so
    # that it runs, so that a module it needs that is missing, or a site configuration it cannot read, stops the run
    # with nothing written.
    published.cache_clear()
    rendered.cache_clear()
    rendered(published("") or "")
    files = read_annotations()
    keyed = [(annotation_key(a, index), a) for rows in files.values() for a in rows]
    pages = {key: subject_path(a) for key, a in keyed if key}
    problems = {id(a): problem for key, a in keyed if (problem := held_problem(a, key, index))}
    holders: dict[str, list[dict]] = defaultdict(list)
    for _, a in keyed:
        if id(a) not in problems and (name := held_name(a)):
            holders[name].append(a)
    for name, rows in holders.items():
        if name in pages:
            for a in rows:
                problems[id(a)] = f"it holds {name} back, which {pages[name].relative_to(wiki.ROADMAP)} links"
        for a in rows[1:] if name not in pages else []:
            problems[id(a)] = f"it holds {name} back, as {subject_path(rows[0]).relative_to(wiki.ROADMAP)} does"
    held = {name: subject_path(a) for _, a in keyed if (name := held_name(a)) and id(a) not in problems}
    held_problems = sorted(f"{subject_path(a).relative_to(wiki.ROADMAP)}: {problems[id(a)]}" for _, a in keyed
                           if id(a) in problems)
    current = {declaration_key(target): target for target in targets if declaration_key(target)}
    report: dict[str, list[str]] = {"added": [], "folders": [], "gone": [], "changed": [], "unindexed": [], "parts": [],
                                  "replaced": [], "appended": [], "unlisted": [],
                                  "held": sorted(f"{name} ({path.relative_to(wiki.ROADMAP)})" for name, path in held.items()),
                                  "held_problems": held_problems}
    if held_problems:
        # A marker the run cannot use could let its declaration through as a second page: write nothing.
        return report
    # A declaration the index lacks, and a page an earlier sync wrote for one, wait for an editor: no page is ever
    # keyed by a name rebuilt from the source.
    report["unindexed"] = sorted(
        [*(unindexed or []), *(f"{target.names[0]} (no Lean name)" for target in targets if not declaration_key(target))]
        + [f"{subject_path(a).relative_to(wiki.ROADMAP)} ({a['extensions'][OWN]['module']}:{a['extensions'][OWN]['name']})"
           for key, a in keyed if key is None and {"module", "name"} <= a.get("extensions", {}).get(OWN, {}).keys()])
    folders: dict[tuple[str, ...], Counter] = defaultdict(Counter)
    for key, target in current.items():
        if key in pages:
            folders[target.module][pages[key].parent] += 1
    in_source_order: dict[tuple[str, ...], list] = defaultdict(list)
    for target in sorted(targets, key=lambda target: target.idx):
        in_source_order[target.module].append(target)
    created: dict[Path, str] = {}
    for key, target in sorted(current.items()):
        if key in pages or key in held or deprecated(target):
            continue
        # Beside the module's pages: in the folder that holds most of them, or, when that folder is split into parts,
        # as a module of many pages is, in the last of its parts that holds one, so that a module whose pages share a
        # topic's parts with others' stays beside its own; else on the generated path as the wiki's folders keep it
        # (see kept_layout). A folder with no page of its own takes the folder pages generate_wiki lays out on the way
        # to it; without them, the deepest folder on the way that has one.
        if folders[target.module]:
            base, laid_out = folders[target.module].most_common(1)[0][0], {}
            while PART.fullmatch(base.name):
                base = base.parent
            order = parts(base)
            folder = max((held for held in folders[target.module] if held in order), key=order.index)
        else:
            folder, laid_out = kept_layout(target.path.parent, created)
        up, missing = folder, []
        while not (up / "README.md").is_file() and up / "README.md" not in created and up != wiki.ROADMAP:
            missing.append(up / "README.md")
            up = up.parent
        if missing and all(laid_out.get(page, page) in generated for page in missing):
            created.update((page, generated[laid_out.get(page, page)]) for page in missing)
        else:
            folder = up
        name, number = target.slug, 1
        while name in wiki.RESERVED_SLUGS or (folder / f"{name}.md").exists():
            number += 1
            name = f"{target.slug}-{number}"
        target.path = folder / f"{name}.md"
        text, fields = page_text(target)
        folder.mkdir(parents=True, exist_ok=True)
        target.path.write_text(text)
        # A new folder's page lists its pages already.
        readme = folder / "README.md"
        if readme.is_file():
            # Where generate_wiki lists the page here, else in source order among its module's pages here, each
            # with its section. A page joins a section of the folder page's own list only beside its module's pages:
            # where that list runs over sections, generate_wiki's order across modules says nothing of them.
            order = listing(generated.get(readme, ""))
            sectioned = len(set(own_list(blocks(readme.read_text())).values())) > 1
            if sectioned or target.path.name not in [entry[0] for entry in order]:
                order = [(target.path.name if other is target else pages[declaration_key(other)].name, other.sections)
                         for other in in_source_order[target.module]
                         if other is target or (there := pages.get(declaration_key(other))) and there.parent == folder]
            listed = set(listed_links(readme))
            position = [entry[0] for entry in order].index(target.path.name)
            earlier = [entry for entry in order[:position] if entry[0] in listed]
            later = [entry for entry in order[position + 1:] if entry[0] in listed]
            # Between two sections, a page joins the one it is in.
            if earlier and later and earlier[-1][1] != order[position][1] == later[0][1]:
                earlier = []
            if kind := add_to_listing(readme, f"- [{wiki.link_text(target.title)}]({target.path.name})",
                                      [entry[0] for entry in earlier], [entry[0] for entry in later],
                                      section_titles(target)):
                report[kind].append(target.path.relative_to(wiki.ROADMAP).as_posix())
        annotation: dict = {"subject": [{"type": "generic", "uri": "../" + target.path.relative_to(wiki.VAULT).as_posix()}]}
        if target.lean:
            annotation["object"] = [{"location": {"declaration": target.lean}}]
        extensions: dict = {OWN: {"from": "docstring"}}
        if "origin" in fields:
            extensions[NAMESPACE] = {"origin": fields["origin"]}
        annotation["extensions"] = extensions
        files.setdefault(links_file(target.path), []).append(annotation)
        pages[key] = target.path
        report["added"].append(f"{key} -> {target.path.relative_to(wiki.ROADMAP)}")
    def title(path: Path) -> str | None:
        if path.is_file():
            return page_heading(path.read_text()) or path.stem
        return page_heading(created[path]) if path in created else None

    for readme in sorted(created, key=lambda path: (len(path.parts), path)):
        fields, body = split_frontmatter(created[readme])
        readme.write_text(folder_page(readme, body, title))
        # A page the generated folder page doesn't list under its name, say one renamed to keep a name free, joins it.
        listed = set(listed_links(readme))
        for page in sorted(path for path in pages.values() if path.parent == readme.parent and path.name not in listed):
            if kind := add_to_listing(readme, f"- [{wiki.link_text(title(page))}]({page.name})"):
                report[kind].append(page.relative_to(wiki.ROADMAP).as_posix())
        annotation = {"subject": [{"type": "generic", "uri": "../" + readme.relative_to(wiki.VAULT).as_posix()}]}
        ours = {key: fields[key] for key in ("navigation", "area") if key in fields}
        if ours:
            annotation["extensions"] = {NAMESPACE: ours}
        files.setdefault(links_file(readme), []).append(annotation)
        report["folders"].append(readme.parent.relative_to(wiki.ROADMAP).as_posix())
        parent = readme.parent.parent / "README.md"
        if parent not in created:
            # Where generate_wiki lists the folder among the parent's.
            order = [entry[0] for entry in listing(generated.get(parent, ""))]
            link = f"{readme.parent.name}/README.md"
            position = order.index(link) if link in order else len(order)
            if kind := add_to_listing(parent, f"- [{wiki.link_text(title(readme))}]({link})", order[:position],
                                      order[position + 1:]):
                report[kind].append(readme.parent.relative_to(wiki.ROADMAP).as_posix())
    # A folder page split into parts lists each part's entries under the heading that links it, as the part lists them.
    for readme in sorted(wiki.ROADMAP.rglob("README.md")):
        text, newline = read_page(readme)
        copied, unrefreshed, dropped = with_part_lists(readme, text)
        report["parts"] += unrefreshed
        report["replaced"] += dropped
        if text != copied:
            write_page(readme, copied, newline)
    # A declaration upstream never documented keeps its page; only one the Lean no longer declares is gone.
    report["gone"] = sorted(
        f"{key} ({path.relative_to(wiki.ROADMAP)})" for key, path in pages.items() if key not in current and not declared(key, index)
    )
    before = json.loads(STATE.read_text())["docstrings"] if STATE.is_file() else None
    digests = {key: docstring_digest(target) for key, target in current.items()}
    if before is not None:
        changed = [f"{key} ({pages[key].relative_to(wiki.ROADMAP)})"
                   for key, value in digests.items() if key in before and before[key] != value and key in pages]
        # A page whose declaration lost its docstring keeps its text: it is reported, and keeps its baseline entry,
        # so that it is reported again until its docstring returns or the page goes.
        removed = [key for key in pages if key in before and key not in current and documented(key, index) is False]
        changed += [f"{key} ({pages[key].relative_to(wiki.ROADMAP)}; docstring removed)" for key in removed]
        digests.update({key: before[key] for key in removed})
        report["changed"] = sorted(changed)
    STATE.write_text(json.dumps({"docstrings": dict(sorted(digests.items()))}, indent=0, ensure_ascii=False) + "\n")
    write_annotations(files)
    return report


def refresh_catalog(generated: dict[Path, str]) -> None:
    """Refresh source-derived areas and coverage, without rewriting articles."""
    for path in (wiki.VAULT / "atlas.json", wiki.VAULT / "coverage" / "README.md"):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(generated[path])


def run_declarations() -> int:
    from autoform_cli.lean import index_project

    index = index_project(wiki.ROOT, exclude_roots=("v1", "Atlas"))
    targets: list = []
    unindexed: list[str] = []
    generated = wiki.generate(None, None, targets, index, unindexed)
    report = apply_declarations(targets, index, generated, unindexed)
    if report["held_problems"]:
        # The run stopped before writing anything: only the markers to fix are worth reporting.
        print(f"Held markers to fix: {len(report['held_problems'])}; the run wrote nothing")
        for row in report["held_problems"]:
            print(f"error: {row}; fix the marker and run again (the run wrote nothing)", file=sys.stderr)
        return 1
    refresh_catalog(generated)
    for kind, title in (("added", "New pages, taken from docstrings"), ("folders", "New folders, as the taxonomy places their modules"),
                        ("gone", "Pages whose declaration is gone"), ("changed", "Pages whose declaration's docstring changed"),
                        ("unindexed", "Declarations the Lean index lacks, and their pages, for an editor"),
                        ("parts", "Part lists not refreshed, as an entry needs an editor"),
                        ("replaced", "Lines of a part list that the refresh replaced or removed, as they differ from the "
                         "part's own entries, to check"),
                        ("appended", "New pages and folders listed at the end of a page that is not simple, to place"),
                        ("unlisted", "New pages and folders listed nowhere, as their page may hold raw HTML or code, the "
                         "site would show it as typed, or their item would not show where placed"),
                        ("held", "Declarations held back, whose pages stay unlinked until the Lean is fixed")):
        print(f"{title}: {len(report[kind])}")
        for row in report[kind]:
            print(f"  {row}")
    for row in report["unlisted"]:
        print(f"error: {row} is listed on no folder page: that page has raw HTML or a code fence, which could take in "
              "its item, the site would show the page as typed, with no link, or the item would not show where it was "
              "placed, so the sync left the page as it is; list it by hand", file=sys.stderr)
    return 1 if report["unlisted"] else 0


def main(argv: list[str]) -> int:
    if len(argv) == 3 and argv[0] == "import":
        return run_import(Path(argv[1]), Path(argv[2]))
    if len(argv) == 2 and argv[0] == "lean-facts":
        return run_lean_facts(Path(argv[1]))
    if argv == ["declarations"]:
        return run_declarations()
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
