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
docstring, beside its module's other pages and listed on their page, and marks it
as taken from the docstring. A deprecated declaration gets none: upstream is
retiring it, and the wiki may have dropped its page. It lists pages whose
declaration is gone and docstrings that changed since the last run
(scripts/wiki-sync.json keeps their digests), and changes no page that exists.
Its first run records the digests only.

import runs once, on a tree whose Lean still holds the wiki's English. TITLES.jsonl
holds checked titles, one {"file", "name", "opening", "title"} per line: a
declaration in that file under that name, whose docstring opens with "opening",
takes the title. DEPENDENCIES.json is the dependency dump the pages were last
ordered by, so every page keeps its path.

Run it with a Python that has Autoform installed (see blueprint-pages.yml).
"""

from __future__ import annotations

import hashlib
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
LEAN_SECTIONS = ("Depends on", "Proof depends on")
FRONTMATTER = re.compile(r"\A---\n(.*?)\n---\n\n?", re.S)
SECTION = re.compile(r"(?m)^## (.+)$")
# A bold run opening a body, and a stop just after it: "**Title.**", "**Title**." or "**Title**:".
BOLD_LEAD = re.compile(r"\*\*(?P<lead>[^*\n]+)\*\*(?P<stop>[.:]?)")


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
        if target and not target.lean:
            extensions[OWN] = {"module": ".".join(target.module), "name": target.names[0]}
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
    if own:
        source = wiki.ROOT / Path(*own["module"].split(".")).with_suffix(".lean")
        if source.is_file():
            for line in source.read_text().splitlines():
                match = wiki.V2_DECLARATION.match(line)
                if match and match.group("name").split(".")[-1] == own["name"]:
                    return wiki.WANTED.get(match.group("kw"), match.group("kw")), None
    return None, None


def apply_lean_facts(index, dependencies: dict) -> tuple[dict[str, int], list[str]]:
    """Write the Lean's facts into the checkout's pages and annotations, and name each page whose declaration the
    Lean no longer has. Such a page loses its link here, so it builds unlinked: a Lean change that renames or
    deletes a declaration never fails the wiki's build, and `declarations` reports the page for an editor."""
    files = read_annotations()
    counts = {"articles": 0, "unresolved": 0, "edges": 0}
    unlinked: list[str] = []
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
                continue
            annotation["kind"] = kind
            if status:
                annotation["status"] = status
            articles[path] = annotation
            counts["articles"] += 1
    by_name = {lean_name(a): path for path, a in articles.items() if lean_name(a)}
    by_short = {
        (a["extensions"][OWN]["module"], a["extensions"][OWN]["name"]): path
        for path, a in articles.items()
        if OWN in a.get("extensions", {})
    }

    def find(name: str) -> Path | None:
        module = dependencies.get(name, {}).get("module", "")
        return by_name.get(name) or by_short.get((module, name.split(".")[-1]))

    depends: dict[Path, tuple[list[Path], list[Path]]] = {path: ([], []) for path in articles}
    for name, entry in dependencies.items():
        path = find(name)
        if path is None:
            continue
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
        page = path.relative_to(wiki.VAULT)

        def link(other: Path) -> str:
            return f"- [{wiki.link_text(title(other))}]({wiki.rel(page, other.relative_to(wiki.VAULT))})"

        sections = [("Depends on", [link(other) for other in statement] or ["This node has no prerequisites."])]
        if proof:
            sections.append(("Proof depends on", [link(other) for other in proof]))
        path.write_text(with_sections(path.read_text(), sections))
    write_annotations(files)
    return counts, unlinked


def run_lean_facts(dependency_file: Path) -> int:
    from autoform_cli.lean import index_project

    if not dependency_file.is_file():
        # Without it every page would build with no dependencies, which looks like a site and isn't one.
        print(f"error: {dependency_file} is missing; the Pages build's edges job writes it", file=sys.stderr)
        return 1
    index = index_project(wiki.ROOT, exclude_roots=("v1", "Atlas"))
    dependencies = json.loads(dependency_file.read_text())["articles"]
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


def declaration_key(target) -> str:
    """How the sync finds a declaration's page: its Lean name, or its module and name when the index can't see it."""
    return target.lean or f"{'.'.join(target.module)}:{target.names[0]}"


def annotation_key(annotation: dict) -> str | None:
    name = lean_name(annotation)
    if name:
        return name
    own = annotation.get("extensions", {}).get(OWN)
    return f"{own['module']}:{own['name']}" if own else None


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def page_text(target) -> tuple[str, dict[str, str]]:
    """A page from a declaration's docstring, as import wrote one, and its frontmatter facts."""
    target.depends, target.proof_depends = [], []
    fields, body = split_frontmatter(wiki.render_target(target, None))
    heading, _, rest = body.partition("\n\n")
    return without_sections(f"{heading}\n\n{without_title_lead(target.title, rest)}", LEAN_SECTIONS), fields


def add_to_listing(readme: Path, line: str) -> None:
    """Add a link line after the page's last list item, or at its end."""
    lines = readme.read_text().rstrip("\n").split("\n")
    last = max((i for i, row in enumerate(lines) if row.startswith("- [")), default=len(lines) - 1)
    lines.insert(last + 1, line)
    readme.write_text("\n".join(lines) + "\n")


def declared(key: str, index) -> bool:
    """Whether the Lean still declares a page's declaration, documented or not."""
    if ":" not in key:
        return key in index.declarations
    module, name = key.rsplit(":", 1)
    source = wiki.ROOT / Path(*module.split(".")).with_suffix(".lean")
    return source.is_file() and any(
        (match := wiki.V2_DECLARATION.match(line)) and match.group("name").split(".")[-1] == name
        for line in source.read_text().splitlines()
    )


def deprecated(target) -> bool:
    """Whether a `@[deprecated]` attribute sits on the declaration's line or on the attribute lines
    just above it, the lines docstring_before passes over."""
    source = wiki.ROOT / Path(*target.module).with_suffix(".lean")
    if not source.is_file():
        return False
    lines = source.read_text().splitlines()
    short = target.names[0].split(".")[-1]
    for number, line in enumerate(lines):
        match = wiki.V2_DECLARATION.match(line)
        if match and match.group("name").split(".")[-1] == short:
            top = number
            while top > 0 and (not lines[top - 1].strip() or lines[top - 1].lstrip().startswith("@[")):
                top -= 1
            return any(re.search(r"@\[[^\]]*\bdeprecated\b", row) for row in lines[top:number + 1])
    return False


def apply_declarations(targets: list, index) -> dict[str, list[str]]:
    """Pages for new declarations, and the report; see the module docstring."""
    files = read_annotations()
    pages = {annotation_key(a): subject_path(a) for rows in files.values() for a in rows if annotation_key(a)}
    current = {declaration_key(target): target for target in targets}
    report: dict[str, list[str]] = {"added": [], "gone": [], "changed": []}
    folders: dict[tuple[str, ...], Counter] = defaultdict(Counter)
    for key, target in current.items():
        if key in pages:
            folders[target.module][pages[key].parent] += 1
    for key, target in sorted(current.items()):
        if key in pages or deprecated(target):
            continue
        # Beside the module's pages, else in the deepest existing folder of the generated path.
        if folders[target.module]:
            folder = folders[target.module].most_common(1)[0][0]
        else:
            folder = target.path.parent
            while not (folder / "README.md").is_file() and folder != wiki.ROADMAP:
                folder = folder.parent
        name, number = target.slug, 1
        while name in wiki.RESERVED_SLUGS or (folder / f"{name}.md").exists():
            number += 1
            name = f"{target.slug}-{number}"
        target.path = folder / f"{name}.md"
        text, fields = page_text(target)
        target.path.write_text(text)
        if (folder / "README.md").is_file():
            add_to_listing(folder / "README.md", f"- [{wiki.link_text(target.title)}]({target.path.name})")
        annotation: dict = {"subject": [{"type": "generic", "uri": "../" + target.path.relative_to(wiki.VAULT).as_posix()}]}
        if target.lean:
            annotation["object"] = [{"location": {"declaration": target.lean}}]
        extensions: dict = {OWN: {"from": "docstring"}}
        if "origin" in fields:
            extensions[NAMESPACE] = {"origin": fields["origin"]}
        if not target.lean:
            extensions[OWN].update({"module": ".".join(target.module), "name": target.names[0]})
        annotation["extensions"] = extensions
        files.setdefault(links_file(target.path), []).append(annotation)
        pages[key] = target.path
        folders[target.module][folder] += 1
        report["added"].append(f"{key} -> {target.path.relative_to(wiki.ROADMAP)}")
    # A declaration upstream never documented keeps its page; only one the Lean no longer declares is gone.
    report["gone"] = sorted(
        f"{key} ({path.relative_to(wiki.ROADMAP)})" for key, path in pages.items() if key not in current and not declared(key, index)
    )
    before = json.loads(STATE.read_text())["docstrings"] if STATE.is_file() else None
    digests = {key: digest(target.description) for key, target in current.items()}
    if before is not None:
        report["changed"] = sorted(
            f"{key} ({pages[key].relative_to(wiki.ROADMAP)})"
            for key, value in digests.items()
            if key in before and before[key] != value and key in pages
        )
    STATE.write_text(json.dumps({"docstrings": dict(sorted(digests.items()))}, indent=0, ensure_ascii=False) + "\n")
    write_annotations(files)
    return report


def run_declarations() -> int:
    from autoform_cli.lean import index_project

    index = index_project(wiki.ROOT, exclude_roots=("v1", "Atlas"))
    targets: list = []
    wiki.generate(None, None, targets, index)
    report = apply_declarations(targets, index)
    for kind, title in (("added", "New pages, taken from docstrings"), ("gone", "Pages whose declaration is gone"),
                        ("changed", "Pages whose declaration's docstring changed")):
        print(f"{title}: {len(report[kind])}")
        for row in report[kind]:
            print(f"  {row}")
    return 0


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
