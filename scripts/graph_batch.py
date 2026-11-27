#!/usr/bin/env python3
"""Make and check a graph-sync batch: the pull request that brings the wiki in step with all the Lean merged into
`main` since the last batch (docs/BLUEPRINT.md, Graph-sync batches).

    python3 scripts/graph_batch.py make [--base REV] [--bodies FILE] [--body FILE]
    python3 scripts/graph_batch.py verify REV [--bodies FILE] [--body FILE]
    python3 scripts/graph_batch.py base [REV]

make runs on a clean checkout of `main` and commits the batch on top of it: one commit that changes only
scripts/taxonomy.json, scripts/wiki-sync.json, pages and folder pages under blueprint/roadmap/ and links files under
blueprint/links/. It starts from the commit the last batch brought the graph up to, which the batch commit names in its
`Graph-sync-through:` trailer, or from --base, which may start earlier, never later. It first places the modules the
Lean added since then that nothing places (see placement_plan): as a merged pull request's `Place:` line asks, else
where the module whose declarations it took was placed, as a proof takes its wanted statement; and it drops the place
of each module that no longer exists. It links each planned page that a merged pull request's `Graph:` line names to
the one declaration that pull request adds in the page's topic and that could state it, and gives no page to the
declarations that may state a named planned page it cannot link so (see link_plan). It then runs
`sync_wiki.py declarations` scoped to every Lean change since that commit, on main's wiki with those links (see
synthetic_base), and checks the commit it made as verify does. --body writes a description for the pull request.

verify checks that a commit is such a batch, made on main's first-parent history, starting no later than where the
last batch before it ended, and exactly what make writes: its taxonomy is main's with the placement plan applied, byte
for byte, and the scoped check (`sync_wiki.py declarations --check`) finds its wiki in step, with changes that are
exactly what the sync writes once the planned pages of the link plan are linked, fresh article ids aside. Run it from
an up-to-date checkout of `main`: it runs the sync of the commit the batch was made on, which must be one of main's own
states; from a newer main, it also checks that the batch still merges into it cleanly and that the scoped check finds
nothing the merge breaks. It then prints the description it recomputes, every list in full, which the batch's
reviewer reads instead of the pull request's (--body writes it as make does, its longest lists given as counts when it
would pass BODY_LIMIT).

base prints the last batch on REV (`HEAD` by default) and the commit the next batch starts from.

make and verify read the descriptions of the pull requests merged since the base with `gh`, unless --bodies gives
them as JSON (see read_bodies). A description is untrusted text: only its `Place:` lines and the article ids of its
`Graph:` lines are read, those GitHub's rendering shows as lines of plain text (visible_lines), none of a description
edited after the merge or given with no rendering (see parse_place, graph_claims); a `Place:` line counts only for a
module that the pull request's own merge changed, that no placement covers and that has no page outside that topic
yet, under a field or subfield the taxonomy has, and an article id only for a planned page of main's wiki.

Run it with a Python that has Autoform installed, as sync_wiki.py.
"""

from __future__ import annotations

import argparse
import functools
import html.parser
import json
import os
import re
import subprocess
import sys
import tempfile
import textwrap
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

if __package__:
    from . import generate_wiki as wiki
    from . import sync_wiki as sync
else:
    import generate_wiki as wiki
    import sync_wiki as sync

TAXONOMY_PATH = "scripts/taxonomy.json"
BASE_TRAILER = "Graph-sync-base"
THROUGH_TRAILER = "Graph-sync-through"
TRAILER = re.compile(rf"({BASE_TRAILER}|{THROUGH_TRAILER}): ([0-9a-f]{{40}})")
# The first line of a batch commit's message, followed by the first 12 digits of the commit it was made on.
SUBJECT = "Sync the graph with the Lean merged up to "
REPOSITORY = "facebookresearch/atlas-lean"
MERGE = re.compile(r"Merge pull request #(\d+) from \S+")
PLACE = re.compile(r"Place:[ \t]*(.*?)[ \t]*")
GRAPH = re.compile(r"Graph:[ \t]*(.*?)[ \t]*")
# An article id on a `Graph:` line: `af_` and 24 lower-case hexadecimal digits, a word of its own.
ARTICLE = re.compile(r"(?<![0-9A-Za-z_])af_[0-9a-f]{24}(?![0-9A-Za-z_])")
# A word on a `Graph:` line that starts as an article id does, in any case, which gets a note when it is none; and a
# `Graph:` line's label in any case, which counts only as written.
ARTICLE_LIKE = re.compile(r"(?<![0-9A-Za-z_])[Aa][Ff]_[0-9A-Za-z_]*")
ANY_CASE_GRAPH = re.compile(r"(?i:graph):[ \t]*(.*?)[ \t]*")
# The kinds of a result. A planned page that records one links only a theorem or a lemma, and one that records another
# kind (sync_wiki.KINDS) states a definition, and links only a definition.
RESULT_KINDS = frozenset({"theorem", "lemma"})
# What the wiki's own extension on a planned page's row may hold for a batch to link the page: its kind and its
# counterparts, which a linked row does not carry (docs/cards.md), and its origin, which it keeps.
LINKABLE = frozenset({"kind", "counterpart", "seed"})
# The opening of a fenced code block: at most three spaces, then a run of three or more backticks or tildes.
FENCE = re.compile(r" {0,3}(`{3,}|~{3,})")
# The markers that open a list item, a quotation, a heading or a table row, whose lines GitHub shows in an element of
# their own: a line after them is read for the notes on lines left out.
BLOCK_MARKERS = re.compile(r"(?:>[ \t]?|[-*+][ \t]+|\d{1,9}[.)][ \t]+|#{1,6}[ \t]+|\|[ \t]*)*")
# Emphasis or code around a line's label, which GitHub shows as markup, not as a line of plain text: the line is read
# for the notes on lines left out too.
LABEL_MARKUP = re.compile(r"[*_`]+((?:Place|Graph):)[*_`]*")
PLACE_VALUE = re.compile(r"(?P<module>\S+)[ \t]+->[ \t]+(?P<to>\S+)(?:[ \t]+\|[ \t]+(?P<title>\S.*))?")
# The first line of a placement entry of scripts/taxonomy.json: two spaces, then the module as a JSON string.
PLACEMENT_START = re.compile(r'  "(?:[^"\\]|\\.)*": ')
# A module of the five libraries, as scripts/taxonomy.json keys it: a path of Lean identifiers, without `.lean`.
MODULE = re.compile(r"[A-Za-z0-9_]+(?:/[A-Za-z0-9_]+)+")
TITLE_LIMIT = 160
# The most characters a batch's description holds, its longest lists given as counts beyond it (describe): GitHub
# takes at most 65,536 in a pull request's, and whoever opens the pull request may add a paragraph.
BODY_LIMIT = 60000
# What a topic title from a description may not hold: Markdown and HTML that the site, a folder page or the batch's
# description would read as more than text, and GitHub's mentions and references.
UNSAFE = set("<>[]{}|`\\@#")
# Module names that say nothing of a module's topic: a topic titled after the folder holding them instead.
GENERIC = {"Basic", "Defs", "Lemmas", "Main", "Core", "Instances", "Results", "Theorems", "Statement", "Statements",
           "Definitions", "Properties", "Wanted"}
# The sync's report sections (sync_wiki.REPORT) that ask an editor for something, by kind.
EDITOR_ITEMS = ("parts", "replaced", "appended", "unlisted", "unassigned", "unindexed", "stale_duplicates")
# The identity and date of the commits made only to compare with (synthetic_base, verify_commit's merge), never pushed:
# fixed, so that they need no configured identity and the same inputs give the same commits.
LOCAL_IDENTITY = {"GIT_AUTHOR_NAME": "graph_batch.py", "GIT_AUTHOR_EMAIL": "graph-batch@example.invalid",
                  "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z", "GIT_COMMITTER_NAME": "graph_batch.py",
                  "GIT_COMMITTER_EMAIL": "graph-batch@example.invalid", "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z"}


class BatchError(RuntimeError):
    """What stops make or verify, said for whoever runs them."""


def git(*args: str, data: bytes | None = None) -> bytes:
    """What a git command run at the repository's root prints (see sync_wiki.git)."""
    return sync.git(*args, data=data)


def commit_of(rev: str) -> str:
    return git("rev-parse", "--verify", "--end-of-options", f"{rev}^{{commit}}").decode().strip()


def is_ancestor(older: str, newer: str) -> bool:
    return subprocess.run(["git", "-C", str(wiki.ROOT), "merge-base", "--is-ancestor", older, newer],
                          capture_output=True).returncode == 0


@functools.cache
def mainline(head: str) -> frozenset[str]:
    """The commits of *head*'s first-parent history: the states `main` has had, each one checked as a whole by the
    merge queue, unlike the commits of a merged pull request's branch."""
    return frozenset(git("rev-list", "--first-parent", head).decode().split())


def blob(commit: str, path: str) -> bytes | None:
    """The bytes of the file *path* at *commit*, or None if it has none there."""
    if not git("ls-tree", "--name-only", "--full-tree", commit, "--", path).strip():
        return None
    return git("cat-file", "blob", f"{commit}:{path}")


def tree_files(commit: str, *paths: str) -> set[str]:
    """Every file of *commit*, or those under *paths*, by its path from the repository's root."""
    listing = git("ls-tree", "-r", "-z", "--name-only", "--full-tree", commit, "--", *paths)
    return {os.fsdecode(path) for path in listing.split(b"\0") if path}


def changed_between(older: str, newer: str) -> list[str]:
    return sorted(os.fsdecode(path) for path in git("diff", "--name-only", "--no-renames", "-z", older, newer,
                                                    "--").split(b"\0") if path)


def batch_path(path: str) -> bool:
    """Whether a batch may change *path*: the taxonomy, or what the scoped sync writes (pages and folder pages, links
    files and the docstring baseline)."""
    return path == TAXONOMY_PATH or sync.written_by_sync(path)


def library_module(path: str) -> str | None:
    """The module a Lean file of one of the five libraries is, as scripts/taxonomy.json keys it, or None."""
    if path.endswith(".lean") and path.split("/", 1)[0] in wiki.LIBRARIES and "/" in path:
        return path.removesuffix(".lean")
    return None


def trailers(message: str) -> dict[str, str]:
    """The batch trailers a commit message gives, each once, or {} when one is missing or given twice."""
    found: dict[str, list[str]] = {}
    for line in message.splitlines():
        if match := TRAILER.fullmatch(line.strip()):
            found.setdefault(match.group(1), []).append(match.group(2))
    if set(found) != {BASE_TRAILER, THROUGH_TRAILER} or any(len(values) != 1 for values in found.values()):
        return {}
    return {key: values[0] for key, values in found.items()}


def batch_of(commit: str, head: str) -> tuple[str, str] | None:
    """(base, through) when *commit* is a batch for the `main` whose tip is *head*: one commit, whose message make
    wrote (SUBJECT, then the two trailers), on the commit its `Graph-sync-through:` trailer names, with a
    `Graph-sync-base:` trailer naming an older commit, both of them on *head*'s first-parent history (mainline), that
    changes a batch's files and nothing else."""
    parents = git("rev-list", "--parents", "-n", "1", commit).decode().split()[1:]
    message = git("log", "-1", "--format=%B", commit).decode("utf-8", "replace")
    found = trailers(message)
    if len(parents) != 1 or not found or parents[0] != found[THROUGH_TRAILER]:
        return None
    base, through = found[BASE_TRAILER], found[THROUGH_TRAILER]
    if message.splitlines()[0] != f"{SUBJECT}{through[:12]}":
        return None
    if base not in mainline(head) or through not in mainline(head) or not is_ancestor(base, through):
        return None
    changed = changed_between(through, commit)
    if not changed or not all(batch_path(path) for path in changed):
        return None
    return base, through


@functools.cache
def merged_heads(head: str) -> frozenset[str]:
    """The heads of the pull requests merged into *head*'s first-parent history, which their reviews covered: the
    second parents of its merges, not the commits within a merged branch."""
    lines = git("rev-list", "--first-parent", "--merges", "--parents", head).decode().splitlines()
    return frozenset(parts[2] for parts in (line.split() for line in lines) if len(parts) > 2)


def last_batch(head: str) -> tuple[str, str, str] | None:
    """The newest batch merged into *head*, as (its commit, its base, the commit it brought the graph up to): the head
    of a merged pull request (merged_heads) that is a batch (batch_of). Each batch is made on a main that holds the one
    before, so the first in topological order is the newest."""
    listing = git("log", "--topo-order", "--format=%H", "--fixed-strings", f"--grep={THROUGH_TRAILER}: ", head)
    for commit in listing.decode().split():
        if commit in merged_heads(head) and (found := batch_of(commit, head)):
            return (commit, *found)
    return None


def merged_pull_requests(base: str, head: str) -> list[tuple[int, str]]:
    """The pull requests the merge queue merged into main after *base*, up to *head*, oldest first: each with its merge
    commit on main's first-parent history."""
    found = []
    for line in git("log", "--first-parent", "--reverse", "--format=%H %s", f"{base}..{head}").decode().splitlines():
        commit, _, subject = line.partition(" ")
        if match := MERGE.match(subject):
            found.append((int(match.group(1)), commit))
    return found


class Body(str):
    """A merged pull request's description; whether it was edited after the merge (*edited*), when its `Place:` lines
    are left out, as no review of the merge saw them; and GitHub's rendering of it (*html*), when known, of which only
    the lines it shows as plain text count (visible_lines)."""
    edited: bool = False
    html: str | None = None


def body(text: str, edited: bool = False, rendered: str | None = None) -> Body:
    value = Body(text)
    value.edited, value.html = edited, rendered
    return value


def fetch_bodies(merged: list[tuple[int, str]]) -> dict[int, Body]:
    """The descriptions of the pull requests *merged*, read with `gh api graphql`, forty at a time, each marked when it
    was edited after the merge; one whose merge commit is not the one main has is left out."""
    bodies: dict[int, Body] = {}
    owner, name = REPOSITORY.split("/")
    for start in range(0, len(merged), 40):
        chunk = merged[start:start + 40]
        fields = " ".join(f"p{number}: pullRequest(number: {number}) {{ number body bodyHTML mergedAt lastEditedAt "
                          "mergeCommit { oid } }" for number, _ in chunk)
        query = f'query {{ repository(owner: "{owner}", name: "{name}") {{ {fields} }} }}'
        try:
            result = subprocess.run(["gh", "api", "graphql", "-f", f"query={query}"], capture_output=True, text=True)
        except FileNotFoundError:
            raise BatchError("reading the pull requests' descriptions needs `gh`, logged in; or give them with "
                             "--bodies") from None
        if result.returncode:
            raise BatchError(f"gh api graphql failed: {result.stderr.strip()}")
        found = json.loads(result.stdout)["data"]["repository"]
        for number, commit in chunk:
            pull = found.get(f"p{number}") or {}
            if (pull.get("mergeCommit") or {}).get("oid") == commit and isinstance(pull.get("body"), str):
                edited, merged_at = pull.get("lastEditedAt"), pull.get("mergedAt")
                rendered = pull.get("bodyHTML") if isinstance(pull.get("bodyHTML"), str) else ""
                bodies[number] = body(pull["body"], bool(edited and merged_at and edited > merged_at), rendered)
    return bodies


def read_bodies(path: Path) -> dict[int, Body]:
    """Descriptions given as JSON: {"<number>": {"body": "<description>", "html": "<GitHub's rendering>", "edited":
    true}}, "edited" for one edited after the merge. A description given with no rendering ({"<number>":
    "<description>"}, or no "html") places nothing: only the rendering says which lines GitHub shows."""
    data = json.loads(path.read_text(encoding="utf-8"))
    bodies = {}
    for number, value in (data.items() if isinstance(data, dict) else []):
        if isinstance(value, dict) and isinstance(value.get("body"), str):
            rendered = value.get("html") if isinstance(value.get("html"), str) else None
            bodies[int(number)] = body(value["body"], value.get("edited") is True, rendered)
        elif isinstance(value, str):
            bodies[int(number)] = body(value)
        else:
            raise BatchError(f"{path}: expected an object of pull request numbers and descriptions")
    if not isinstance(data, dict):
        raise BatchError(f"{path}: expected an object of pull request numbers and descriptions")
    return bodies


def place_lines(text: str, pattern: re.Pattern = PLACE) -> list[str]:
    """The values of a description's `Place:` lines (or `Graph:` lines, with *pattern* GRAPH), read from its Markdown,
    for the notes on lines GitHub's rendering does not show (visible_lines reads that, and only it counts): lines of
    their own, as Markdown ends lines (at a line feed or a carriage return only), indented by less than four columns,
    outside fenced code blocks and HTML comments, which the rendered description does not show as text, possibly after
    the markers of a list item, a quotation, a heading or a table row (BLOCK_MARKERS), a table row's closing pipe
    aside, and with emphasis or code around the label (LABEL_MARKUP). A fence closes only on a line of at most three spaces, a run of its own character at least as long, and
    nothing after it but spaces and tabs; a line holding `<!--` anywhere opens a comment that runs to the next `-->`."""
    found, fence, comment = [], None, False
    for line in re.split(r"\r\n|\r|\n", text):
        if comment:
            comment = "-->" not in line
            continue
        if fence:
            if re.fullmatch(rf" {{0,3}}{re.escape(fence[0])}{{{len(fence)},}}[ \t]*", line):
                fence = None
            continue
        if match := FENCE.match(line):
            fence = match.group(1)
            continue
        if "<!--" in line:
            comment = "-->" not in line[line.index("<!--") + 4:]
            continue
        if line.expandtabs(4)[:4] == "    ":
            continue  # An indented code block, or a line too deep to be one of its own.
        line = line.strip(" \t")
        line = line[BLOCK_MARKERS.match(line).end():]
        if markup := LABEL_MARKUP.match(line):
            line = markup.group(1) + line[markup.end():].rstrip("*_`")
        if match := pattern.fullmatch(line.rstrip(" \t|") if line.endswith("|") else line):
            found.append(match.group(1))
    return found


# Elements that hold no content and have no end tag.
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"}


class VisibleLines(html.parser.HTMLParser):
    """The lines of plain text of a rendered description's top-level paragraphs, split at `<br>`: what GitHub shows as
    lines of their own. A line that holds any element (a link, code, emphasis, an image), or that an element spans,
    is left out, as is everything in another element: a list, a quotation, a table, a code block, a `<details>`."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.lines: list[str] = []
        self.depth, self.inner, self.paragraph, self.tainted, self.current = 0, 0, False, False, []

    def flush(self) -> None:
        text = "".join(self.current).strip(" \t\n")
        if text and not self.tainted:
            self.lines.append(text)
        self.current, self.tainted = [], self.inner > 0

    def handle_starttag(self, tag: str, attrs) -> None:
        if self.paragraph:
            if tag == "br":
                self.flush()
                return
            self.tainted = True
            self.inner += tag not in VOID
        elif tag == "p" and self.depth == 0:
            self.paragraph, self.inner, self.tainted, self.current = True, 0, False, []
        elif tag not in VOID:
            self.depth += 1

    def handle_startendtag(self, tag: str, attrs) -> None:
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag: str) -> None:
        if self.paragraph:
            if tag == "p" and self.inner == 0:
                self.flush()
                self.paragraph = False
            elif tag not in VOID and self.inner:
                self.inner -= 1
        elif tag not in VOID and self.depth:
            self.depth -= 1

    def handle_data(self, data: str) -> None:
        if self.paragraph:
            self.current.append(data)


def visible_lines(rendered: str, pattern: re.Pattern = PLACE) -> list[str]:
    """The values of the `Place:` lines (or `Graph:` lines, with *pattern* GRAPH) that GitHub's rendering of a
    description shows as lines of plain text in a top-level paragraph (VisibleLines)."""
    parser = VisibleLines()
    parser.feed(rendered)
    parser.close()
    return [match.group(1) for line in parser.lines if (match := pattern.fullmatch(line))]


def placed_module(value: str) -> str | None:
    """The module a `Place:` line's value names, or None if it names none (parse_place)."""
    try:
        return parse_place(value)[0]
    except ValueError:
        return None


def parse_place(value: str) -> tuple[str, str, str | None]:
    """The module, field and topic title a `Place:` line gives: `<module> -> <field>`, and ` | <topic title>` after
    them when it names the topic; ValueError if it is anything else. The module is written as scripts/taxonomy.json
    keys it, a path of Lean identifiers without `.lean`, and the field as `<subject>/<field>` or
    `<subject>/<field>/<subfield>`. A title is one line of at most TITLE_LIMIT printable characters, none of UNSAFE,
    with no address (`://`), which GitHub would read as a reference.
    The error never repeats the line's text, which is untrusted."""
    match = PLACE_VALUE.fullmatch(value)
    if not match:
        raise ValueError("it is not `<module> -> <field>` or `<module> -> <field> | <topic>`")
    module, to, title = match.group("module", "to", "title")
    if not MODULE.fullmatch(module) or module.split("/", 1)[0] not in wiki.LIBRARIES:
        raise ValueError("it names no module of the five libraries, as a path without `.lean`")
    if title is not None and (len(title) > TITLE_LIMIT or not title.isprintable() or UNSAFE & set(title)
                              or "://" in title):
        raise ValueError(f"its topic is not one line of at most {TITLE_LIMIT} printable characters free of "
                         f"{''.join(sorted(UNSAFE))} and of addresses")
    return module, to, title


def default_title(head: str, module: str) -> str:
    """The topic title of a module a `Place:` line names without one: its docstring's `# ` heading, as a page title,
    else its name, as generate_wiki titles a module's page, or, for a name that says nothing (GENERIC), its folder's."""
    text = (blob(head, f"{module}.lean") or b"").decode("utf-8", "replace")
    *folder, name = module.split("/")
    return (wiki.page_title(wiki.module_heading(text))
            or wiki.topic_title(folder[-1] if name in GENERIC and len(folder) > 1 else name))


def fields_of(taxonomy: dict) -> set[str]:
    """Every place a module may go: each subject's fields and subfields, as `<subject>/<field>[/<subfield>]`."""
    found = set()
    for subject, entry in taxonomy["subjects"].items():
        for spec in entry.get("fields", []):
            found.add(f"{subject}/{spec['slug']}")
            found.update(f"{subject}/{spec['slug']}/{sub['slug']}" for sub in spec.get("subfields", []))
    return found


def placement_of(module: str, placements: dict) -> dict | None:
    """The entry that places *module*: its own, else its nearest placed folder's (generate_wiki.placement)."""
    found = wiki.placement(tuple(module.split("/")), placements)
    return found[1] if found else None


def subject_of(module: str, taxonomy: dict) -> str | None:
    """The subject an unplaced module's pages go under, in its `not-yet-classified/` folder, as generate_wiki takes it
    from its library's folder; None when the taxonomy has no such subject, and the module gets no pages."""
    library, folder = module.split("/")[:2]
    subject = wiki.LIBRARIES[library].get(folder, folder)
    return subject if subject in taxonomy["subjects"] else None


def lean_index(commit: str):
    """Autoform's index of the Lean sources of *commit*, read from git, as the scoped sync reads a base."""
    from autoform_cli.lean import index_project

    with tempfile.TemporaryDirectory(prefix="atlas-batch-") as folder:
        root = Path(folder).resolve()
        sync.extract_tree(commit, root, sync.lean_source)
        return index_project(root, exclude_roots=sync.EXCLUDED)


def in_topic(page: str, to: str, title: str) -> bool:
    """Whether a page, by path from the roadmap, sits where the placement (*to*, *title*) lays out its module's pages
    (generate_wiki.topic_node): in the topic's folder, or right in the field for a topic of one page, either of them
    possibly within one of the field's parts."""
    if not page.startswith(f"{to}/"):
        return False
    rest = page[len(to) + 1:].split("/")
    if len(rest) > 1 and re.fullmatch(r"part-\d+", rest[0]):
        rest = rest[1:]
    return len(rest) == 1 or rest[0] == wiki.slugify(title)


def module_pages(head: str, index) -> dict[str, set[str]]:
    """The pages that already stand for a declaration of each module at *head*, by path from the roadmap: those whose
    row links the declaration, holds it back or lists it as a duplicate, read as the sync reads rows."""
    pages: dict[str, set[str]] = {}
    for path in sorted(tree_files(head, "blueprint/links")):
        if not sync.LINKS_FILE.fullmatch(path):
            continue
        try:
            rows = sync.read_rows(blob(head, path).decode("utf-8"))
        except ValueError:
            continue  # The sync stops on such a file itself.
        for row in rows:
            if not isinstance(row, dict):
                continue
            try:
                names = {name for name in (sync.lean_name(row), sync.held_name(row)) if name}
                names.update(sync.duplicate_names(row))
                legacy = sync.legacy_pair(row)
                page = sync.page_name(row) if names or legacy else None
            except (ValueError, TypeError, AttributeError, KeyError):
                continue
            modules = {library_module(declaration.path.as_posix()) for name in names
                       if (declaration := index.declarations.get(name)) is not None}
            if legacy:
                # A row an earlier sync wrote with only a module and a name.
                modules.add(library_module(legacy[0].replace(".", "/") + ".lean"))
            for module in modules - {None}:
                pages.setdefault(module, set()).add(page)
    return pages


@dataclass
class Placement:
    module: str
    to: str
    title: str
    # Where it comes from: a pull request's `Place:` line ("#123") or the module whose declarations it took.
    source: str


@dataclass
class PlacementPlan:
    added: list[Placement] = field(default_factory=list)
    dropped: list[str] = field(default_factory=list)
    # The modules new since the base that stay unplaced, each with where its pages go: its subject's
    # `not-yet-classified/` folder, or nowhere for a folder with no subject.
    unplaced: list[tuple[str, str | None]] = field(default_factory=list)
    # The older modules a pull request in the range changed that get no pages, in a folder that is no subject.
    subjectless: list[str] = field(default_factory=list)
    # What an editor may want to know: `Place:` lines left out, and why; modules whose declarations came from places
    # that disagree; modules that already have pages.
    notes: list[str] = field(default_factory=list)

    def entries(self) -> dict[str, dict[str, str]]:
        return {item.module: {"to": item.to, "title": item.title} for item in self.added}


def placement_plan(base: str, head: str, bodies: dict[int, str], indexes=None) -> PlacementPlan:
    """The taxonomy changes a batch from *base* to *head* makes, before its sync.

    A module that no placement covers, neither its own nor its folder's (see placement_of), is placed:
    1. as a `Place:` line of a pull request merged in the range asks, when that pull request's merge changed the module
       and the line names a field or subfield the taxonomy has; lines that disagree about one module place it nowhere.
       A line that names no topic takes the topic of 2 when it names the same field, else the module's own title
       (default_title);
    2. else, if the module is new since *base*, where the declarations it has took their place at *base*: the module
       each of them was in at *base*, placed as the taxonomy at *head*, or else at *base*, places it, when all of them
       agree on one place and none came from an unplaced module. A proof that moves a wanted statement, with its name,
       into a new module so takes that statement's place.
    A placement never contradicts where a module's pages already are (see module_pages, in_topic): the sync moves no
    page, so a module with a page outside the topic it would get is noted and left as it is, for a graph pull request
    that moves its pages too; a proof's module, whose moved statement's page is already in that topic, is placed. A
    changed module that gets no pages, in a folder that is no subject, is listed (PlacementPlan.subjectless), and such
    a module older than the base is never placed: the scoped sync would give pages only to its new declarations. A
    `Place:` line of a description edited after the merge, or one GitHub does not show as a line of plain text, is left
    out, with a note (Body, visible_lines). A module that no
    longer exists at *head*, neither as a file nor as a folder, loses its own placement. Mathlib's entries
    (`Mathlib/...`) are not the project's modules and stay. *indexes* gives the Lean indexes of *base* and *head* (see
    lean_index), read otherwise."""
    taxonomy = json.loads(blob(head, TAXONOMY_PATH))
    old = json.loads(blob(base, TAXONOMY_PATH) or b'{"placements": {}}')
    placements, old_placements, places = taxonomy["placements"], old.get("placements", {}), fields_of(taxonomy)
    files, old_files = tree_files(head), tree_files(base)
    modules = {module for path in files if (module := library_module(path))}
    old_modules = {module for path in old_files if (module := library_module(path))}
    folders = {"/".join(path.split("/")[:end]) for path in files for end in range(1, path.count("/") + 1)}
    plan = PlacementPlan()

    @functools.cache
    def read_indexes():
        return indexes or (lean_index(base), lean_index(head))

    @functools.cache
    def pages() -> dict[str, set[str]]:
        return module_pages(head, read_indexes()[1])

    # 2 first, as 1 may take its topic.
    inherited: dict[str, tuple[str, str, str]] = {}
    unsure: dict[str, str] = {}
    new = sorted(module for module in modules - old_modules if placement_of(module, placements) is None)
    if new:
        old_index, index = read_indexes()
        names: dict[str, list[str]] = {}
        for name, declaration in index.declarations.items():
            if (module := library_module(declaration.path.as_posix())) in new:
                names.setdefault(module, []).append(name)
        for module in new:
            spots, sources = set(), set()
            for name in sorted(names.get(module, [])):
                before = old_index.declarations.get(name)
                if before is None:
                    continue
                source = before.path.with_suffix("").as_posix()
                spot = placement_of(source, placements) or placement_of(source, old_placements)
                spots.add((spot["to"], spot["title"]) if spot else None)
                sources.add(source)
            if len(spots) == 1 and None not in spots:
                (to, title), = spots
                if to in places:
                    inherited[module] = (to, title, ", ".join(sorted(sources)))
                else:
                    unsure[module] = (f"{module} is left unplaced: its declarations' place, {to}, is no field or "
                                      "subfield of the taxonomy")
            elif len(spots) > 1:
                unsure[module] = (f"{module} is left unplaced: its declarations came from modules placed differently "
                                  f"or not at all ({', '.join(sorted(sources))})")

    asked: dict[str, dict[tuple[str, str], list[int]]] = {}
    for number, commit in merged_pull_requests(base, head):
        if number not in bodies:
            continue
        # Only GitHub's rendering says which lines it shows as plain text; the Markdown's reading serves the notes.
        rendered = getattr(bodies[number], "html", None)
        written = place_lines(bodies[number])
        lines = visible_lines(rendered) if rendered is not None else []
        if not lines and not written:
            continue
        if getattr(bodies[number], "edited", False):
            plan.notes.append(f"#{number}: its `Place:` lines are left out: its description was edited after the merge")
            continue
        if rendered is None:
            plan.notes.append(f"#{number}: its `Place:` lines are left out: its rendering is not known")
            continue
        shown = {placed_module(value) for value in lines}
        if hidden := [value for value in written if (module := placed_module(value)) and module not in shown]:
            plan.notes.append(f"#{number}: {len(hidden)} `Place:` line(s) left out: GitHub does not show them as "
                              "lines of plain text")
        own = {module for path in changed_between(f"{commit}^1", commit) if (module := library_module(path))}
        for value in lines:
            try:
                module, to, title = parse_place(value)
            except ValueError as error:
                plan.notes.append(f"#{number}: a `Place:` line is left out: {error}")
                continue
            if module not in modules:
                plan.notes.append(f"#{number}: `{module}` is left unplaced: main has no such module")
            elif module not in own:
                plan.notes.append(f"#{number}: `{module}` is left unplaced: the pull request's merge does not change it")
            elif to not in places:
                plan.notes.append(f"#{number}: `{module}` is left unplaced: its line names no field or subfield of the "
                                  "taxonomy")
            elif placement_of(module, placements) is not None:
                plan.notes.append(f"#{number}: `{module}` keeps its place: the taxonomy already places it")
            else:
                if title is None:
                    title = (inherited[module][1] if module in inherited and inherited[module][0] == to
                             else default_title(head, module))
                numbers = asked.setdefault(module, {}).setdefault((to, title), [])
                if number not in numbers:
                    numbers.append(number)
    chosen: dict[str, Placement] = {}
    for module, spots in sorted(asked.items()):
        if len(spots) == 1:
            (to, title), numbers = next(iter(spots.items()))
            chosen[module] = Placement(module, to, title, ", ".join(f"#{number}" for number in numbers))
        else:
            asking = ", ".join(f"#{number}" for numbers in spots.values() for number in numbers)
            plan.notes.append(f"`{module}` is left unplaced: {asking} ask for different places")
    for module in new:
        if module not in asked and module in inherited:
            to, title, sources = inherited[module]
            chosen[module] = Placement(module, to, title, sources)
        elif module not in asked and module in unsure:
            plan.notes.append(unsure[module])
    for module, item in sorted(chosen.items()):
        elsewhere = sorted(page for page in pages().get(module, ()) if not in_topic(page, item.to, item.title))
        if module in old_modules and subject_of(module, taxonomy) is None:
            plan.notes.append(f"`{module}` is left unplaced: it is older than the batch, in a folder with no subject, so "
                              "the batch would give pages only to its new declarations; placing it is a graph pull "
                              "request that also runs the sync over the whole project")
        elif elsewhere:
            plan.notes.append(f"`{module}` is left unplaced: it already has pages outside the topic `{item.title}` of "
                              f"`{item.to}`, such as `{elsewhere[0]}`, which a placement would not move; placing it is "
                              "a graph pull request that moves them")
        else:
            plan.added.append(item)
    placed = {item.module for item in plan.added}
    plan.unplaced = [(module, subject_of(module, taxonomy)) for module in new if module not in placed]
    changed = {module for path in changed_between(base, head) if (module := library_module(path)) in modules}
    plan.subjectless = sorted(module for module in changed - set(new) - placed
                              if placement_of(module, placements) is None and subject_of(module, taxonomy) is None)
    plan.dropped = sorted(key for key in placements if key.split("/", 1)[0] in wiki.LIBRARIES
                          and key not in modules and key not in folders)
    return plan


def placement_entries(lines: list[str]) -> list[tuple[str, list[str]]]:
    """The entries of the lines of scripts/taxonomy.json's placements block, in order, each as its module and its
    lines without the comma that ends the last of them: one line, as the file writes an entry, or several, as a hand
    edit may leave one. ValueError if the lines are not such entries."""
    entries, number = [], 0
    while number < len(lines):
        if not PLACEMENT_START.match(lines[number]):
            raise ValueError(f"scripts/taxonomy.json: not a placement entry: {lines[number][:80]}")
        for last in range(number, len(lines)):
            if last > number and PLACEMENT_START.match(lines[last]):
                raise ValueError(f"scripts/taxonomy.json: a placement entry does not end before the next one: "
                                 f"{lines[number][:80]}")
            chunk = lines[number:last + 1]
            comma = chunk[-1].endswith(",")
            text = "\n".join(chunk)[:-1] if comma else "\n".join(chunk)
            try:
                entry = json.loads("{" + text + "}")
            except ValueError:
                continue
            if len(entry) == 1 and isinstance(next(iter(entry.values())), dict):
                entries.append((next(iter(entry)), chunk[:-1] + [chunk[-1][:-1] if comma else chunk[-1]]))
                number = last + 1
                break
        else:
            raise ValueError(f"scripts/taxonomy.json: a placement entry does not end: {lines[number][:80]}")
    return entries


def edit_placements(text: str, added: dict[str, dict[str, str]], dropped: list[str]) -> str:
    """scripts/taxonomy.json's *text* with the placements *added* and without those *dropped*. Each added entry is one
    line, as the file writes it, right after the entry whose module comes last before its own in plain string order,
    or first if none does: its place depends on the entries, not on when it is added, as insert_rows places a links
    file's rows. A dropped entry loses all its lines, and every other line stays as it is, an entry over several lines
    included. ValueError if the placements block cannot be read entry by entry (placement_entries)."""
    lines = text.split("\n")
    try:
        start = lines.index(' "placements": {')
        end = next(number for number in range(start + 1, len(lines)) if lines[number] in (" }", " },"))
    except (ValueError, StopIteration):
        raise ValueError("scripts/taxonomy.json has no placements block") from None
    entries = placement_entries(lines[start + 1:end])
    keys = {key for key, _ in entries}
    if overlap := sorted(keys & set(added)):
        raise ValueError(f"already placed: {', '.join(overlap)}")
    if missing := sorted(set(dropped) - keys):
        raise ValueError(f"no such placement: {', '.join(missing)}")
    kept = [(key, chunk) for key, chunk in entries if key not in set(dropped)]
    for key, spot in sorted(added.items()):
        line = f"  {json.dumps(key, ensure_ascii=False)}: {json.dumps(spot, ensure_ascii=False)}"
        at = max(((other, number) for number, (other, _) in enumerate(kept) if other < key), default=(None, -1))[1]
        kept.insert(at + 1, (key, [line]))
    block = [line for number, (_, chunk) in enumerate(kept)
             for line in chunk[:-1] + [chunk[-1] + ("," if number < len(kept) - 1 else "")]]
    edited = "\n".join(lines[:start + 1] + block + lines[end:])
    before, after = json.loads(text), json.loads(edited)
    expected = {key: value for key, value in before["placements"].items() if key not in set(dropped)} | added
    if after["placements"] != expected or {**after, "placements": None} != {**before, "placements": None}:
        raise ValueError("editing the placements changed something else")
    return edited


@dataclass
class Link:
    """A planned page a batch links: its article id and its path from the roadmap; the declaration it links, and the
    pull request whose `Graph:` line names the page; the links file of its row and the row the batch writes there
    (linked_row); and the kind the page records and the declaration's own (its Lean keyword), for the batch's reviewer
    to compare."""
    article: str
    page: str
    declaration: str
    number: int
    links_file: str
    row: dict
    kind: str = ""
    keyword: str = ""


@dataclass
class LinkPlan:
    """What a batch does for the pages that the `Graph:` lines of the pull requests it covers name (see link_plan)."""
    links: list[Link] = field(default_factory=list)
    # The planned pages it does not link, each with its path, why, and the declarations that may state it, which it
    # gives no page.
    left: list[tuple[str, str, str, list[str]]] = field(default_factory=list)
    # The other ids named, which it leaves as they are, each with the pull requests that name it and why; and those of
    # pages linked already, each with the pull requests that name it.
    unchanged: list[tuple[str, list[int], str]] = field(default_factory=list)
    linked: dict[str, list[int]] = field(default_factory=dict)
    # The descriptions whose `Graph:` lines it leaves out, and why.
    notes: list[str] = field(default_factory=list)

    @property
    def withheld(self) -> list[str]:
        """The declarations the batch gives no page, as the scoped sync's --withhold takes them."""
        return sorted({name for *_, names in self.left for name in names})


def numbered(numbers: list[int]) -> str:
    return ", ".join(f"#{number}" for number in numbers)


def graph_claims(base: str, head: str, bodies: dict[int, str]) -> tuple[dict[str, list[int]], list[str]]:
    """The article ids that the `Graph:` lines of the pull requests merged after *base*, up to *head*, name, each with
    the pull requests that name it, oldest first; and a note for each description whose ids are left out, and for
    each pull request whose description is not known, which leaves its `Place:` lines out too. A `Graph:`
    line counts as a `Place:` line does: only as GitHub's rendering shows it, as a line of plain text in a top-level
    paragraph (visible_lines), and in no description edited after its pull request merged or given with no rendering
    (Body). A word on such a line that starts as an article id does but is none (ARTICLE_LIKE), and a line whose label
    is `Graph:` in another case, get a note too."""
    claims: dict[str, list[int]] = {}
    notes = []
    for number, _ in merged_pull_requests(base, head):
        if number not in bodies:
            notes.append(f"#{number}: its `Place:` and `Graph:` lines are left out: its description is not known")
            continue
        rendered = getattr(bodies[number], "html", None)
        written = {article for value in place_lines(bodies[number], GRAPH) for article in ARTICLE.findall(value)}
        values = visible_lines(rendered, GRAPH) if rendered is not None else []
        shown = [article for value in values for article in ARTICLE.findall(value)]
        odd = [word for value in values for word in ARTICLE_LIKE.findall(value) if not ARTICLE.fullmatch(word)]
        cased = len(visible_lines(rendered, ANY_CASE_GRAPH)) - len(values) if rendered is not None else 0
        if not written and not shown and not odd and not cased:
            continue
        if getattr(bodies[number], "edited", False):
            notes.append(f"#{number}: its `Graph:` line is left out: its description was edited after the merge")
            continue
        if rendered is None:
            notes.append(f"#{number}: its `Graph:` line is left out: its rendering is not known")
            continue
        if hidden := written - set(shown):
            notes.append(f"#{number}: {len(hidden)} article id(s) of a `Graph:` line left out: GitHub does not show "
                         "them on a line of plain text")
        if odd:
            notes.append(f"#{number}: {len(odd)} word(s) of its `Graph:` line left out, such as `{odd[0][:40]}`: an "
                         "article id is `af_` and 24 lower-case hexadecimal digits")
        if cased:
            notes.append(f"#{number}: {cased} line(s) labelled as a `Graph:` line in another case left out: only "
                         "`Graph:` counts")
        for article in dict.fromkeys(shown):
            claims.setdefault(article, []).append(number)
    return claims, notes


def article_rows(head: str) -> dict[str, list[tuple[str, dict]]]:
    """The rows of *head*'s links files, by their article id, each with its file."""
    found: dict[str, list[tuple[str, dict]]] = {}
    for path in sorted(tree_files(head, "blueprint/links")):
        if not sync.LINKS_FILE.fullmatch(path):
            continue
        try:
            rows = sync.read_rows(blob(head, path).decode("utf-8"))
        except ValueError:
            continue  # The sync stops on such a file itself.
        for row in rows:
            if isinstance(row, dict) and isinstance(row.get("id"), str):
                found.setdefault(row["id"], []).append((path, row))
    return found


def page_state(head: str, row: dict) -> tuple[str, str, str | None]:
    """What a batch may do for the page of *row*, a row of *head*'s wiki whose article id a `Graph:` line names: the
    page, by path from the roadmap, then "link" for a planned page it may link; "keep" for a planned page it may not
    link, and why; "linked" for a page linked to a declaration of the project already; or "none" for any other page,
    and why. It leaves the last two as they are. A planned page is a page, not a folder page, whose row has no Lean
    link, naming a declaration or a project, and no module and name an earlier sync wrote. Linking one that is a node
    still to expand (`not_ready`) is an editor's call, who expands it or links it; so is relinking one that holds a
    declaration back (`held`), and linking one that records no kind (sync_wiki.KINDS), whose sort the batch cannot
    tell (a card's main statement, say, must be a definition or a result as its card says), one that records the kind
    `instance`, as an instance gets no page and so is never a candidate (generate_wiki), one its folder page does
    not list, which the sync would stop on once it is linked (sync_wiki.page_problems), or one whose row holds anything
    but its subject, its id and, in the wiki's own extension, LINKABLE."""
    page = "?"
    try:
        page = sync.page_name(row)
        if sync.subject_path(row) is None:
            return page, "none", "its row names no one page"
        ends = sync.lean_ends(row)
        name = sync.lean_name(row)
        flagged = sync.mathlib_flag(row) if row.get("object") else False
    except (ValueError, TypeError, AttributeError, KeyError):
        return page, "none", "its row cannot be read"
    folder, _, leaf = page.rpartition("/")
    if leaf == "README.md":
        return page, "none", "it is a folder page"
    if blob(head, f"blueprint/roadmap/{page}") is None:
        return page, "none", "its page is missing"
    if name:
        return page, "linked", f"it is linked to `{name}` already"
    if flagged:
        return page, "none", "it credits a Mathlib declaration"
    if ends.own or ends.mathlib or ends.stated_elsewhere:
        return page, "none", "its row has a Lean link already"
    if sync.legacy_pair(row):
        return page, "none", "its row names a declaration by the module and name an earlier sync wrote"
    extensions = row.get("extensions", {})
    own = extensions.get(sync.OWN, {}) if isinstance(extensions, dict) else None
    autoform = extensions.get(sync.NAMESPACE, {}) if isinstance(extensions, dict) else None
    if isinstance(autoform, dict) and autoform.get("not_ready"):
        return page, "keep", "it is a node still to expand: expanding or linking it is an editor's call"
    if isinstance(own, dict) and "held" in own:
        return page, "keep", f"it holds `{sync.held_name(row) or 'a declaration'}` back: relinking it is an editor's call"
    if recorded_kind(row) is None:
        return page, "keep", "it records no kind, so the batch cannot tell what sort of declaration states it"
    if recorded_kind(row) == "instance":
        return page, "keep", ("it records the kind `instance`, and an instance gets no page, so no candidate can state "
                              "it: linking it is an editor's call")
    readme = (blob(head, f"blueprint/roadmap/{folder}/README.md" if folder else "blueprint/roadmap/README.md")
              or b"").decode("utf-8", "replace")
    if leaf not in {listed for block in sync.blocks(readme) if (listed := sync.own_page(block))}:
        return page, "keep", "its folder page does not list it: listing and linking it are an editor's call"
    if not (set(row) <= {"subject", "id", "extensions"} and isinstance(extensions, dict)
            and set(extensions) <= {sync.OWN} and isinstance(own, dict) and set(own) <= LINKABLE):
        return page, "keep", ("its row holds more than its kind, its counterparts and its seed: linking it is an "
                              "editor's call")
    return page, "link", None


def recorded_kind(row: dict) -> str | None:
    """The kind a page's row records under the wiki's own extension, if it is one of sync_wiki.KINDS."""
    extensions = row.get("extensions")
    own = extensions.get(sync.OWN) if isinstance(extensions, dict) else None
    kind = own.get("kind") if isinstance(own, dict) else None
    return kind if isinstance(kind, str) and kind in sync.KINDS else None


def in_topic_folder(page: str, to: str, title: str) -> bool:
    """Whether a page, by path from the roadmap, sits in the folder of the topic (*to*, *title*), or in a part, a card
    or any folder within it, possibly within one of the field's parts: in_topic, but not right in the field, where any
    topic of the field could have put it."""
    if not page.startswith(f"{to}/"):
        return False
    rest = page[len(to) + 1:].split("/")
    if len(rest) > 1 and re.fullmatch(r"part-\d+", rest[0]):
        rest = rest[1:]
    return len(rest) > 1 and rest[0] == wiki.slugify(title)


def keyed_targets(commit: str, paths: set[str], taxonomy: dict, index=None) -> dict[str, tuple]:
    """The declarations a page may be keyed by in the Lean files *paths* of *commit*, as the sync reads them with
    *taxonomy* (wiki.load_library, sync_wiki.declaration_key), each with its target and whether it is deprecated
    (sync_wiki.deprecated): read from those files alone, with *index*, the Lean index of the whole commit, else theirs."""
    from autoform_cli.lean import index_project

    found: dict[str, tuple] = {}
    if not paths:
        return found
    with tempfile.TemporaryDirectory(prefix="atlas-batch-files-") as folder:
        root = Path(folder).resolve()
        sync.extract_tree(commit, root, lambda path: path in paths)
        index = index if index is not None else index_project(root, exclude_roots=sync.EXCLUDED)
        with sync.relocated(root=root):
            for library in wiki.LIBRARIES:
                if not (root / library).is_dir():
                    continue
                for target in wiki.load_library(library, index, taxonomy)[0]:
                    if key := sync.declaration_key(target):
                        found[key] = (target, sync.deprecated(target))
    return found


def page_keys(head: str, index) -> set[str]:
    """The declarations that the rows of *head*'s wiki already stand for, as the scoped sync reads them
    (sync_wiki.scoped_plan): those a row links, holds back or lists as a duplicate, which it gives no page."""
    with tempfile.TemporaryDirectory(prefix="atlas-batch-links-") as folder:
        root = Path(folder).resolve()
        sync.extract_tree(head, root, lambda path: path.startswith("blueprint/links/"))
        (root / "blueprint" / "links").mkdir(parents=True, exist_ok=True)
        with sync.relocated(vault=root / "blueprint"):
            rows, named, held, _ = sync.held_markers(sync.readable_rows(sync.read_annotations()), index)
            twins = sync.duplicate_markers(rows)[0]
    return set(named) | set(held) | set(twins)


def own_prerequisites(text: str, page: str = "page.md") -> tuple[list[str], list[str]] | None:
    """The targets of the links a page's own `## Depends on` holds, and those of its `## Proof depends on`, each in
    order and once, as Autoform's graph loader reads them (autoform_cli.graph._parse_node): headings in any case, and
    wrapped, titled and reference links, but nothing a code block or a comment holds. None when it cannot read the
    page."""
    from autoform_cli.graph import _parse_node

    parsed, _ = _parse_node(page, Path(page), text)
    if parsed is None:
        return None
    return list(dict.fromkeys(parsed.statement_targets)), list(dict.fromkeys(parsed.proof_targets))


def cut_exactly(page: str, text: str) -> bool:
    """Whether link_edits drops a page's own dependency sections exactly as Autoform reads them: what it leaves holds
    no dependency link that Autoform reads (own_prerequisites), and every other part of the page, as Autoform splits it
    (autoform_cli.markdown.article_parts), stays as it was. It does not for a heading the sync's exact match misses (in
    another case, say), or one in a code block, which the sync would cut from."""
    from autoform_cli.markdown import DEPENDENCY_SECTIONS, article_parts

    edited = sync.without_sections(text, sync.LEAN_SECTIONS) if sync.has_lean_sections(text) else text
    if own_prerequisites(edited, page) != ([], []):
        return False
    before, after = article_parts(text), article_parts(edited)
    kept = [(part.title, part.heading, part.body) for part in before.sections
            if part.title.strip().casefold() not in DEPENDENCY_SECTIONS]
    return (after.statement == before.statement
            and [(part.title, part.heading, part.body) for part in after.sections] == kept)


def linked_row(row: dict, name: str) -> dict | None:
    """*row*, a planned page's, linked to the project's declaration *name* as the sync links a page it writes
    (sync_wiki.crediting and settled): its Lean link right after its id, and without its kind and its counterparts,
    which a linked row does not carry (docs/cards.md); its other keys kept, in their order. None when no such row
    credits the declaration, as when the links folder's defaults credit otherwise."""
    ends = sync.crediting(name)
    if ends is None:
        return None
    linked: dict = {}
    for key, value in row.items():
        if key == "extensions":
            extensions = {space: dict(entries) if space == sync.OWN and isinstance(entries, dict) else entries
                          for space, entries in value.items()}
            own = extensions.get(sync.OWN)
            if isinstance(own, dict):
                for dropped in ("kind", "counterpart"):
                    own.pop(dropped, None)
                if not own:
                    del extensions[sync.OWN]
            if extensions:
                linked[key] = extensions
            continue
        linked[key] = value
        if key == "id":
            linked["object"] = ends
    return linked if sync.settled(linked, name) else None


def link_plan(base: str, head: str, bodies: dict[int, str], taxonomy: dict, indexes=None) -> LinkPlan:
    """What a batch from *base* to *head*, which writes *taxonomy*, does for the pages that the `Graph:` lines of the
    pull requests merged in between name (graph_claims). For a planned page (page_state), each pull request that names
    it has as candidates the declarations its merge adds, documents, makes public or undeprecates, compared with its
    merge's first parent, whose sort fits the kind the page records: a theorem or a lemma for a result's kind
    (RESULT_KINDS), a definition for any other. Of them, those in the page's module or topic are those whose module
    *taxonomy* places, by its own entry or its folder's, in the topic whose folder holds the page, in it or in a part,
    a card or any folder within it (in_topic_folder); a page right in a field's folder is in no topic here. The batch
    gives a page to those still pageless: those the scoped sync from *base* takes as its own and no row stands for
    (page_keys).

    The batch links the page when one pull request names it, whose candidates in its topic are exactly one declaration,
    still pageless, which may state no other page a `Graph:` line names; it then writes the page's row as linked_row
    does and drops the page's own dependency sections (link_edits). It never links a page whose own dependency
    sections link any page (own_prerequisites): the batch cannot tell whether the declaration's Lean records that
    prerequisite, as a linked page's must (docs/BLUEPRINT.md, "Leave no gaps"). Otherwise it links nothing, and gives
    no page to the pageless candidates in the page's topic, or to all the pageless candidates if none is there, of
    every pull request that names it: they are left for an editor (LinkPlan.left, LinkPlan.withheld). When the one
    candidate in the page's topic is gone or deprecated at *head*, the page is left for an editor too, with what the
    merges that took it away added to its module (successors). A planned page with no such candidate, and any other
    page a `Graph:` line names, is left as it is, and listed (LinkPlan.unchanged, LinkPlan.linked).
    *indexes* gives the Lean indexes of *base* and *head* (see lean_index), read otherwise."""
    plan = LinkPlan()
    claims, plan.notes = graph_claims(base, head, bodies)
    if not claims:
        return plan
    rows = article_rows(head)
    states: dict[str, tuple] = {}
    for article, numbers in claims.items():
        found = rows.get(article, [])
        if len(found) != 1:
            plan.unchanged.append((article, numbers, "no row has this article id" if not found
                                   else "several rows have this article id"))
            continue
        path, row = found[0]
        page, state, why = page_state(head, row)
        if state == "link":
            text = blob(head, f"blueprint/roadmap/{page}").decode("utf-8")
            prerequisites = own_prerequisites(text, page)
            if prerequisites is None:
                state, why = "keep", "Autoform cannot read its dependency sections: linking it is an editor's call"
            elif targets := list(dict.fromkeys([*prerequisites[0], *prerequisites[1]])):
                state, why = "keep", (f"its own dependency sections link {len(targets)} page(s), such as "
                                      f"`{targets[0].replace('`', '')}`, and the batch cannot tell whether the "
                                      "declaration's Lean records them: linking it is an editor's call")
            elif not cut_exactly(page, text):
                state, why = "keep", ("the batch cannot drop its own dependency sections exactly as Autoform reads them: "
                                      "linking it is an editor's call")
        if state == "linked":
            plan.linked[article] = numbers
        elif state == "none":
            plan.unchanged.append((article, numbers, why))
        else:
            states[article] = (path, row, page, state, why)
    if not states:
        return plan
    old_index, index = indexes or (lean_index(base), lean_index(head))
    merges = merged_pull_requests(base, head)
    commits = dict(merges)
    # What each merge added, as it added it.
    added: dict[int, dict[str, object]] = {}
    for number in sorted({number for article in states for number in claims[article]}):
        commit = commits[number]
        files = {path for path in changed_between(f"{commit}^1", commit) if library_module(path)}
        after, before = keyed_targets(commit, files, taxonomy), keyed_targets(f"{commit}^1", files, taxonomy)
        added[number] = {key: target for key, (target, old) in after.items()
                         if not old and (key not in before or before[key][1])}
    wanted = set().union(*(set(keys) for keys in added.values()))
    now = keyed_targets(head, {index.declarations[key].path.as_posix() for key in wanted if key in index.declarations},
                        taxonomy, index)
    then = keyed_targets(base, {old_index.declarations[key].path.as_posix() for key in wanted
                                if key in old_index.declarations}, taxonomy, old_index)
    taken = page_keys(head, index) if wanted else set()
    # The declarations the batch gives a page: keyed at head and not deprecated there, not keyed at the base unless
    # deprecated there, and with no row standing for them.
    pageless = {key for key in wanted if key in now and not now[key][1] and (key not in then or then[key][1])
                and key not in taken}

    def in_its_topic(target, page: str) -> bool:
        spot = placement_of("/".join(target.module), taxonomy["placements"])
        return spot is not None and in_topic_folder(page, spot["to"], spot["title"])

    def fits(target, kind: str | None) -> bool:
        return kind is None or (kind in RESULT_KINDS) == (target.declaration in RESULT_KINDS)

    def successors(gone: str, number: int, page: str, kind: str | None) -> list[str]:
        """What later merges made of *gone*, the candidate #*number* added, which main no longer has as it was: of the
        declarations that the merges that took it out of its module or deprecated it added to that module, those the
        batch gives a page, in the page's topic and of its sort."""
        module = "/".join(added[number][gone].module) + ".lean"
        found: set[str] = set()
        later = [commit for merged, commit in merges][[merged for merged, _ in merges].index(number) + 1:]
        for commit in later:
            if module not in changed_between(f"{commit}^1", commit):
                continue
            after, before = keyed_targets(commit, {module}, taxonomy), keyed_targets(f"{commit}^1", {module}, taxonomy)
            if gone in before and not before[gone][1] and (gone not in after or after[gone][1]):
                found.update(key for key, (_, old) in after.items() if not old and (key not in before or before[key][1]))
        at_head = keyed_targets(head, {module}, taxonomy, index) if found else {}
        at_base = keyed_targets(base, {module}, taxonomy, old_index) if found else {}
        return sorted(key for key in found if key in at_head and not at_head[key][1] and key not in taken
                      and (key not in at_base or at_base[key][1]) and fits(at_head[key][0], kind)
                      and in_its_topic(at_head[key][0], page))

    fields = fields_of(taxonomy)
    decided = {}
    for article, (path, row, page, state, why) in sorted(states.items()):
        numbers = claims[article]
        kind = recorded_kind(row)
        each = []
        for number in numbers:
            # The merge's own candidates, as it added them: later Lean can rename, deprecate or remove one, but not
            # make the choice the merge left open.
            sorts = {key: target for key, target in added[number].items() if fits(target, kind)}
            each.append((number, sorted(sorts),
                         sorted(key for key, target in sorts.items() if in_its_topic(target, page))))
        target, vanished = None, False
        if len(numbers) > 1:
            why = f"{numbered(numbers)} name it, and the batch does not choose between them" + (f"; {why}" if why else "")
            candidates = sorted({key for _, mine, near in each for key in near or mine if key in pageless})
        else:
            number, mine, near = each[0]
            candidates = [key for key in near or mine if key in pageless]
            if state == "keep":
                pass
            elif len(near) == 1 and near[0] in pageless:
                target = near[0]
            elif len(near) == 1 and (near[0] not in now or now[near[0]][1]):
                # Renamed, deprecated or removed since: what it became, which may get a page, is the editor's to judge.
                vanished, candidates = True, successors(near[0], number, page, kind)
                why = (f"`{near[0]}`, the one declaration in its topic that #{number} adds and that could state it, is "
                       "gone or deprecated on `main` now" + (", and the pull requests that took it away add these in "
                                                            "its module" if candidates else
                                                            ": compare what replaced it, if anything, with the page"))
            elif len(near) == 1:
                why = (f"#{number} adds one documented declaration in its topic that could state it, `{near[0]}`, which "
                       + ("a row stands for already" if near[0] in taken else "`main` had before this batch's base"))
            elif near:
                why = f"#{number} adds {len(near)} documented declarations in its topic that could state it"
            elif mine and re.sub(r"/part-\d+$", "", page.rpartition("/")[0]) in fields:
                why = (f"#{number} adds documented declarations that could state it, but the page sits right in a "
                       "field's folder, in no topic")
            elif mine:
                why = f"#{number} adds no documented declaration in its topic that could state it, only elsewhere"
            else:
                why = f"#{number} adds no documented declaration that could state it"
        decided[article] = (path, row, page, numbers, target, why, candidates, vanished, state)
    # A declaration that may state two pages states neither for sure.
    shared = Counter(key for *_, candidates, _, _ in decided.values() for key in candidates)
    for article, (path, row, page, numbers, target, why, candidates, vanished, state) in decided.items():
        keyword = (index.declarations[target].keyword if target in index.declarations else now[target][0].declaration
                   ) if target is not None else ""
        if target is not None and shared[target] > 1:
            target, why = None, f"`{target}`, its one candidate, may also state another page that a `Graph:` line names"
        linked = linked_row(row, target) if target is not None else None
        if target is not None and linked is None:
            target, why = None, f"no row the batch can write credits `{target}`"
        if target is not None:
            plan.links.append(Link(article, page, target, numbers[0], path, linked, recorded_kind(row) or "", keyword))
            continue
        if not (candidates or vanished) and (state == "keep" or len(numbers) > 1):
            why += ("; " + (f"#{numbers[0]} adds" if len(numbers) == 1 else f"{numbered(numbers)} add")
                    + " no candidate the batch would give a page")
        # Every reason names the pull requests that name the page.
        if not any(re.search(rf"#{number}\b", re.sub(r"`[^`]*`", "", why)) for number in numbers):
            why = f"{numbered(numbers)} name{'s' if len(numbers) == 1 else ''} it; {why}"
        if candidates or vanished:
            plan.left.append((article, page, why, candidates))
        else:
            plan.unchanged.append((article, numbers, why))
    return plan


def link_edits(head: str, links: list[Link]) -> dict[str, bytes]:
    """What the files a batch's *links* change hold then, by their path from the repository's root: each page's row,
    in its links file, as linked_row wrote it, every other byte of the file kept; and each page without its own
    `## Depends on` and `## Proof depends on` (sync_wiki.without_sections), which `sync_wiki.py lean-facts` writes from
    the Lean for a linked page, its other text kept."""
    texts: dict[str, str] = {}
    for link in links:
        page = f"blueprint/roadmap/{link.page}"
        text = blob(head, page).decode("utf-8")
        if sync.has_lean_sections(text):
            texts[page] = sync.without_sections(text, sync.LEAN_SECTIONS)
        lines, ends = sync.records(texts[link.links_file] if link.links_file in texts
                                   else blob(head, link.links_file).decode("utf-8"))
        found = [number for number, line in enumerate(lines)
                 if line.strip() and isinstance(row := json.loads(line), dict) and row.get("id") == link.article]
        if len(found) != 1:
            raise BatchError(f"{link.links_file} has {len(found)} rows with the article id {link.article}")
        lines[found[0]] = json.dumps(link.row, ensure_ascii=False)
        texts[link.links_file] = "".join(line + end for line, end in zip(lines, ends))
    return {path: text.encode("utf-8") for path, text in texts.items()}


def local_commit(tree: str, parents: list[str], message: str) -> str:
    """A commit of *tree* on *parents*, made only to compare with (LOCAL_IDENTITY)."""
    command = ["git", "-C", str(wiki.ROOT), "commit-tree", tree, *(part for parent in parents for part in ("-p", parent)),
               "-m", message]
    return subprocess.run(command, env={**os.environ, **LOCAL_IDENTITY}, capture_output=True, check=True,
                          text=True).stdout.strip()


def synthetic_base(base: str, head: str, blobs: dict[str, str]) -> str:
    """A commit that has *head*'s tree, but the Lean sources of *base* and the files *blobs* gives, by path and blob:
    the taxonomy the batch writes, and the pages and links files its links change (link_edits), each with the mode
    *head* gives it. The scoped sync run from it takes every Lean change from *base* to *head* as its own, on *head*'s
    wiki and baseline as the batch edits them before the sync, read with the taxonomy the batch writes. It is a local
    commit, never pushed."""
    with tempfile.TemporaryDirectory(prefix="atlas-batch-index-") as folder:
        environment = {**os.environ, "GIT_INDEX_FILE": str(Path(folder) / "index")}

        def run(*args: str, data: bytes | None = None) -> bytes:
            return subprocess.run(["git", "-C", str(wiki.ROOT), *args], input=data, env=environment,
                                  capture_output=True, check=True).stdout

        run("read-tree", head)
        raw = run("diff", "--raw", "--no-renames", "-z", "--no-abbrev", base, head, "--").split(b"\0")
        entries = []
        for meta, path in zip(raw[0::2], raw[1::2]):
            name = os.fsdecode(path)
            if not meta.startswith(b":") or not sync.lean_source(name):
                continue
            mode, _, sha = meta[1:].decode("ascii").split(" ")[:3]
            entries.append(f"{mode} {sha}\t{name}" if mode != "000000" else f"0 {'0' * 40}\t{name}")
        if entries:
            run("update-index", "-z", "--index-info", data="".join(f"{entry}\0" for entry in entries).encode())
        for path, sha in sorted(blobs.items()):
            mode = run("ls-files", "-s", "-z", "--", f":(literal){path}").split(b" ", 1)[0].decode() or "100644"
            run("update-index", "--cacheinfo", f"{mode},{sha},{path}")
        tree = run("write-tree").decode().strip()
    return local_commit(tree, [head], f"The tree of {head} with the Lean of {base}")


def run_sync(root: Path, base: str, report: Path, check: bool, withheld: list[str] = ()) -> tuple[int, str]:
    """Run *root*'s copy of `sync_wiki.py declarations --base BASE` (with --check when *check*), withholding the
    declarations *withheld* (LinkPlan.withheld), its output kept."""
    command = [sys.executable, str(root / "scripts" / "sync_wiki.py"), "declarations", "--base", base,
               "--report", str(report)] + (["--check"] if check else []) + [f"--withhold={name}" for name in withheld]
    result = subprocess.run(command, cwd=root, capture_output=True, text=True)
    return result.returncode, result.stdout + result.stderr


def checked_sync(root: Path, base: str, report: Path, withheld: list[str] = ()) -> tuple[dict, str]:
    """Run *root*'s scoped check from *base* (run_sync), withholding *withheld*, and return its report and output. The
    report must be this run's: *report* is removed first, so a run that stops before writing one, as on a git error, is
    refused rather than read from an earlier run; and the exit status must agree with it, 0 in step and 1 not.
    BatchError otherwise."""
    report.unlink(missing_ok=True)
    status, output = run_sync(root, base, report, check=True, withheld=withheld)
    try:
        data = json.loads(report.read_text()) if report.is_file() else None
    except ValueError:
        data = None
    if not isinstance(data, dict) or status != (0 if data.get("in_step") is True else 1):
        raise BatchError(f"the scoped check stopped (exit {status}) without a report that agrees with it. Its "
                         "output:\n" + output)
    return data, output


def report_sections(output: str) -> dict[str, list[str]]:
    """The items the sync's printed report lists under each of its sections (sync_wiki.REPORT), by kind."""
    titles = {f"{title}: ": kind for kind, title in sync.REPORT}
    found: dict[str, list[str]] = {}
    current = None
    for line in output.splitlines():
        if line.startswith("  ") and current is not None:
            found[current].append(line[2:])
            continue
        current = next((kind for title, kind in titles.items() if line.startswith(title)
                        and line[len(title):].strip().isdigit()), None)
        if current is not None:
            found.setdefault(current, [])
    return found


def status_paths() -> list[str]:
    """What the working tree and the index change from HEAD, untracked files included, by path."""
    found = git("status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none").split(b"\0")
    paths, skip = [], False
    for record in found:
        if skip:
            skip = False
            continue
        if record:
            paths.append(os.fsdecode(record[3:]))
            skip = record[:1] in (b"R", b"C")
    return sorted(paths)


def bodies_for(base: str, head: str, path: Path | None) -> dict[int, str]:
    return read_bodies(path) if path else fetch_bodies(merged_pull_requests(base, head))


def message_for(base: str, head: str, plan: PlacementPlan, report: dict, links: LinkPlan | None = None) -> str:
    """The batch commit's message, with the trailers that name its base and the commit it brings the graph up to."""
    linked = f"; {len(links.links)} planned pages linked" if links and links.links else ""
    summary = (f"Pages for the {len(report.get('missing', []))} documented declarations that the Lean merged into main "
               f"after {base[:12]}, up to {head[:12]}, left without one; {len(plan.added)} modules placed and "
               f"{len(plan.dropped)} placements of modules that no longer exist dropped{linked}. Made by "
               "scripts/graph_batch.py make.")
    return "\n".join([f"{SUBJECT}{head[:12]}", "", textwrap.fill(summary, 72), "", f"{BASE_TRAILER}: {base}",
                      f"{THROUGH_TRAILER}: {head}", ""])


def make(options) -> int:
    head = commit_of("HEAD")
    if left := status_paths():
        raise BatchError(f"make needs a clean checkout of main; it has changes: {', '.join(left[:5])}. Commit or "
                         "remove them, or make the batch in a fresh checkout")
    last = last_batch(head)
    if options.base:
        base = commit_of(options.base)
        if last is not None and not is_ancestor(base, last[2]):
            raise BatchError(f"{base} is after {last[2]}, where the last batch ended: a batch from it would skip the "
                             "Lean merged in between")
    elif last is not None:
        base = last[2]
    else:
        raise BatchError("no batch on this branch yet: give the first batch's base with --base")
    if base == head or base not in mainline(head):
        raise BatchError(f"{base} is not an older commit of this branch's first-parent history")
    print(f"Batch from {base} up to {head}.", flush=True)
    bodies = bodies_for(base, head, options.bodies)
    indexes = (lean_index(base), lean_index(head))
    plan = placement_plan(base, head, bodies, indexes)
    taxonomy = wiki.ROOT / TAXONOMY_PATH
    text = edit_placements(taxonomy.read_text(encoding="utf-8"), plan.entries(), plan.dropped)
    taxonomy.write_text(text, encoding="utf-8")
    # The planned pages the merged pull requests' `Graph:` lines name, linked before the sync, which then gives their
    # declarations no second page.
    links = link_plan(base, head, bodies, json.loads(text), indexes)
    if links.withheld:
        print(f"Withheld, so with no page, as they may state a planned page left for an editor: "
              f"{', '.join(links.withheld)}", flush=True)
    edits = link_edits(head, links.links)
    for path, data in edits.items():
        (wiki.ROOT / path).write_bytes(data)
    written = {path: git("hash-object", "-w", "--", path).decode().strip() for path in [TAXONOMY_PATH, *edits]}
    synthetic = synthetic_base(base, head, written)
    with tempfile.TemporaryDirectory(prefix="atlas-batch-report-") as folder:
        report_path = Path(folder) / "report.json"
        status, output = run_sync(wiki.ROOT, synthetic, report_path, check=False, withheld=links.withheld)
        report = json.loads(report_path.read_text()) if report_path.is_file() else {}
    print(output, end="" if output.endswith("\n") else "\n", flush=True)
    restore = "`git reset --hard` and `git clean -fd blueprint` restore the checkout"
    if status:
        raise BatchError(f"the sync stopped, and nothing is committed; {restore}. When it stops on what main already "
                         "carries, fix that on main first: every batch from here would stop the same way")
    changed = status_paths()
    if stray := [path for path in changed if not batch_path(path)]:
        raise BatchError(f"the run changed files a batch never changes: {', '.join(stray)}; nothing is committed, and "
                         f"{restore}")
    if not changed:
        print("Nothing to sync: the graph is in step with the Lean merged up to here.")
        for note in (plan.notes + [f"{module} gets no pages: its folder has no subject" for module in plan.subjectless]
                     + links.notes + [f"{article} ({page}) is left for an editor: {why}"
                                      for article, page, why, _ in links.left]):
            print(f"note: {note}")
        return 0
    git("add", "-A", "--", TAXONOMY_PATH, "scripts/wiki-sync.json", "blueprint/roadmap", "blueprint/links")
    git("commit", "-q", "--no-verify", "-F", "-", data=message_for(base, head, plan, report, links).encode())
    commit = commit_of("HEAD")
    print(f"Committed the batch as {commit}.", flush=True)
    try:
        verify_commit(commit, bodies, plan=plan, links=links)
    except BatchError as error:
        raise BatchError(f"{error}\nThe batch does not check: `git reset --hard HEAD^` takes the commit away") from None
    if options.body:
        text = describe(commit, base, head, plan, report, report_sections(output), links)
        options.body.write_text(text, encoding="utf-8")
        if text != describe(commit, base, head, plan, report, report_sections(output), links, full=True):
            print(f"The description gives its longest lists as counts, to stay within GitHub's limit ({len(text)} "
                  "characters): `verify` prints them in full.")
    return 0


@dataclass
class Verdict:
    base: str
    through: str
    plan: PlacementPlan
    # The report and the items for an editor of the sync as make runs it (run_sync, report_sections), when verify
    # recomputes what the batch does; None otherwise.
    made: tuple[dict, dict[str, list[str]]] | None = None
    links: LinkPlan = field(default_factory=LinkPlan)


def verify_commit(commit: str, bodies: dict[int, str], plan: PlacementPlan | None = None,
                  links: LinkPlan | None = None, onto: str | None = None, recompute: bool = False) -> Verdict:
    """Check that *commit* is a batch on the first-parent history of the checkout's HEAD (batch_of), that it starts no
    later than where the last batch before it ended, and that it is exactly what make writes (see the module
    docstring): its taxonomy is main's with the placement plan applied, and its wiki is what the scoped sync writes
    once the planned pages of the link plan are linked (link_plan, link_edits), withholding the declarations it
    withholds; and, given a newer main *onto*, that it still merges cleanly into it, with one entry a module in the
    taxonomy, and that the scoped check finds nothing the merge breaks there, such as a second page for a declaration
    or a link to one main no longer has; BatchError otherwise. With *recompute*, also run the sync as make does, on the
    commit the batch was made on, for what the batch does (Verdict.made)."""
    head = commit_of("HEAD")
    found = batch_of(commit, head)
    if found is None:
        raise BatchError(f"{commit} is not a batch of this checkout's main: one commit, with make's message and its "
                         f"{BASE_TRAILER} and {THROUGH_TRAILER} trailers, on the commit the second names, both commits "
                         "on main's first-parent history, that changes only a batch's files. Run verify from an "
                         "up-to-date checkout of main")
    base, through = found
    if (last := last_batch(through)) is not None and not is_ancestor(base, last[2]):
        raise BatchError(f"the batch starts at {base}, after {last[2]}, where the last batch before it ended: it skips "
                         "the Lean merged in between")
    indexes = (lean_index(base), lean_index(through)) if plan is None or links is None else None
    plan = plan or placement_plan(base, through, bodies, indexes)
    expected = edit_placements(blob(through, TAXONOMY_PATH).decode("utf-8"), plan.entries(), plan.dropped)
    actual = (blob(commit, TAXONOMY_PATH) or b"").decode("utf-8")
    if expected != actual:
        try:
            want, have = json.loads(expected)["placements"], json.loads(actual)["placements"]
            differ = sorted(key for key in want.keys() | have.keys() if want.get(key) != have.get(key))
        except (ValueError, KeyError, TypeError):
            differ = []
        raise BatchError("the batch's scripts/taxonomy.json is not main's with the placement plan applied: "
                         + (f"the entries of {', '.join(differ[:10])} differ" if differ else "its bytes differ")
                         + ". If a merged pull request's description changed since make read it, make a new batch")
    links = links or link_plan(base, through, bodies, json.loads(actual), indexes)
    edits = link_edits(through, links.links)
    blobs = {TAXONOMY_PATH: git("rev-parse", f"{commit}:{TAXONOMY_PATH}").decode().strip()}
    blobs.update({path: git("hash-object", "-w", "--stdin", data=data).decode().strip() for path, data in edits.items()})
    synthetic = synthetic_base(base, through, blobs)
    merged = None
    if onto is not None:
        result = subprocess.run(["git", "-C", str(wiki.ROOT), "merge-tree", "--write-tree", "--no-messages", onto,
                                 commit], capture_output=True, text=True)
        if result.returncode:
            raise BatchError(f"the batch no longer merges cleanly into {onto}: make a new batch from a fresh main")
        tree = result.stdout.split()[0]
        try:
            sync.STRICT_JSON.decode(git("cat-file", "blob", f"{tree}:{TAXONOMY_PATH}").decode("utf-8"))
        except ValueError as error:
            raise BatchError(f"merged into {onto}, the batch leaves scripts/taxonomy.json unreadable ({error}): make a "
                             "new batch from a fresh main") from None
        merged = local_commit(tree, [onto, commit], f"The batch {commit} merged into {onto}")
    with tempfile.TemporaryDirectory(prefix="atlas-batch-verify-") as folder:
        tree = Path(folder) / "tree"
        git("worktree", "add", "-q", "--detach", str(tree), commit)
        try:
            report, output = checked_sync(tree, synthetic, Path(folder) / "batch-report.json", links.withheld)
            if report.get("in_step") is not True or report.get("wiki_changes") not in ("sync", "none"):
                raise BatchError("the scoped check does not find the batch's wiki exactly the sync's, in step. Its "
                                 "output:\n" + output)
            if merged is not None:
                subprocess.run(["git", "-C", str(tree), "checkout", "-q", "--detach", merged], check=True,
                               capture_output=True)
                try:
                    onto_report, output = checked_sync(tree, onto, Path(folder) / "merge-report.json")
                except BatchError as error:
                    raise BatchError(f"merged into {onto}, the batch could not be checked: {error}") from None
                if onto_report.get("in_step") is not True:
                    raise BatchError(f"merged into {onto}, the batch breaks what the scoped check reads: make a new "
                                     "batch from a fresh main. Its output:\n" + output)
            made = None
            if recompute:
                subprocess.run(["git", "-C", str(tree), "checkout", "-q", "--detach", through], check=True,
                               capture_output=True)
                (tree / TAXONOMY_PATH).write_bytes(git("cat-file", "blob", f"{commit}:{TAXONOMY_PATH}"))
                for path, data in edits.items():
                    (tree / path).write_bytes(data)
                made_path = Path(folder) / "made-report.json"
                status, output = run_sync(tree, synthetic, made_path, check=False, withheld=links.withheld)
                if status or not made_path.is_file():
                    raise BatchError(f"running the sync as make does stopped (exit {status}). Its output:\n" + output)
                made = (json.loads(made_path.read_text()), report_sections(output))
        finally:
            git("worktree", "remove", "--force", str(tree))
    print(f"{commit} is the batch from {base} up to {through}: its taxonomy is main's with the placement plan "
          "applied, and its wiki is in step, exactly what the sync writes"
          + (f" once the {len(links.links)} planned pages of the link plan are linked" if links.links else "")
          + (f", withholding {len(links.withheld)} declarations" if links.withheld else "") + "."
          + (f" It merges cleanly into {onto}, and the scoped check finds nothing the merge breaks." if onto else ""))
    return Verdict(base, through, plan, made, links)


def reason_kind(why: str) -> str:
    """*why*, the reason a page that a `Graph:` line names is left as it is, without what is that page's own, for
    describe's short form to count the pages by the kind of reason: the pages its own dependency sections link, the
    pages and declarations it names in code (a value with a `.` or a `/`; `main` or `instance` stays), and the numbers
    of pull requests and of pages. No backtick stays, as in the full form."""
    why = re.sub(r"link \d+ page\(s\), such as `[^`]*`", "link other pages", why)
    why = re.sub(r"#\d+(?:, #\d+)*", "#N", re.sub(r"`[^`]*[./][^`]*`", "…", why))
    return re.sub(r"\b\d+\b", "N", why).replace("`", "")


# Short names for the reasons a planned page is left for an editor (link_plan), each found by a phrase that only its
# reason holds, for the short form of that list (describe). A reason may hold more than one, as one that several pull
# requests name says why its page is kept too; one that holds none is given by its kind (reason_kind).
LEFT_KINDS = (("does not choose between them", "several pull requests name it"),
              ("is a node still to expand", "a node still to expand"),
              ("back: relinking it", "it holds a declaration back"),
              ("records no kind", "it records no kind"),
              ("records the kind `instance`", "it records the kind instance"),
              ("its folder page does not list it", "its folder page does not list it"),
              ("its row holds more than", "its row holds more than its kind, counterparts and seed"),
              ("Autoform cannot read", "Autoform cannot read it"),
              ("own dependency sections link", "its own dependency sections link pages"),
              ("cannot drop its own dependency sections", "its dependency sections cannot be cut as Autoform reads them"),
              ("is gone or deprecated on `main` now", "its one candidate is gone or deprecated"),
              ("documented declarations in its topic", "several candidates in its topic"),
              ("right in a field's folder", "it sits right in a field's folder"),
              ("only elsewhere", "its candidates are all outside its topic"),
              ("may also state another page", "its one candidate may state another page"),
              ("no row the batch can write credits", "no row the batch can write credits its candidate"))


def left_line(page: str, why: str, names: list[str]) -> str:
    """The line of the short form of the planned pages left for an editor (describe) for *page*, left for *why*, with
    *names* given no page: the page, the pull requests that name it (outside code, *why* names them all, as link_plan
    gives every reason), the short names of its reason (LEFT_KINDS) and how many declarations it gives no page."""
    numbers = dict.fromkeys(int(number) for number in re.findall(r"#(\d+)\b", re.sub(r"`[^`]*`", "", why)))
    kind = ("; ".join(label for phrase, label in LEFT_KINDS if phrase in why)
            or reason_kind(re.sub(r"^#\d+(?:, #\d+)* names? it; ", "", why)))
    return f"- `{page}`, {numbered(list(numbers))}: {kind}" + (f"; {len(names)} given no page" if names else "")


def describe(commit: str, base: str, head: str, plan: PlacementPlan, report: dict,
             sections: dict[str, list[str]], links: LinkPlan | None = None, full: bool = False) -> str:
    """A description for the batch's pull request, in Markdown. Every value in it is the repository's, a description's
    line that parse_place checked, or an article id of a `Graph:` line, which ARTICLE matched.

    While the description would pass BODY_LIMIT characters, which fits GitHub's limit with room to spare, the list
    whose short form saves the most gives way to it, one list at a time: how many entries the list holds, and a pointer
    to `verify`, which prints the description with every list in full (*full*). The planned pages left for an editor,
    the only record of the declarations a batch withholds, give way last, once no other list can, and only to a line a
    page (left_line)."""
    links = links or LinkPlan()
    missing = report.get("missing", [])
    modules: dict[str, int] = {}
    for key in missing:
        modules[report["new"][key]] = modules.get(report["new"][key], 0) + 1
    folders = sum(1 for path in changed_between(head, commit)
                  if path.startswith("blueprint/roadmap/") and path.endswith("/README.md"))
    digests = report.get("digests", {})
    recorded = sum(1 for value in digests.values() if value is not None)
    unrecorded = [page for page in report.get("changed", []) if page.split(" (", 1)[0] in digests]
    pointer = f"`python3 scripts/graph_batch.py verify {commit}`, run from a checkout of `main`, prints them all."
    lines = ["Graph: batch", "",
             f"Pages for the documented declarations that the Lean merged into `main` after `{base}`, up to `{head}`, "
             "left without one, made by `scripts/graph_batch.py make` "
             "([Graph-sync batches](docs/BLUEPRINT.md#graph-sync-batches)).", "",
             f"- {len(missing)} new pages, for declarations of {len(modules)} modules; {folders} folder pages written "
             f"or extended; {recorded} docstring digests written and {len(digests) - recorded} dropped.",
             f"- {len(plan.added)} modules placed in `scripts/taxonomy.json`, {len(plan.dropped)} placements of modules "
             "that no longer exist dropped."]
    if links.links or links.left:
        lines.append(f"- {len(links.links)} planned pages that merged pull requests' `Graph:` lines name linked to a "
                     f"declaration; {len(links.left)} left for an editor, and {len(links.withheld)} declarations that "
                     "may state them given no page.")
    lines.append("")
    # Each list: its lines in full, and the lines that stand for it in a description too long for GitHub.
    parts: list[tuple[list[str], list[str]]] = []

    def part(title: str, intro: list[str], body: list[str], short: str | list[str], last: bool = False) -> None:
        """A list, which gives way to *short*: a line, which the pointer to `verify` follows, or lines of their own;
        once no other list can, if *last*."""
        heading = [f"### {title}", ""]
        parts.append((heading + intro + body + [""],
                      heading + (short if isinstance(short, list) else [f"{short} {pointer}"]) + [""], last))

    if plan.added:
        part("Placements", [], ["| Module | Field | Topic | From |", "| --- | --- | --- | --- |"]
             + [f"| `{item.module}` | `{item.to}` | `{item.title}` | {item.source} |" for item in plan.added],
             f"{len(plan.added)} modules placed, too many to list here:")
    if plan.dropped:
        part("Placements dropped", [], [f"- `{key}`" for key in plan.dropped],
             f"{len(plan.dropped)} placements dropped, too many to list here:")
    if links.links:
        part("Planned pages linked", [
            "A merged pull request's `Graph:` line names each of these planned pages, and the pull request adds one "
            "documented declaration in the page's topic that could state it, which the batch links. The page keeps its "
            "article id and its text, whose own `## Depends on` and `## Proof depends on` link nothing; its recorded "
            "kind and counterparts go, and so do those sections, which `sync_wiki.py lean-facts` writes for a linked "
            "page from the Lean. Compare each page with its declaration:", ""],
            [f"- linked `{link.article}` (kind `{link.kind}`) to `{link.declaration}` (a Lean `{link.keyword}`), from "
             f"#{link.number}'s `Graph:` line: `{link.page}`" for link in links.links],
            f"{len(links.links)} planned pages linked, too many to list here; compare each with its declaration:")
    if links.left:
        def intro(shown: str, end: str) -> list[str]:
            return [f"A merged pull request's `Graph:` line names each of these planned pages, and the batch cannot "
                    f"tell which declaration states it: it links none, and gives no page to the declarations {shown}, "
                    "which may state it. An editor links the page to the one that does, in a graph pull request; a batch "
                    "made after it with `--base` set to this one's base gives the others their pages. Until then, a "
                    "later batch may link the page to a later pull request's declaration, and those "
                    f"{shown} here then get their pages only from such a batch "
                    f"([Graph-sync batches](docs/BLUEPRINT.md#graph-sync-batches)){end}", ""]

        # Given way last, and then to a line a page: the list is the only record of what the batch withholds.
        part("Planned pages left for an editor", intro("listed", ":"),
             [f"- `{article}` (`{page}`): {why}" + ("; given no page: " + ", ".join(f"`{name}`" for name in names)
                                                   if names else "") for article, page, why, names in links.left],
             intro("counted", ". A line a page gives the pull requests that name it, the short names of its reason and "
                              f"how many declarations it gives no page, too many to name here: {pointer}")
             + [left_line(page, why, names) for _, page, why, names in links.left], last=True)
    if plan.unplaced:
        part("New modules left unplaced", [
            "Nothing placed them: they had no `Place:` line and took no placed module's declarations, or the notes "
            "below say why not. Placing one is a graph pull request that moves its pages; for one with no pages, in a "
            "folder with no subject, it also runs the whole-project sync, which writes them "
            "([Maintaining articles](docs/BLUEPRINT.md#maintaining-articles)):", ""],
            [f"- `{module}`: " + (f"in `{subject}/not-yet-classified/`" if subject else
                                  "**no pages**, as its folder has no subject") for module, subject in plan.unplaced],
            f"{len(plan.unplaced)} new modules left unplaced, {sum(1 for _, subject in plan.unplaced if not subject)} "
            "of them with no pages, as their folder has no subject, too many to list here:")
    if plan.subjectless:
        part("Changed modules with no pages", [
            "Their folders have no subject, so their new documented declarations get no pages until a graph pull "
            "request places them and runs the whole-project sync:", ""], [f"- `{module}`" for module in plan.subjectless],
            f"{len(plan.subjectless)} changed modules with no pages, too many to list here:")
    if plan.notes or links.notes:
        part("Left for an editor", [], [f"- {note}" for note in plan.notes + links.notes],
             f"{len(plan.notes) + len(links.notes)} notes for an editor, too many to list here:")
    for kind, title in sync.REPORT:
        if kind in EDITOR_ITEMS and sections.get(kind):
            part(title, [], ["```text"] + sections[kind] + ["```"],
                 f"{len(sections[kind])} lines, too many to list here:")
    if unrecorded:
        part("Pages to check", ["Their declaration's docstring changed, and no pull request recorded the new digest:",
                                ""], ["```text"] + unrecorded + ["```"],
             f"{len(unrecorded)} pages whose declaration's docstring changed, and no pull request recorded the new "
             "digest, too many to list here:")
    for title, key in (("Held back, so with no page", "held"), ("Listed as duplicates, so with no page", "duplicates")):
        if report.get(key):
            part(title, [], ["```text"] + report[key] + ["```"], f"{len(report[key])} declarations, too many to list here:")
    if links.unchanged or links.linked:
        named: dict[int, list[str]] = {}
        for article, numbers in links.linked.items():
            for number in numbers:
                named.setdefault(number, []).append(article)
        body = []
        if links.unchanged:
            body += ["```text"] + [f"{article} ({numbered(numbers)}): {why}".replace("`", "")
                                   for article, numbers, why in links.unchanged] + ["```"]
        if links.linked:
            body += ([""] if body else []) + [f"Pages linked already, {len(links.linked)}, by the pull request that "
                                              "names them:", "", "```text"]
            body += [f"#{number}: {' '.join(articles)}" for number, articles in sorted(named.items())] + ["```"]
        # The short form keeps how many ids each kind of reason leaves as they are (reason_kind).
        counted = Counter(reason_kind(why) for _, _, why in links.unchanged)
        part("Pages named on `Graph:` lines, left as they are", [], body,
             f"{len(links.linked)} ids name pages linked already"
             + "".join(f"; {count} ids: {why}" for why, count in sorted(counted.items())) + ", too many to list here:")
    part("New pages by module", [], [f"- `{module}`: {count}" for module, count in sorted(modules.items())],
         f"{len(missing)} new pages, for declarations of {len(modules)} modules, too many to list here:")
    tail = ["## Validation", "",
            f"- `python3 scripts/graph_batch.py verify {commit}`, from a checkout of `main` that has `{head}`: the "
            "taxonomy is main's with the placement plan applied, and the scoped check finds the wiki in step, "
            "exactly what the sync writes" + (" once the planned pages above are linked" if links.links else "") + "."]
    chosen = [whole for whole, _, _ in parts]
    while not full and len("\n".join(lines + [line for block in chosen for line in block] + tail)) >= BODY_LIMIT:
        # The list whose short form saves the most, the earlier one on a tie; a last one only once no other can.
        savings = [(not last, len("\n".join(chosen[index])) - len("\n".join(short)), -index)
                   for index, (_, short, last) in enumerate(parts) if chosen[index] is not short]
        if not (savings := [saving for saving in savings if saving[1] > 0]):
            break
        chosen[-max(savings)[2]] = parts[-max(savings)[2]][1]
    return "\n".join(lines + [line for block in chosen for line in block] + tail) + "\n"


def run_verify(options) -> int:
    commit = commit_of(options.commit)
    head = commit_of("HEAD")
    if head == commit:
        raise BatchError("run verify from an up-to-date checkout of main, not from the batch itself: its checks are "
                         "against main's history, and they run this checkout's copy of the scripts")
    found = batch_of(commit, head)
    if found is None:
        raise BatchError(f"{commit} is not a batch of this checkout's main: one commit, with make's message and its "
                         f"{BASE_TRAILER} and {THROUGH_TRAILER} trailers, on the commit the second names, both commits "
                         "on main's first-parent history, that changes only a batch's files. Run verify from an "
                         "up-to-date checkout of main")
    # From a newer main, the batch must still merge into it as it is.
    onto = head if head not in (commit, found[1]) and not is_ancestor(head, commit) else None
    verdict = verify_commit(commit, bodies_for(*found, options.bodies), onto=onto, recompute=True)
    # What the reviewer reads: recomputed here, not taken from the pull request's description, which can be edited.
    report, sections = verdict.made
    whole = describe(commit, verdict.base, verdict.through, verdict.plan, report, sections, verdict.links, full=True)
    text = describe(commit, verdict.base, verdict.through, verdict.plan, report, sections, verdict.links)
    print("\nWhat the batch does, as verify recomputes it from main, every list in full (read this, not the pull "
          "request's description):\n")
    print(whole)
    if verdict.links.withheld:
        print(f"The declarations it withholds, so with no page: {', '.join(verdict.links.withheld)}")
    if text != whole:
        print(f"\nThe description gives some of these lists as counts, to stay within GitHub's limit: "
              f"{len(text)} characters, against {len(whole)} in full.")
    if options.body:
        options.body.write_text(text, encoding="utf-8")
    return 0


def run_base(options) -> int:
    head = commit_of(options.rev)
    if found := last_batch(head):
        commit, base, through = found
        print(f"Last batch: {commit}, from {base} up to {through}.")
        print(f"The next batch starts from {through}.")
        return 0
    print("No batch on this branch yet: the first batch takes its base from --base.")
    return 1


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog="graph_batch.py", description=__doc__.split("\n\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)
    making = commands.add_parser("make", help="commit the next batch on a clean checkout of main")
    making.add_argument("--base", metavar="REV", help="where the batch starts: the first batch's base, or an earlier "
                                                      "commit than where the last batch ended")
    making.add_argument("--bodies", type=Path, metavar="FILE", help="the pull requests' descriptions, as JSON")
    making.add_argument("--body", type=Path, metavar="FILE",
                        help="write a description for the pull request, outside the checkout")
    verifying = commands.add_parser("verify", help="check that a commit is exactly the batch make writes")
    verifying.add_argument("commit", metavar="REV", help="the batch's head commit")
    verifying.add_argument("--bodies", type=Path, metavar="FILE", help="the pull requests' descriptions, as JSON")
    verifying.add_argument("--body", type=Path, metavar="FILE",
                           help="also write the description verify recomputes, outside the checkout")
    basing = commands.add_parser("base", help="print the last batch and where the next one starts")
    basing.add_argument("rev", nargs="?", default="HEAD", metavar="REV")
    options = parser.parse_args(argv)
    try:
        return {"make": make, "verify": run_verify, "base": run_base}[options.command](options)
    except (BatchError, sync.GitError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as error:
        stderr = error.stderr.decode("utf-8", "replace") if isinstance(error.stderr, bytes) else error.stderr or ""
        print(f"error: {' '.join(map(str, error.cmd))} failed: {stderr.strip()}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
