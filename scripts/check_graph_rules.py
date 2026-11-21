#!/usr/bin/env python3
"""Check the mechanical graph rules of docs/BLUEPRINT.md ("Graph rules") on the working tree.

    python scripts/check_graph_rules.py                            report every finding
    python scripts/check_graph_rules.py --base BASE                also say which findings BASE doesn't have
    python scripts/check_graph_rules.py --base BASE --blocking     and fail on those
    python scripts/check_graph_rules.py --built                    after lean-facts: informal links that close a
                                                                   cycle through Lean edges (report-only)

The rules themselves, and which of them this script checks, are in docs/BLUEPRINT.md under "Graph rules"
and its "Checks" subsection; each finding names its rule. The script reads the working tree (in CI, the
committed tree, before `sync_wiki.py lean-facts` adds the Lean's facts), and reads pages with the pinned
Autoform's own Markdown readers, so it sees links, headings and code as `autoform check` and the site do.
--built is never compared with a base and never blocks.

With --base, each finding is compared with the base commit's by its rule, the page it is about and what is
wrong, counting repeats and ignoring line numbers, so a row inserted above an old finding doesn't make it new
and a second copy of an old mistake is still new. Findings the base already has are inherited. Without
--blocking the exit status is 0 whatever is found (report-only); with it, a new finding exits 1. In GitHub
Actions every finding is also an annotation on the run, and --summary appends a table to the job summary.
"""

from __future__ import annotations

import argparse
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
from collections import Counter
from dataclasses import dataclass, field, replace
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
OWN = "org.atlas-wiki"
AUTOFORM = "org.autoform"
NOT_READY = "not_ready"
ARTICLE_ID = re.compile(r"af_[0-9a-f]{24}\Z")
# The folder `generate_wiki.py` and `sync_wiki.py declarations` use for modules the taxonomy has not placed
# yet: a field folder beside a subject's fields, or a subject folder at the root.
UNCLASSIFIED = "not-yet-classified"
# The most files GitHub lists in one pull request's diff.
MAX_CHANGED_FILES = 3000
# Build outputs (docs/BLUEPRINT.md, rule 8) that must never be committed.
OUTPUTS = ("site", "site-src", "build", "v2-dependencies.jsonl", "v2-dependencies.jsonl.gz", "v2-modules.txt")
# Facts `lean-facts` adds to an annotation at build time (rule 8).
DERIVED_FACTS = ("kind", "status")
# The annotation files the pinned Autoform reads under blueprint/links/ (autoform_cli/annotations.py).
DEFAULTS = "_defaults.json"
ANNOTATION_LINES = (".jsonl", ".ndjson")
ANNOTATION_SUFFIXES = (".json", *ANNOTATION_LINES)
LEAN_SECTIONS = frozenset({"depends on", "proof depends on"})
PARTS = ("annotations", "taxonomy", "listings", "edges", "outputs")


@dataclass(frozen=True)
class Finding:
    rule: int
    subject: str  # the repository path the finding is about
    detail: str  # what is wrong, with no line number
    where: str = ""  # file:line, for people only
    part: str = ""  # the part of the check that found it, to check only that part of the base

    def key(self) -> tuple[int, str, str]:
        return (self.rule, self.subject, self.detail)

    def __str__(self) -> str:
        rule = f"rule {self.rule}" if self.rule else "Autoform's format"
        return f"{self.where or self.subject}: {self.detail} ({rule})"


@dataclass
class Report:
    findings: list[Finding] = field(default_factory=list)

    def add(self, rule: int, subject: str, detail: str, where: str = "") -> None:
        self.findings.append(Finding(rule, subject, detail, where))


def autoform():
    """The pinned Autoform's readers, which the wiki build installs (docs/BLUEPRINT.md)."""
    try:
        from autoform_cli import graph, markdown
    except ImportError:
        sys.exit("check_graph_rules.py needs Autoform at .github/autoform-ref; install it as docs/BLUEPRINT.md shows")
    return graph, markdown


def rel(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def local_targets(page: Path, text: str) -> list[Path]:
    """The pages and folders `text` visibly links, as Autoform reads links (code, comments and escapes
    masked, reference links resolved, percent-escapes decoded)."""
    _, markdown = autoform()
    targets = []
    for _, target, _ in markdown.markdown_links(text):
        try:
            split = urlsplit(target)
        except ValueError:
            continue
        if split.scheme or split.netloc or not split.path:
            continue
        try:
            linked = (page.parent / unquote(split.path)).resolve()
            targets.append(linked / "README.md" if linked.is_dir() else linked)
        except (OSError, ValueError):
            continue  # a target no file can have (an encoded NUL, say) lists nothing; it is skipped, not reported
    return targets


def lean_sections(text: str) -> list[str]:
    """The `## Depends on` and `## Proof depends on` headings in `text`, as Autoform reads headings."""
    _, markdown = autoform()
    found = []
    for line in markdown.content_lines(text):
        heading = markdown.HEADING.match(line)
        if heading and len(heading.group(1)) == 2 and heading.group(2).strip().casefold() in LEAN_SECTIONS:
            found.append(heading.group(2).strip())
    return found


def linked(annotation: dict) -> bool:
    """Whether a row ties its page to Lean, as `sync_wiki.py lean-facts` reads it: a declaration under
    `object`, or the module and name an earlier sync wrote."""
    extensions = annotation.get("extensions")
    own = extensions.get(OWN) if isinstance(extensions, dict) else None
    objects = annotation.get("object")
    named = isinstance(objects, list) and any(
        isinstance(end, dict) and isinstance(end.get("location"), dict) and end["location"].get("declaration")
        for end in objects
    )
    return bool(named or (isinstance(own, dict) and "module" in own and "name" in own))


# --------------------------------------------------------------------------- annotations: rules 5, 8, 12


def read_text(path: Path, root: Path, report: Report, rule: int) -> str | None:
    """A file's text, decoded strictly as UTF-8, or None with a finding when it cannot be read: Autoform leaves
    out an annotation file that is not UTF-8 and reports a page it cannot read, and lean-facts stops on either."""
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        report.add(rule, rel(path, root), "not UTF-8; Autoform leaves it out and lean-facts stops on it")
    except OSError as error:
        report.add(rule, rel(path, root), f"cannot be read ({error.strerror})")
    return None


def annotation_rows(text: str, source: Path) -> list[tuple[int | None, str]]:
    """The rows Autoform reads from a links file: one per line of a `.jsonl` or `.ndjson`, the whole of a `.json`."""
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    if source.name.lower().endswith(ANNOTATION_LINES):
        return [(number, line) for number, line in enumerate(text.split("\n"), 1) if line.strip(" \t")]
    return [(None, text)]


def links_files(links: Path, symlinks: list[Path] | None = None) -> list[Path]:
    """The files under blueprint/links/ the pinned Autoform reads (autoform_cli/annotations.py): no dot-named
    file or folder, and no symbolic link, which Autoform does not follow; those go in `symlinks`."""
    symlinks = symlinks if symlinks is not None else []
    found: list[Path] = []
    pending = [links]
    while pending:
        folder = pending.pop()
        try:
            entries = sorted(os.scandir(folder), key=lambda entry: entry.name)
        except OSError:
            continue
        for entry in entries:
            if entry.name.startswith("."):
                continue
            if entry.is_symlink():
                symlinks.append(Path(entry.path))
                continue
            if entry.is_dir(follow_symlinks=False):
                pending.append(Path(entry.path))
            elif entry.is_file(follow_symlinks=False):
                found.append(Path(entry.path))
    return sorted(found)


def check_row_extensions(subject: str, annotation: dict, at: str, report: Report) -> bool:
    """Validate the flag's type now; check the resulting page's placement and linkage after reading all rows."""
    extensions = annotation.get("extensions", {})
    ours = extensions.get(AUTOFORM, {}) if isinstance(extensions, dict) else {}
    if not isinstance(ours, dict) or NOT_READY not in ours:
        return False
    if not isinstance(ours[NOT_READY], bool):
        report.add(12, subject, f"{NOT_READY} takes true or false; Autoform drops any other value", at)
        return False
    return ours[NOT_READY]


def annotation_page(roadmap: Path, source: Path, name: str, annotation: dict, at: str, report: Report) -> Path | None:
    subjects = annotation.get("subject")
    if not isinstance(subjects, list) or len(subjects) != 1 or not isinstance(subjects[0], dict):
        report.add(5, name, "a row names exactly one subject page", at)
        return None
    uri = subjects[0].get("uri")
    # sync_wiki resolves a subject as written; Autoform decodes it first.
    if isinstance(uri, str) and uri and unquote(uri) != uri:
        report.add(5, name, f"subject {uri!r} has a percent-escape; write the page's path as it is", at)
        return None
    try:
        page = (source.parent / uri).resolve() if isinstance(uri, str) and uri else None
    except (OSError, ValueError):
        page = None
    if page is None or page.suffix != ".md" or roadmap not in page.parents:
        report.add(5, name, f"subject {uri!r} is not a page under blueprint/roadmap/", at)
        return None
    if not page.is_file():
        report.add(5, page.relative_to(roadmap.parent.parent).as_posix(), "its annotation names a page that does not exist", at)
        return None
    return page


def load_annotations(root: Path, report: Report, *, linked_pages: set[Path] | None = None) -> dict[Path, dict]:
    vault = root / "blueprint"
    roadmap = (vault / "roadmap").resolve()
    links = vault / "links"
    seen: dict[Path, str] = {}  # pages with a row in a subject's links file, which sync_wiki.py reads
    rows: set[Path] = set()  # pages with a row in any file Autoform reads
    ids: dict[str, list[tuple[str, str]]] = {}
    annotations: dict[Path, dict] = {}
    linked_pages = set() if linked_pages is None else linked_pages
    pending: dict[Path, str] = {}
    symlinks: list[Path] = []
    if links.is_symlink() or not links.is_dir():
        # Autoform accepts only a real folder here ("blueprint/links is not a folder, so no annotation is read").
        report.add(5, "blueprint/links", "not a folder (a symbolic link or missing), so Autoform reads no annotation")
        return annotations
    files = links_files(links, symlinks)
    from literature_links import companion

    defaults: dict[Path, dict] = {}
    for source in files:
        if source.name != DEFAULTS:
            continue
        name = rel(source, root)
        if source.parent != links:
            report.add(5, name, "Autoform merges this defaults file too; keep the one in blueprint/links/")
        text = read_text(source, root, report, 5)
        if text is None:
            continue
        try:
            shared = json.loads(text)
        except json.JSONDecodeError as error:
            report.add(5, name, f"not JSON ({error.msg})")
            continue
        if not isinstance(shared, dict):
            report.add(5, name, "annotation defaults must be a JSON object")
            continue
        for fact in DERIVED_FACTS:
            if fact in shared:
                report.add(8, name, f"the defaults commit {fact!r}, which lean-facts adds at build time")
        # Only extensions and Lean reference data affect the page-level checks below.
        defaults[source.parent] = {key: shared[key] for key in ("extensions", "object") if key in shared}

    templates: dict[Path, dict] = {}

    def template_for(folder: Path) -> dict:
        if folder not in templates:
            ancestors = [parent for parent in reversed(folder.parents) if parent == links or links in parent.parents]
            template: dict = {}
            for parent in [*ancestors, folder]:
                if parent in defaults:
                    template = companion.merge(template, defaults[parent], defaults=True)
            templates[folder] = template
        return templates[folder]

    for link in symlinks:
        # Not followed, and named by its own path: Autoform leaves it out and render refuses it.
        name = link.relative_to(root).as_posix()
        report.add(5, name, "a symbolic link in blueprint/links/; Autoform does not follow it and render refuses it")
    for source in files:
        name, lowered = rel(source, root), source.name.lower()
        if not lowered.endswith(ANNOTATION_SUFFIXES) or source.name == DEFAULTS:
            continue
        top_level = source.parent == links
        template = template_for(source.parent)
        if not (top_level and source.suffix == ".jsonl"):
            # Autoform reads every .json, .jsonl and .ndjson file here, at any depth; sync_wiki.py reads only
            # blueprint/links/<Subject>.jsonl, so annotations anywhere else are a second, unsynced source.
            report.add(5, name, "Autoform reads this file, but annotations go in blueprint/links/<Subject>.jsonl")
        text = read_text(source, root, report, 5)
        if text is None:
            continue
        for number, line in annotation_rows(text, source):
            at = name if number is None else f"{name}:{number}"
            try:
                annotation = json.loads(line)
            except json.JSONDecodeError as error:
                report.add(5, name, f"a row is not JSON ({error.msg})", at)
                continue
            if not isinstance(annotation, dict):
                report.add(5, name, "a row names exactly one subject page", at)
                continue
            page = annotation_page(roadmap, source, name, annotation, at, report)
            subject = rel(page, root) if page is not None else name
            for fact in DERIVED_FACTS:
                if fact in annotation:
                    report.add(8, subject, f"its annotation commits {fact!r}, which lean-facts adds at build time", at)
            if page is None:
                continue
            # Every row is checked in full, a second row for a page included: Autoform merges them all.
            objects = annotation.get("object", [])
            if not isinstance(objects, list):
                report.add(5, subject, "its annotation's `object` is not a list of ends", at)
            elif len(objects) > 1:
                report.add(5, subject, "its annotation names more than one Lean declaration", at)
            article_id = annotation.get("id")
            if article_id is not None:  # a missing id is not a finding until the one-off fill (#5524)
                if not isinstance(article_id, str) or not ARTICLE_ID.fullmatch(article_id):
                    report.add(5, subject, f"malformed id {article_id!r}", at)
                else:
                    ids.setdefault(article_id, []).append((subject, at))
            try:
                effective = companion.merge(template, annotation) if template else annotation
            except RecursionError:
                report.add(5, subject, "annotation and defaults are nested too deeply to merge", at)
                effective = annotation
            if check_row_extensions(subject, effective, at, report):
                pending.setdefault(page, at)
            if linked(annotation) or linked(effective):
                linked_pages.add(page)
            # Autoform merges a row from any file it reads, so a second one anywhere is a second annotation.
            if page in rows:
                report.add(5, subject, "the page has more than one annotation", at)
            rows.add(page)
            if not top_level or source.suffix != ".jsonl":
                continue
            parts = page.relative_to(roadmap).parts
            expected = "roadmap" if len(parts) == 1 else parts[0]
            if source.name != f"{expected}.jsonl":
                report.add(5, subject, f"its annotation belongs in blueprint/links/{expected}.jsonl", at)
            if page in seen:
                continue
            seen[page] = at
            annotation["_at"] = at
            annotations[page] = annotation
    for page, at in sorted(pending.items()):
        if page in linked_pages:
            report.add(12, rel(page, root), f"a node still to be broken down ({NOT_READY}) names no Lean declaration", at)
        elif page.name == "README.md":
            report.add(12, rel(page, root), f"a folder page is not a node to break down; mark an article {NOT_READY}", at)
    for page in sorted(roadmap.rglob("*.md")):
        # lean-facts stops on such a page much later in the build (#5069).
        if page not in seen and not any(part.startswith(".") for part in page.relative_to(roadmap).parts):
            report.add(5, rel(page, root), "the page has no annotation row in blueprint/links/")
    for article_id, owners in sorted(ids.items()):
        if len({subject for subject, _ in owners}) > 1:
            # One finding per collision, the same whichever row comes first.
            pages = sorted({subject for subject, _ in owners})
            report.add(5, pages[0], f"id {article_id} is shared by " + ", ".join(pages),
                       ", ".join(at for _, at in sorted(owners)))
    return annotations


# --------------------------------------------------------------------------- taxonomy and listings: rules 1, 2


def check_taxonomy(root: Path, report: Report) -> None:
    roadmap = root / "blueprint" / "roadmap"
    path = "scripts/taxonomy.json"
    try:
        taxonomy = json.loads((root / path).read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        report.add(1, path, f"unreadable taxonomy ({error})")
        return
    subjects = taxonomy.get("subjects") if isinstance(taxonomy, dict) else None
    if not isinstance(subjects, dict):
        report.add(1, path, "taxonomy subjects must be a JSON object")
        return
    field_slugs: dict[str, set[str]] = {}
    for name, subject in sorted(subjects.items()):
        if not isinstance(subject, dict) or not isinstance(subject.get("fields", []), list):
            report.add(1, path, f"subject {name!r} must be an object with a list of fields")
            continue
        fields = subject.get("fields", [])
        if any(not isinstance(entry, dict) or not isinstance(entry.get("slug"), str) or not entry["slug"]
               for entry in fields):
            report.add(1, path, f"each field of subject {name!r} must be an object with a nonempty string slug")
            continue
        field_slugs[name] = {entry["slug"] for entry in fields}
    for folder in sorted(path for path in roadmap.iterdir() if path.is_dir()):
        if folder.name == UNCLASSIFIED:
            continue
        if folder.name not in subjects:
            report.add(1, rel(folder, root), "not a subject of scripts/taxonomy.json")
            continue
        fields = field_slugs.get(folder.name)
        if not fields:
            continue
        for child in sorted(folder.iterdir()):
            if child.is_dir() and child.name not in fields | {UNCLASSIFIED}:
                report.add(1, rel(child, root), f"not a field of {folder.name} in scripts/taxonomy.json")
            elif child.is_file() and child.suffix == ".md" and child.name != "README.md":
                report.add(1, rel(child, root), "a page of a subject with fields goes in a field folder")


def check_listings(root: Path, report: Report) -> None:
    roadmap = (root / "blueprint" / "roadmap").resolve()
    # Every folder that holds a page at any depth, so one with only subfolders still needs its folder page.
    folders = {folder for page in roadmap.rglob("*.md") for folder in page.parents
               if folder == roadmap or roadmap in folder.parents}
    for folder in sorted(folders):
        readme = folder / "README.md"
        if not readme.is_file():
            report.add(2, rel(folder, root), "the folder has no README.md folder page")
            continue
        text = read_text(readme, root, report, 2)
        listed = set(local_targets(readme, text)) if text is not None else set()
        for child in sorted(folder.iterdir()):
            entry = child / "README.md" if child.is_dir() else child
            if (child.is_dir() and entry.is_file()) or (child.suffix == ".md" and child.name != "README.md"):
                if entry.resolve() not in listed:
                    report.add(2, rel(entry, root), f"not listed on {rel(readme, root)}")


# --------------------------------------------------------------------------- edges: rules 9, 11


def check_edges(root: Path, linked_pages: set[Path], report: Report) -> None:
    graph_module, _ = autoform()
    vault = root / "blueprint"
    for page in sorted(linked_pages):
        # Folder pages are included: lean-facts skips them, so nothing would rewrite their sections.
        text = read_text(page, root, report, 9)
        for heading in lean_sections(text) if text is not None else ():
            canonical = "Proof depends on" if heading.casefold() == "proof depends on" else "Depends on"
            report.add(9, rel(page, root), f"commits `## {canonical}`, which lean-facts writes at build time")
    try:
        graph = graph_module.load_graph(vault)
    except graph_module.GraphValidationError as error:
        # Not an ATLAS rule: Autoform's own format. `autoform check` reports the same issues after lean-facts.
        for issue in error.issues:
            report.add(0, "blueprint", f"autoform cannot load the graph: {issue}")
        return
    paths = {node_id: rel(Path(node.path), root) for node_id, node in graph.nodes.items()}
    for warning in graph.warnings:
        if "informal target" in warning or "informally uses itself" in warning:
            node_id = warning.split(":", 1)[0]
            report.add(11, paths.get(node_id, node_id), f"`## Informally uses`: {warning.split(': ', 1)[-1]}")
    counted = {node_id: set(node.dependencies) for node_id, node in graph.nodes.items()}
    informal = {node_id: set(node.informal_dependencies) for node_id, node in graph.nodes.items()}
    union = {node_id: counted[node_id] | informal[node_id] for node_id in graph.nodes}
    for group in strongly_connected(union):
        # One finding per informal link that closes the cycle, keyed by its two ends, so a second such link
        # between pages already in a cycle is still a new finding.
        members = set(group)
        for source in sorted(group):
            for target in sorted(informal[source] & members):
                report.add(11, paths[source], f"`## Informally uses` links {paths[target]}, which reaches back to it")


def strongly_connected(edges: dict) -> list[list]:
    """The strongly connected groups of two or more nodes (Tarjan, iterative)."""
    index: dict = {}
    low: dict = {}
    stack: list = []
    on_stack: set = set()
    groups: list[list] = []
    counter = 0
    for root in sorted(edges):
        if root in index:
            continue
        work = [(root, iter(sorted(edges.get(root, ()))))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            node, children = work[-1]
            advanced = False
            for child in children:
                if child not in index:
                    index[child] = low[child] = counter
                    counter += 1
                    stack.append(child)
                    on_stack.add(child)
                    work.append((child, iter(sorted(edges.get(child, ())))))
                    advanced = True
                    break
                if child in on_stack:
                    low[node] = min(low[node], index[child])
            if advanced:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])
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
    return groups


# --------------------------------------------------------------------------- git: rules 8, 15


def git(root: Path, *args: str) -> list[str]:
    output = subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True, text=True).stdout
    return [line for line in output.splitlines() if line]


def check_outputs(root: Path, report: Report, commit: str | None = None, repository: Path | None = None) -> None:
    """Rule 8: no build output is tracked, in the working tree or, with `commit`, in that commit."""
    repository = repository or root
    if not (repository / ".git").exists():
        return
    if commit:
        paths = git(repository, "ls-tree", "-r", "--name-only", commit, "--", *OUTPUTS)
    else:
        paths = git(repository, "ls-files", "--", *OUTPUTS)
    for path in paths:
        report.add(8, path, "a build output is committed")


def check_size(root: Path, base: str, report: Report) -> None:
    changed = git(root, "diff", "--name-only", base, "HEAD")
    if len(changed) >= MAX_CHANGED_FILES:
        report.add(15, "the PR", f"changes {len(changed)} files; split it below {MAX_CHANGED_FILES}, "
                   "the most GitHub shows in one diff")


# --------------------------------------------------------------------------- running


def check(root: Path = ROOT, base: str | None = None, parts: tuple[str, ...] = PARTS) -> list[Finding]:
    report = Report()
    done = 0

    def tag(part: str) -> None:
        nonlocal done
        report.findings[done:] = [replace(finding, part=part) for finding in report.findings[done:]]
        done = len(report.findings)

    linked_pages: set[Path] = set()
    if {"annotations", "edges"} & set(parts):
        load_annotations(root, report, linked_pages=linked_pages)
        if "annotations" not in parts:
            del report.findings[done:]
        tag("annotations")
    if "taxonomy" in parts:
        check_taxonomy(root, report)
        tag("taxonomy")
    if "listings" in parts:
        check_listings(root, report)
        tag("listings")
    if "edges" in parts:
        check_edges(root, linked_pages, report)
        tag("edges")
    if "outputs" in parts:
        check_outputs(root, report)
        tag("outputs")
    if base:
        check_size(root, base, report)
        tag("size")
    return report.findings


def base_findings(root: Path, base: str, parts: set[str]) -> list[Finding]:
    """The base commit's findings, for the parts of the check the head has findings in: its vault and taxonomy
    exported from git and checked alone, and its tracked build outputs."""
    findings: list[Finding] = []
    tree_parts = tuple(part for part in PARTS if part in parts and part != "outputs")
    if tree_parts:
        with tempfile.TemporaryDirectory() as directory:
            archive = subprocess.run(
                ["git", "-C", str(root), "archive", "--format=tar", base, "blueprint", "scripts/taxonomy.json"],
                check=True, capture_output=True,
            ).stdout
            with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
                try:
                    tar.extractall(directory, filter="data")
                except TypeError:  # Python before 3.11.4 has no extraction filters; the archive is our own commit
                    tar.extractall(directory)
            findings += check(Path(directory), parts=tree_parts)
    if "outputs" in parts:
        report = Report()
        check_outputs(root, report, commit=base)
        findings += report.findings
    return findings


def split_new(findings: list[Finding], known: list[Finding]) -> tuple[list[Finding], list[Finding]]:
    """The findings the base doesn't have, and those it does, counting repeats."""
    remaining = Counter(finding.key() for finding in known)
    new, inherited = [], []
    for finding in findings:
        if remaining[finding.key()] > 0:
            remaining[finding.key()] -= 1
            inherited.append(finding)
        else:
            new.append(finding)
    return new, inherited


def annotate(finding: Finding, level: str) -> str:
    """A GitHub Actions workflow command that shows `finding` on the run and the PR's files."""
    location = (finding.where or finding.subject).split(", ")[0]
    path, _, line = location.partition(":")
    parts = [f"file={path}"] if Path(path).suffix else []
    if line.isdigit():
        parts.append(f"line={line}")
    title = f"title=Graph rule {finding.rule}" if finding.rule else "title=Autoform format"
    message = str(finding).replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    return f"::{level} {','.join(parts + [title])}::{message}"


def summary(new: list[Finding], inherited: list[Finding], compared: bool, blocking: bool) -> str:
    mode = "blocking" if blocking else "report-only"
    lines = [f"## Graph rules ({mode})", ""]
    if not new and not inherited:
        return "\n".join(lines + ["No findings.", ""])
    lines += ["| Rule | New | Already on the base |" if compared else "| Rule | Findings |",
              "| ---: | ---: | ---: |" if compared else "| ---: | ---: |"]
    rules = sorted({finding.rule for finding in new + inherited})
    for rule in rules:
        count_new = sum(finding.rule == rule for finding in new)
        count_old = sum(finding.rule == rule for finding in inherited)
        name = rule or "format"
        lines.append(f"| {name} | {count_new} | {count_old} |" if compared else f"| {name} | {count_new} |")
    shown = new[:50]
    if shown:
        lines += ["", "New findings:" if compared else "Findings:", ""] + [f"- {finding}" for finding in shown]
        if len(new) > len(shown):
            lines.append(f"- … and {len(new) - len(shown)} more in the step's log")
    return "\n".join(lines) + "\n"


def reaches(edges: dict, start, goal) -> bool:
    """Whether `goal` can be reached from `start` along `edges`."""
    seen, pending = {start}, [start]
    while pending:
        node = pending.pop()
        if node == goal:
            return True
        for other in edges.get(node, ()):
            if other not in seen:
                seen.add(other)
                pending.append(other)
    return False


def built_informal_cycles(root: Path) -> list[Finding]:
    """Rule 11 on the built graph: an informal link whose target depends on its page through counted edges, as
    Autoform's `informal_cycle_warnings` finds it after `lean-facts` has added the Lean's edges. On the committed
    tree a linked page has no dependency sections (rule 9), so only this pass sees a cycle through Lean edges.
    A cycle the committed tree already closes (through informal links and planned pages' own edges) is left to
    the first pass, so no cycle is reported twice."""
    graph_module, _ = autoform()
    try:
        graph = graph_module.load_graph(root / "blueprint")
    except graph_module.GraphValidationError:
        return []  # autoform check reports it
    linked_pages: set[Path] = set()
    load_annotations(root, Report(), linked_pages=linked_pages)
    paths = {node_id: rel(Path(node.path), root) for node_id, node in graph.nodes.items()}
    counted = {node_id: set(node.dependencies) for node_id, node in graph.nodes.items()}
    # The committed tree's edges: a planned page's own sections, which lean-facts leaves alone, and every
    # informal link; a linked page commits no dependency section (rule 9).
    committed = {
        node_id: (set() if Path(node.path).resolve() in linked_pages else set(node.dependencies))
        | set(node.informal_dependencies)
        for node_id, node in graph.nodes.items()
    }
    findings = []
    for warning in graph_module.informal_cycle_warnings(graph):
        source, _, rest = warning.partition(": informally uses ")
        target = rest.split(", which depends on it", 1)[0]
        if source not in graph.nodes or target not in graph.nodes or not reaches(counted, target, source):
            findings.append(Finding(11, paths.get(source, source), f"`## Informally uses`: {warning}", part="built"))
            continue
        if reaches(committed, target, source):
            continue  # the first pass reports this link
        findings.append(Finding(11, paths[source], f"`## Informally uses` links {paths[target]}, which depends on "
                                "it through Lean edges", part="built"))
    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", help="the commit the PR merges into: say which findings it doesn't have")
    parser.add_argument("--blocking", action="store_true", help="exit 1 on a finding the base doesn't have")
    parser.add_argument("--summary", type=Path, help="append a Markdown summary here (GITHUB_STEP_SUMMARY)")
    parser.add_argument("--built", action="store_true",
                        help="after lean-facts: report only the informal links that close a cycle through Lean edges")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    if args.built:
        # Report-only, and on the checkout lean-facts has changed, so there is no base to compare with.
        findings = built_informal_cycles(args.root.resolve())
        actions = os.environ.get("GITHUB_ACTIONS") == "true"
        for finding in findings:
            print(annotate(finding, "warning") if actions else f"warning: {finding}", file=sys.stderr)
        if args.summary:
            with args.summary.open("a", encoding="utf-8") as handle:
                lines = ["## Graph rules on the built graph (report-only)", ""]
                lines += [f"- {finding}" for finding in findings[:50]] or ["No informal link closes a cycle through Lean edges."]
                if len(findings) > 50:
                    lines.append(f"- … and {len(findings) - 50} more in the step's log")
                handle.write("\n".join(lines) + "\n")
        print(f"graph rules (built): {len(findings)} finding(s), reported only" if findings else "graph rules (built): OK")
        return 0
    if args.blocking and not args.base:
        # With nothing to compare with, every finding would count as new, those main already has included.
        parser.error("--blocking needs --base: it fails only on findings the base doesn't have")
    root = args.root.resolve()
    try:
        if args.base:
            git(root, "rev-parse", "--verify", "--quiet", f"{args.base}^{{commit}}")
    except subprocess.CalledProcessError:
        parser.error(f"--base {args.base!r} is not a commit in this repository; fetch it first")
    findings = check(root, args.base)
    if args.base and findings:
        parts = {finding.part for finding in findings if finding.part != "size"}
        new, inherited = split_new(findings, base_findings(root, args.base, parts))
    else:
        new, inherited = findings, []
    actions = os.environ.get("GITHUB_ACTIONS") == "true"
    for finding in inherited:
        print(annotate(finding, "notice") if actions else f"already on the base: {finding}", file=sys.stderr)
    for finding in new:
        level = "error" if args.blocking else "warning"
        print(annotate(finding, level) if actions else f"{level}: {finding}", file=sys.stderr)
    if args.summary:
        with args.summary.open("a", encoding="utf-8") as handle:
            handle.write(summary(new, inherited, bool(args.base), args.blocking))
    if not findings:
        print("graph rules: OK")
    else:
        what = f"{len(new)} new" if args.base else f"{len(new)}"
        print(f"graph rules: {what} finding(s)" + (f", {len(inherited)} already on the base" if args.base else "")
              + ("" if args.blocking else ", reported only") + "; see Graph rules in docs/BLUEPRINT.md")
    return 1 if args.blocking and new else 0


if __name__ == "__main__":
    sys.exit(main())
