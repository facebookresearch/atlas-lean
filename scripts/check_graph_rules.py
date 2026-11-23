#!/usr/bin/env python3
"""Check the mechanical graph rules of docs/BLUEPRINT.md ("Graph rules") on the working tree.

    python scripts/check_graph_rules.py                        report every finding
    python scripts/check_graph_rules.py --base BASE            also check the size of the change from BASE (rule 15)
    python scripts/check_graph_rules.py --blocking             exit 1 on any finding

The rules themselves, and which of them this script checks, are in docs/BLUEPRINT.md under "Graph rules"
and its "Checks" subsection; each finding names its rule. The script reads the working tree (in CI, the
committed tree, before `sync_wiki.py lean-facts` adds the Lean's facts), and reads pages with the pinned
Autoform's own Markdown readers, so it sees links, headings and code as `autoform check` and the site do.

The check is pass or fail on the whole tree, as a linter is: main is kept clean, so any finding is the change's
own. Without --blocking the exit status is 0 whatever is found (report-only); with it, any finding exits 1. In
GitHub Actions every finding is also an annotation on the run, and --summary appends a list to the job summary.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
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


@dataclass(frozen=True)
class Finding:
    rule: int
    subject: str
    detail: str
    where: str = ""

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


def names_declaration(end: object) -> bool:
    location = end.get("location") if isinstance(end, dict) else None
    declaration = location.get("declaration") if isinstance(location, dict) else None
    return (isinstance(declaration, str) and bool(declaration)
            and end.get("role") in (None, "states"))


def credit_candidates(objects: list) -> set[str]:
    """Declaration names that can supply credit; generic and reference ends do not."""
    named = [end for end in objects if names_declaration(end)]
    states = [end for end in named if end.get("role") == "states"]
    return {end["location"]["declaration"] for end in states or named}


def linked(annotation: dict) -> bool:
    """Whether a row ties its page to Lean, as `sync_wiki.py lean-facts` reads it: a declaration under
    `object`, or the module and name an earlier sync wrote."""
    extensions = annotation.get("extensions")
    own = extensions.get(OWN) if isinstance(extensions, dict) else None
    objects = annotation.get("object")
    named = isinstance(objects, list) and any(names_declaration(end) for end in objects)
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


def links_files(links: Path, symlinks: list[Path]) -> list[Path]:
    """The files under blueprint/links/ the pinned Autoform reads (autoform_cli/annotations.py): no dot-named
    file or folder, and no symbolic link, which Autoform does not follow; those go in `symlinks`."""
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


def not_ready(subject: str, annotation: dict, at: str, report: Report) -> bool:
    """Whether a row marks its page not_ready, with a finding when the flag is not a boolean."""
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


def check_defaults(source: Path, root: Path, links: Path, report: Report) -> None:
    name = rel(source, root)
    if source.parent != links:
        report.add(5, name, "Autoform merges this defaults file too; keep the one in blueprint/links/")
    text = read_text(source, root, report, 5)
    if text is None:
        return
    try:
        shared = json.loads(text)
    except json.JSONDecodeError as error:
        report.add(5, name, f"not JSON ({error.msg})")
        return
    if not isinstance(shared, dict):
        report.add(5, name, "annotation defaults must be a JSON object")
        return
    for fact in DERIVED_FACTS:
        if fact in shared:
            report.add(8, name, f"the defaults commit {fact!r}, which lean-facts adds at build time")
    # Autoform merges the defaults into every row, so each of these would apply to every page.
    if "id" in shared:
        report.add(5, name, "the defaults set a page ID; put each ID on its annotation row")
    objects = shared.get("object")
    if linked({**shared, "object": objects if isinstance(objects, list) else [objects]}):
        report.add(5, name, "the defaults name a Lean declaration for every page; name it on the page's own row")
    extensions = shared.get("extensions")
    ours = extensions.get(AUTOFORM) if isinstance(extensions, dict) else None
    if isinstance(ours, dict) and NOT_READY in ours:
        report.add(12, name, f"the defaults set {NOT_READY} for every page; mark each node to break down on its own row")


def load_annotations(root: Path, report: Report) -> set[Path]:
    """Check the annotations under blueprint/links/ and return the pages a row ties to Lean."""
    vault = root / "blueprint"
    roadmap = (vault / "roadmap").resolve()
    links = vault / "links"
    rows: set[Path] = set()  # pages with a row in any file Autoform reads
    ids: dict[str, str] = {}
    linked_pages: set[Path] = set()
    symlinks: list[Path] = []
    if links.is_symlink() or not links.is_dir():
        # Autoform accepts only a real folder here ("blueprint/links is not a folder, so no annotation is read").
        report.add(5, "blueprint/links", "not a folder (a symbolic link or missing), so Autoform reads no annotation")
        return linked_pages
    files = links_files(links, symlinks)
    for link in symlinks:
        # Not followed, and named by its own path: Autoform leaves it out and render refuses it.
        name = link.relative_to(root).as_posix()
        report.add(5, name, "a symbolic link in blueprint/links/; Autoform does not follow it and render refuses it")
    for source in files:
        name, lowered = rel(source, root), source.name.lower()
        if source.name == DEFAULTS:
            check_defaults(source, root, links, report)
            continue
        if not lowered.endswith(ANNOTATION_SUFFIXES):
            continue
        top_level = source.parent == links
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
            # Check row fields even if the subject is unusable.
            for fact in DERIVED_FACTS:
                if fact in annotation:
                    report.add(8, subject, f"its annotation commits {fact!r}, which lean-facts adds at build time", at)
            objects = annotation.get("object", [])
            if not isinstance(objects, list):
                report.add(5, subject, "its annotation's `object` is not a list of ends", at)
            elif len(credit_candidates(objects)) > 1:
                report.add(5, subject, "its annotation names more than one Lean declaration for credit", at)
            article_id = annotation.get("id")
            if "id" in annotation:  # The committed-annotation suite separately requires an ID on every row.
                if not isinstance(article_id, str) or not ARTICLE_ID.fullmatch(article_id):
                    report.add(5, subject, f"malformed id {article_id!r}", at)
                elif ids.setdefault(article_id, subject) != subject:
                    report.add(5, subject, f"id {article_id} is shared by {ids[article_id]}, {subject}", at)
            row_linked = linked(annotation)
            marked = not_ready(subject, annotation, at, report)
            if marked and row_linked:
                report.add(12, subject, f"a node still to be broken down ({NOT_READY}) names no Lean declaration", at)
            if page is None:
                continue
            if row_linked:
                linked_pages.add(page)
            if marked and not row_linked and page.name == "README.md":
                report.add(12, subject, f"a folder page is not a node to break down; mark an article {NOT_READY}", at)
            # Autoform merges a row from any file it reads, so a second one anywhere is a second annotation.
            if page in rows:
                report.add(5, subject, "the page has more than one annotation", at)
            rows.add(page)
            if top_level and source.suffix == ".jsonl":
                parts = page.relative_to(roadmap).parts
                expected = "roadmap" if len(parts) == 1 else parts[0]
                if source.name != f"{expected}.jsonl":
                    report.add(5, subject, f"its annotation belongs in blueprint/links/{expected}.jsonl", at)
    for page in sorted(roadmap.rglob("*.md")):
        # lean-facts stops on such a page much later in the build (#5069).
        if page not in rows and not any(part.startswith(".") for part in page.relative_to(roadmap).parts):
            report.add(5, rel(page, root), "the page has no annotation row in blueprint/links/")
    return linked_pages


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
    for page in sorted(linked_pages):
        # Folder pages are included: lean-facts skips them, so nothing would rewrite their sections.
        text = read_text(page, root, report, 9)
        for heading in lean_sections(text) if text is not None else ():
            canonical = "Proof depends on" if heading.casefold() == "proof depends on" else "Depends on"
            report.add(9, rel(page, root), f"commits `## {canonical}`, which lean-facts writes at build time")

    check_informal_edges(root, report)


def check_informal_edges(root: Path, report: Report) -> None:
    graph_module, _ = autoform()
    try:
        graph = graph_module.load_graph(root / "blueprint")
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


def check_outputs(root: Path, report: Report) -> None:
    """Rule 8: no build output is tracked."""
    if not (root / ".git").exists():
        return
    for path in git(root, "ls-files", "--", *OUTPUTS):
        report.add(8, path, "a build output is committed")


def check_size(root: Path, base: str, report: Report) -> None:
    changed = git(root, "diff", "--name-only", base, "HEAD")
    if len(changed) >= MAX_CHANGED_FILES:
        report.add(15, "the PR", f"changes {len(changed)} files; split it below {MAX_CHANGED_FILES}, "
                   "the most GitHub shows in one diff")


# --------------------------------------------------------------------------- running


def check(root: Path = ROOT, base: str | None = None) -> list[Finding]:
    report = Report()
    linked_pages = load_annotations(root, report)
    check_taxonomy(root, report)
    check_listings(root, report)
    check_edges(root, linked_pages, report)
    check_outputs(root, report)
    if base:
        check_size(root, base, report)
    return report.findings


def annotate(finding: Finding, level: str) -> str:
    """A GitHub Actions workflow command that shows `finding` on the run and the PR's files."""
    location = finding.where or finding.subject
    path, _, line = location.partition(":")
    parts = [f"file={path}"] if Path(path).suffix else []
    if line.isdigit():
        parts.append(f"line={line}")
    title = f"title=Graph rule {finding.rule}" if finding.rule else "title=Autoform format"
    message = str(finding).replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    return f"::{level} {','.join(parts + [title])}::{message}"


def summary(findings: list[Finding], blocking: bool, *, built: bool = False) -> str:
    title = "Informal dependencies on the built graph" if built else "Graph rules"
    lines = [f"## {title} ({'blocking' if blocking else 'report-only'})", ""]
    if not findings:
        return "\n".join(lines + ["No findings.", ""])
    lines += [f"- {finding}" for finding in findings[:50]]
    if len(findings) > 50:
        lines.append(f"- … and {len(findings) - 50} more in the step's log")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", help="the commit the change starts from, to check its size (rule 15)")
    parser.add_argument("--blocking", action="store_true", help="exit 1 on any finding")
    parser.add_argument("--built", action="store_true", help="after lean-facts: report informal dependencies only")
    parser.add_argument("--summary", type=Path, help="append a Markdown summary here (GITHUB_STEP_SUMMARY)")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    if args.built and (args.base or args.blocking):
        parser.error("--built reports on the built graph and cannot be used with --base or --blocking")
    root = args.root.resolve()
    try:
        if args.base:
            git(root, "rev-parse", "--verify", "--quiet", f"{args.base}^{{commit}}")
    except subprocess.CalledProcessError:
        parser.error(f"--base {args.base!r} is not a commit in this repository; fetch it first")
    if args.built:
        report = Report()
        check_informal_edges(root, report)
        findings = report.findings
    else:
        findings = check(root, args.base)
    actions = os.environ.get("GITHUB_ACTIONS") == "true"
    level = "error" if args.blocking else "warning"
    for finding in findings:
        print(annotate(finding, level) if actions else f"{level}: {finding}", file=sys.stderr)
    if args.summary:
        with args.summary.open("a", encoding="utf-8") as handle:
            handle.write(summary(findings, args.blocking, built=args.built))
    if not findings:
        print("graph rules: OK")
    else:
        print(f"graph rules: {len(findings)} finding(s)" + ("" if args.blocking else ", reported only")
              + "; see Graph rules in docs/BLUEPRINT.md")
    return 1 if args.blocking and findings else 0


if __name__ == "__main__":
    sys.exit(main())
