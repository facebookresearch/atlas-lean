#!/usr/bin/env python3
"""Collapse the v2 declaration dump onto wiki articles.

    scripts/extract_v2_lean_dependencies.py DUMP.jsonl[.gz] OUTPUT.json

The dump (from scripts/dump_v2_dependencies.lean, run by the Pages build's
edges job) lists, for every constant in the v2 modules, the v2 constants its
type and value use. Articles are exactly the Lean names the wiki's articles
link, as Autoform reads them, so source-level commands and compiled constants
cannot disagree about projections, wrappers, wanted declarations, or docstrings. An
article's statement dependencies are the articles its type reaches through
non-article constants (private helpers, auxiliary declarations, undocumented
definitions), together with what its value reaches when it is a definition (its
body) or an inductive type (its constructors' types). A theorem's proof
dependencies are those its value reaches the same way, minus the statement
ones. Mutually recursive definitions and mutual inductive types depend on each
other, which a dependency DAG can't show, so statement edges inside such a group
are left out and the group is listed under "mutual". The build adds the result
to the articles' Depends on lists; it is never committed.
"""

from __future__ import annotations

import gzip
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BLUEPRINT = ROOT / "blueprint"
LIBRARIES = frozenset({"MathlibExt", "CSLibExt", "PhyslibExt", "WantedExt"})
# A definition is its body and an inductive type its constructors, so their values are part of the statement.
STATEMENT_VALUE = frozenset({"def", "inductive"})


def read_dump(path: Path) -> dict[str, dict]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as handle:
        return {row["name"]: row for row in map(json.loads, handle) if row}


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


def article_manifest() -> set[str]:
    """The Lean names the wiki's articles link, read by Autoform's own loader."""

    from autoform_cli.graph import load_graph

    return set(load_graph(BLUEPRINT).lean_names())


def frontiers(rows: dict[str, dict], articles: set[str]) -> dict[str, frozenset[str]]:
    """For every non-article constant, the articles reachable through non-articles."""
    memo: dict[str, frozenset[str]] = {}
    for start in rows:
        if start in articles or start in memo:
            continue
        stack = [(start, False)]
        active: set[str] = set()
        while stack:
            name, expanded = stack.pop()
            if name in memo:
                continue
            row = rows.get(name)
            uses = (row["type"] + row["value"]) if row else []
            if not expanded:
                if name in active:  # mutual recursion: resolve with what is known
                    continue
                active.add(name)
                stack.append((name, True))
                stack.extend((use, False) for use in uses if use not in articles and use not in memo)
                continue
            reached: set[str] = set()
            for use in uses:
                if use in articles:
                    reached.add(use)
                else:
                    reached |= memo.get(use, frozenset())
            memo[name] = frozenset(reached)
            active.discard(name)
    return memo


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


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    manifest = article_manifest()
    rows = publish_private_targets(read_dump(Path(sys.argv[1])), manifest)
    missing = sorted(manifest - rows.keys())
    if missing:
        for name in missing[:20]:
            print(f"warning: roadmap Lean target is absent from the compiled dependency dump: {name}", file=sys.stderr)
        print(f"warning: {len(missing)} roadmap targets have no compiled dependency row", file=sys.stderr)
    articles = manifest & rows.keys()
    reach = frontiers(rows, articles)

    def collapse(name: str, uses: list[str]) -> set[str]:
        found: set[str] = set()
        for use in uses:
            found |= {use} if use in articles else reach.get(use, frozenset())
        found.discard(name)
        return found

    result = {}
    for name in sorted(articles):
        row = rows[name]
        if row["kind"] in STATEMENT_VALUE:
            statement, proof = collapse(name, row["type"] + row["value"]), set()
        else:
            statement = collapse(name, row["type"])
            proof = collapse(name, row["value"]) - statement
        result[name] = {
            "module": row["module"],
            "statement": sorted(statement),
            "proof": sorted(proof),
        }
    groups = mutual_groups({name: set(entry["statement"]) for name, entry in result.items()})
    for group in groups:
        for name in group:
            result[name]["statement"] = [use for use in result[name]["statement"] if use not in group]
    output = Path(sys.argv[2])
    output.parent.mkdir(parents=True, exist_ok=True)
    # A target with no compiled row has no module to name its library, so its own name has to.
    missing_by_library = {
        library: [name for name in missing if name.split(".")[0] == library]
        for library in sorted(LIBRARIES)
    }
    unplaced = [name for name in missing if name.split(".")[0] not in LIBRARIES]
    if unplaced:
        print(f"warning: {len(unplaced)} targets without a compiled row name no library: {unplaced[:5]}", file=sys.stderr)
    output.write_text(
        json.dumps(
            {
                "missing_articles": missing_by_library,
                "mutual": groups,
                "articles": result,
            },
            ensure_ascii=False,
            sort_keys=True,
        )
        + "\n"
    )
    edges = sum(len(entry["statement"]) + len(entry["proof"]) for entry in result.values())
    print(
        f"{len(rows)} constants, {len(articles)} compiled articles, {len(missing)} without a compiled row, "
        f"{edges} article edges -> {output}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
