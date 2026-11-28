#!/usr/bin/env python3
"""Which of CI's checks a pull request needs, from the paths its merge commit changes.

    git diff-tree -r -z --no-commit-id --name-only HEAD^1 HEAD -- > PATHS
    python3 -I scripts/ci_scope.py PATHS >> "$GITHUB_OUTPUT"

.github/workflows/ci.yml and blueprint-pages.yml run it on pull requests only: merge groups, pushes,
scheduled and manual runs run every check without asking. It prints one line per check it can skip:

- `build=false` when every changed path is one that the build never reads: graph data (blueprint/,
  the graph's data files in scripts/ and the card move ledger's fragments, the .jsonl files directly
  in scripts/card-moves.d/), or documentation (Markdown outside blueprint/, scripts/ and .github/,
  and the agent guidance in .agents/ and .claude/);
- `tool_tests=false` when every changed path is graph data, documentation, a Lean source of the
  nine libraries or provenance/: the tool tests of scripts/test_scripts.sh read only scripts,
  workflows and the pins;
- `site_tests=false` when every changed path is documentation, a Lean source of the nine libraries
  or provenance/, and none of the files in SITE_TEST_READS: the site-script tests of
  .github/workflows/blueprint-pages.yml read the graph's data, their own code and those files.

Any other path, or no path at all, prints `true`. The workflow skips a check only on `false`, so a
failure here, or of its step, runs everything as before. Changed paths are never printed.

It reads no file but the listing, and imports only the standard library.
"""

from __future__ import annotations

import sys

# The graph's data files outside blueprint/, which graph checks read and the Lean build does not.
GRAPH_FILES = frozenset({
    "scripts/taxonomy.json",
    "scripts/wiki-sync.json",
    "scripts/card-moves.jsonl",
    "scripts/mathgraph-map.jsonl",
})


# The folder of the card move ledger's fragments: each fragment, a .jsonl file directly in it, is graph data, as the
# frozen file in GRAPH_FILES is; anything else below it is not.
FRAGMENTS = "scripts/card-moves.d/"


def fragment(path: str) -> bool:
    return path.startswith(FRAGMENTS) and path.count("/") == 2 and path.endswith(".jsonl")


def graph(path: str) -> bool:
    return path.startswith("blueprint/") or path in GRAPH_FILES or fragment(path)


LIBRARIES = ("MathlibExt", "MathlibExtTest", "CSLibExt", "CSLibExtTest", "PhyslibExt", "PhyslibExtTest",
             "Domains", "DomainsTest", "WantedExt")


def library_source(path: str) -> bool:
    return path.endswith(".lean") and path.split("/", 1)[0] in LIBRARIES


# What the site-script tests read besides the graph's data and their own code, from traces of their
# runs: scripts/test_blueprint_taxonomy.py indexes four Lean modules, and the importer's tests compare
# its schemas with docs/mathgraph-import.md.
SITE_TEST_READS = frozenset({
    "MathlibExt/Probability/Causality/PotentialOutcomes.lean",
    "MathlibExt/Probability/ChineseRestaurant.lean",
    "MathlibExt/Combinatorics/SimpleGraph/TreeMetric.lean",
    "Domains/Biology/StatisticalGenetics/MendelianRandomization.lean",
    "docs/mathgraph-import.md",
})


def documentation(path: str) -> bool:
    if path.startswith((".agents/", ".claude/")):
        return True
    return path.endswith(".md") and not path.startswith(("blueprint/", "scripts/", ".github/"))


def needs_build(paths: list[str]) -> bool:
    return not paths or not all(graph(path) or documentation(path) for path in paths)


def needs_tool_tests(paths: list[str]) -> bool:
    return not paths or not all(graph(path) or documentation(path) or library_source(path)
                                or path.startswith("provenance/") for path in paths)


def needs_site_tests(paths: list[str]) -> bool:
    return not paths or not all((documentation(path) or library_source(path) or path.startswith("provenance/"))
                                and path not in SITE_TEST_READS for path in paths)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: scripts/ci_scope.py PATHS (NUL-separated, as git diff-tree -z writes them)", file=sys.stderr)
        return 2
    with open(argv[1], "rb") as listing:
        paths = [path.decode("utf-8", "surrogateescape") for path in listing.read().split(b"\0") if path]
    build, tool_tests, site_tests = needs_build(paths), needs_tool_tests(paths), needs_site_tests(paths)
    print(f"build={'true' if build else 'false'}")
    print(f"tool_tests={'true' if tool_tests else 'false'}")
    print(f"site_tests={'true' if site_tests else 'false'}")
    print(f"Changed paths: {len(paths)}. build: {'runs' if build else 'skipped'}; "
          f"tool tests: {'run' if tool_tests else 'skipped'}; "
          f"site-script tests: {'run' if site_tests else 'skipped'}.", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
