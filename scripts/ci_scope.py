#!/usr/bin/env python3
"""Whether a pull request needs CI's `build`, from the paths its merge commit changes.

    git diff-tree -r -z --no-commit-id --name-only HEAD^1 HEAD -- > PATHS
    python3 -I scripts/ci_scope.py PATHS >> "$GITHUB_OUTPUT"

The `changes` job of .github/workflows/ci.yml runs it on pull requests only: merge groups, pushes and
manual runs build without asking. It prints `build=false` only when every changed path is one that
the build never reads: graph data (blueprint/ and the graph's data files in scripts/), or
documentation (Markdown outside scripts/ and .github/, and the agent guidance in .agents/ and
.claude/). Any other path, or no path at all, prints `build=true`. The workflow skips `build` only on
`false`, so a failure here, or of the job, builds as before. Changed paths are never printed.
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


def graph(path: str) -> bool:
    return path.startswith("blueprint/") or path in GRAPH_FILES


def documentation(path: str) -> bool:
    if path.startswith((".agents/", ".claude/")):
        return True
    return path.endswith(".md") and not path.startswith(("scripts/", ".github/"))


def needs_build(paths: list[str]) -> bool:
    return not paths or not all(graph(path) or documentation(path) for path in paths)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: scripts/ci_scope.py PATHS (NUL-separated, as git diff-tree -z writes them)", file=sys.stderr)
        return 2
    with open(argv[1], "rb") as listing:
        paths = [path.decode("utf-8", "surrogateescape") for path in listing.read().split(b"\0") if path]
    build = needs_build(paths)
    print(f"build={'true' if build else 'false'}")
    if not build:
        reason = "all of them graph data or documentation"
    elif paths:
        reason = "not all of them graph data or documentation"
    else:
        reason = "none"
    print(f"Changed paths: {len(paths)}, {reason}: build {'runs' if build else 'is skipped'}.", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
