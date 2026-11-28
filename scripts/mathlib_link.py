#!/usr/bin/env python3
"""Markdown links to Mathlib declarations, in the form the site turns into links to its Mathlib pages.

    python scripts/mathlib_link.py GRAPH NAME...

GRAPH is the `mathlib-graph` artifact (docs/mathlib-layer.md). For each NAME, an exact Lean name of a node of
that graph, this prints

    [NAME](https://github.com/leanprover-community/mathlib4/blob/<revision>/<Module/Path>.lean#L<line> "NAME")

the line of the declaration's name in Mathlib's source at the graph's revision, with the name as the link's title.
The address works on every site; scripts/build_mathlib_pages.py points such a link at the declaration's Mathlib
page when the site has one. A name that is not a node is reported and makes the command fail; nothing is guessed.
docs/mathlib-pages.md describes the link scheme.
"""

from __future__ import annotations

import argparse
import gzip
import json
import re
import sys
from pathlib import Path

MATHLIB_GIT = "https://github.com/leanprover-community/mathlib4"
# Every node's name is made of letters, digits and . _ ' ? !, which a double-quoted Markdown title holds as is.
TITLE_SAFE = re.compile(r"[^\s\"\\()\[\]<>]+")


def links(graph: Path, names: list[str]) -> tuple[list[str], list[str]]:
    rev = json.loads((graph / "stats.json").read_text(encoding="utf-8"))["versions"]["mathlib_rev"]
    if not re.fullmatch(r"[0-9a-f]{40}", rev or ""):
        raise SystemExit(f"{graph}/stats.json: revision {rev!r} is not a full commit")
    wanted = set(names)
    found: dict[str, str] = {}
    with gzip.open(graph / "nodes.jsonl.gz", "rt", encoding="utf-8") as handle:
        for line in handle:
            row = json.loads(line)
            if row["name"] in wanted:
                path = row["module"].replace(".", "/")
                found[row["name"]] = f"{MATHLIB_GIT}/blob/{rev}/{path}.lean#L{row['name_line']}"
    printed, missing = [], []
    for name in names:
        if name not in found:
            missing.append(f"{name}: not a Mathlib node of {graph}")
        elif not TITLE_SAFE.fullmatch(name):
            missing.append(f"{name}: cannot be a Markdown link title as it is")
        else:
            printed.append(f'[{name}]({found[name]} "{name}")')
    return printed, missing


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("graph", type=Path, help="the mathlib-graph artifact")
    parser.add_argument("names", nargs="+", help="exact Lean names of Mathlib declarations")
    args = parser.parse_args(argv)
    printed, missing = links(args.graph, args.names)
    for line in printed:
        print(line)
    for line in missing:
        print(line, file=sys.stderr)
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
