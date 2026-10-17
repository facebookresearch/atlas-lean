#!/usr/bin/env python3
"""Extract target-level Lean dependencies for the v1 wiki from the ATLAS v1 visualizer.

    scripts/extract_v1_lean_dependencies.py <visualizer-commit>

The visualizer at https://rammalahmad.github.io/atlas/ embeds, for every v1
declaration, its statement and proof dependencies collapsed onto the evaluated
textbook targets (`eval_statement_deps`, `eval_proof_deps`), so a chain through
helper lemmas still links the two targets it connects. This keeps only the
target-to-target part and writes blueprint/sources/v1/lean-dependencies.json,
which scripts/generate_wiki.py reads.
"""

from __future__ import annotations

import json
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "blueprint" / "sources" / "v1" / "lean-dependencies.json"
RAW = "https://raw.githubusercontent.com/rammalahmad/rammalahmad.github.io/{commit}/atlas/book/{book}/graph/index.html"
MARKER = "const DATA = "


def book_data(commit: str, book: str) -> dict:
    with urllib.request.urlopen(RAW.format(commit=commit, book=book), timeout=120) as response:
        page = response.read().decode("utf-8")
    data, _ = json.JSONDecoder().raw_decode(page, page.index(MARKER) + len(MARKER))
    return data


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    commit = sys.argv[1]
    books = sorted(path.parent.name for path in (ROOT / "v1" / "Atlas").glob("*/report.json"))
    result: dict[str, object] = {
        "source": "https://github.com/rammalahmad/rammalahmad.github.io",
        "commit": commit,
        "books": {},
    }
    for book in books:
        report = json.loads((ROOT / "v1" / "Atlas" / book / "report.json").read_text())
        targets = {item["lean_declaration"] for item in report["statements"]["details"] if item.get("lean_declaration")}
        nodes = {node["name"]: node for node in book_data(commit, book)["nodes"]}
        entries = {}
        for name in sorted(targets & nodes.keys()):
            statement = sorted(set(nodes[name]["eval_statement_deps"]) & targets - {name})
            proof = sorted(set(nodes[name]["eval_proof_deps"]) & targets - {name} - set(statement))
            if statement or proof:
                entries[name] = {"statement": statement, "proof": proof}
        result["books"][book] = entries
        print(f"{book}: {len(entries)} targets with target dependencies", file=sys.stderr)
    OUTPUT.write_text(json.dumps(result, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
