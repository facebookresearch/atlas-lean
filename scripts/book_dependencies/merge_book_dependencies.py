#!/usr/bin/env python3
"""Keep the verified book-derived edges for one book and write them into the vault.

    merge_book_dependencies.py WORK BOOK

Reads WORK/book-deps/<Book>.proposed.json and .verified.json (or every
<Book>.partN pair for a book split across agents); writes
blueprint/sources/v1/book-dependencies/<Book>.json
with every confirmed edge, reclassified edges under their corrected kind, and
no rejected ones.
"""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main() -> int:
    work, book = Path(sys.argv[1]), sys.argv[2]
    deps = work / "book-deps"
    parts = sorted(deps.glob(f"{book}.part*.proposed.json")) or [deps / f"{book}.proposed.json"]
    edges, verdicts = [], []
    for part in parts:
        proposed = json.loads(part.read_text())
        verified = json.loads(part.with_name(part.name.replace(".proposed.", ".verified.")).read_text())
        if len(proposed["edges"]) != len(verified["verdicts"]):
            raise SystemExit(f"{part.name}: {len(proposed['edges'])} edges but {len(verified['verdicts'])} verdicts")
        edges += proposed["edges"]
        verdicts += verified["verdicts"]
    kept, seen = [], set()
    for edge, verdict in zip(edges, verdicts):
        if (edge["from"], edge["to"], edge["kind"]) != (verdict["from"], verdict["to"], verdict["kind"]):
            raise SystemExit(f"verdict out of order at {edge} / {verdict}")
        if verdict["verdict"] == "rejected":
            continue
        kind = verdict.get("new_kind") if verdict["verdict"] == "reclassify" else edge["kind"]
        if kind not in ("statement", "proof") or (edge["from"], edge["to"]) in seen:
            continue
        seen.add((edge["from"], edge["to"]))
        kept.append({key: edge[key] for key in ("from", "to", "evidence", "quote")} | {"kind": kind})
    output = ROOT / "blueprint" / "sources" / "v1" / "book-dependencies" / f"{book}.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    document = {
        "book": book,
        "source": proposed["source"],
        "method": "Extracted from the source text by one agent and checked edge by edge by a second; "
        "rejected edges are dropped.",
        "edges": sorted(kept, key=lambda edge: (edge["from"], edge["to"])),
    }
    output.write_text(json.dumps(document, indent=1, ensure_ascii=False) + "\n")
    print(f"{book}: kept {len(kept)} of {len(edges)} proposed edges -> {output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
