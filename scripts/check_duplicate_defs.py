#!/usr/bin/env python3
"""Report same-short-name definition candidates across all supplied roots.

Definitions in two or more distinct files are candidates even when their source
signatures differ. Namespaces, binder renaming, inference, and bodies are not
compared semantically. This neither proves duplication nor certifies uniqueness.
Only syntactically bare `abbrev X := A.Name` aliases are excluded; unqualified,
typed/applied or ambiguous aliases remain. See source_diagnostics.py for limits.

Exit 1 for candidates, 0 for none; --report-only returns 0 for findings too.
Input/scan errors always exit 2, including empty roots. No Lean is invoked.
"""

import argparse
import sys
from collections import defaultdict
from pathlib import Path

from source_diagnostics import DEFINITION_KINDS, Declaration, ScanError, scan


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report-only",
        action="store_true",
        help="report candidates without failing; scan errors remain fatal",
    )
    parser.add_argument(
        "--require-declarations",
        action="store_true",
        help="fail if no definition declarations were recognized (CI)",
    )
    parser.add_argument("roots", nargs="+", type=Path)
    args = parser.parse_args()
    try:
        file_count, declarations = scan(args.roots)
    except (OSError, UnicodeError, ScanError) as exc:
        print(f"SCAN ERROR: {exc}", file=sys.stderr)
        return 2
    definitions = [decl for decl in declarations if decl.kind in DEFINITION_KINDS]
    if args.require_declarations and not definitions:
        print("SCAN ERROR: no recognized declarations of definitions", file=sys.stderr)
        return 2
    by_name: dict[str, list[Declaration]] = defaultdict(list)
    for decl in definitions:
        if not decl.direct_alias:
            by_name[decl.short_name].append(decl)
    print(
        f"Scanned files: {file_count}; definition declarations: {len(definitions)}; "
        f"direct aliases excluded: {sum(decl.direct_alias for decl in definitions)}"
    )
    groups = 0
    for name, occurrences in sorted(by_name.items()):
        files = {decl.path for decl in occurrences}
        if len(files) < 2:
            continue
        groups += 1
        print(f"CANDIDATE {name}: same short name in {len(files)} files")
        for decl in occurrences:
            print(
                f"  {decl.path}:{decl.line} [{decl.kind}] {decl.name} source signature={decl.signature!r}"
            )
    print(
        f"Candidate groups: {groups} (source diagnostics only; no semantic comparison)"
    )
    return 1 if groups and not args.report_only else 0


if __name__ == "__main__":
    raise SystemExit(main())
