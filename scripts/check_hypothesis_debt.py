#!/usr/bin/env python3
"""Report line-leading theorem_wanted and def_wanted declarations.

Comments, ordinary strings, and prose annotations are not debt. proof_wanted
is not a supported declaration keyword. This inventories explicit deferred
work only; it cannot detect removable hypotheses or prove debt has decreased.
See source_diagnostics.py for lexical and command-recognition limits.

Exit 1 for findings, 0 for none; --report-only reports findings with exit 0.
Invalid/empty roots and scan errors always exit 2. No Lean is invoked.
"""

import argparse
import sys
from pathlib import Path

from source_diagnostics import WANTED_KINDS, ScanError, scan


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report-only",
        action="store_true",
        help="report wanted declarations without failing; scan errors remain fatal",
    )
    parser.add_argument(
        "--require-declarations",
        action="store_true",
        help="fail if no wanted declarations were recognized (CI)",
    )
    parser.add_argument("roots", nargs="+", type=Path)
    args = parser.parse_args()
    try:
        file_count, declarations = scan(args.roots)
    except (OSError, UnicodeError, ScanError) as exc:
        print(f"SCAN ERROR: {exc}", file=sys.stderr)
        return 2
    wanted = [decl for decl in declarations if decl.kind in WANTED_KINDS]
    if args.require_declarations and not wanted:
        print("SCAN ERROR: no recognized declarations of wanted work", file=sys.stderr)
        return 2
    print(
        f"Scanned files: {file_count}; recognized declarations: {len(declarations)}; "
        f"wanted declarations: {len(wanted)}"
    )
    for decl in wanted:
        print(f"DEBT {decl.path}:{decl.line}: {decl.kind} {decl.name}")
    print(f"Total debt items: {len(wanted)}")
    return 1 if wanted and not args.report_only else 0


if __name__ == "__main__":
    raise SystemExit(main())
