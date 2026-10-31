#!/usr/bin/env python3
"""Week 2 CI: hypothesis-debt detector v0 (90-day plan #1-#7).

Scans Lean files for L1 markers: theorem_wanted / def_wanted /
proof_wanted, and explicit 'hypothesis debt' / 'L1' annotations.
Report only; CI gates on the report being reviewed, not on zero.
Debt only decreases by proving the hypothesis, never by renaming.
Usage: python3 scripts/check_hypothesis_debt.py <dir> [...]
"""
import re, sys, os

WANTED = re.compile(r'\b(theorem_wanted|def_wanted|proof_wanted)\b[ \t]+([A-Za-z0-9_.]+)')
DEBT = re.compile(r'(?i)(hypothesis debt|L1 capstone|assumes?:?\s+[A-Z][A-Za-z ]{3,60})')


def main():
    if len(sys.argv) < 2:
        print("usage: check_hypothesis_debt.py <dir>...")
        return 2
    total = 0
    for root in sys.argv[1:]:
        for dp, _, fn in os.walk(root):
            for f in fn:
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(dp, f)
                try:
                    txt = open(p, encoding="utf-8", errors="replace").read()
                except Exception:
                    continue
                for m in WANTED.finditer(txt):
                    print(f"DEBT {p}: {m.group(1)} {m.group(2)}")
                    total += 1
                for m in DEBT.finditer(txt):
                    print(f"DEBT-MARKER {p}: {m.group(0).strip()[:100]}")
                    total += 1
    print(f"\nTotal debt items: {total}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
