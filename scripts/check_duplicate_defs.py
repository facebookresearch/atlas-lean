#!/usr/bin/env python3
"""Week 2 CI: duplicate-definition check (90-day plan #1-#7).

Rules: same short name + same normalized type in >=2 homes -> BLOCK
(must alias). Same short name + DIFFERENT normalized type -> BLOCK with
semantic-conflict label (must qualify/bridge, never silent-alias).
Alias shims (abbrev X := Canonical) are not homes.

LIMITATION (v0): groups by SHORT name, ignoring namespace, so it over-flags
namespaced defs already distinct when fully qualified (e.g.
BernoulliMixture.Params vs GaussianMixture.Params). Flags are CANDIDATES
for human review, not proof of duplication.
Usage: python3 scripts/check_duplicate_defs.py <dir> [...]
Exit 1 if any block, else 0.
"""
import re, sys, os
from collections import defaultdict

DECL = re.compile(
    r'^[ \t]*(?:@\[[^\]\n]*\][ \t]*\n?[ \t]*)*'
    r'(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public|meta)[ \t]+)*'
    r'(def|abbrev|structure|class|inductive)[ \t]+([^\s:({\[]+)',
    re.M)
ALIAS = re.compile(r'^\s*abbrev\s+(\S+)\s*:?=[ \t]*([A-Za-z0-9_.]+)\s*$', re.M)


def strip_comments(s):
    out, i, n, depth, in_str = [], 0, len(s), 0, False
    while i < n:
        c = s[i]
        if depth:
            if s.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if s.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if c == "\n":
                out.append("\n")
            i += 1
            continue
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if s.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            if j < 0:
                break
            i = j
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def norm_sig(code, m):
    tail = code[m.end():m.end() + 400].split(":=")[0].split("where")[0]
    return re.sub(r'\s+', ' ', tail).strip()[:200]


def scan(root):
    by_name = defaultdict(list)
    for dp, _, fn in os.walk(root):
        for f in fn:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            try:
                raw = open(p, encoding="utf-8", errors="replace").read()
            except Exception:
                continue
            code = strip_comments(raw)
            for m in DECL.finditer(code):
                kind, name = m.group(1), m.group(2).split(".")[-1]
                if kind == "abbrev" and ALIAS.search(code[m.start():m.start() + 300]):
                    continue
                by_name[name].append((p, kind, norm_sig(code, m)))
    return by_name


def main():
    if len(sys.argv) < 2:
        print("usage: check_duplicate_defs.py <dir>...")
        return 2
    blocks = 0
    for root in sys.argv[1:]:
        for name, occ in sorted(scan(root).items()):
            files = {p for p, _, _ in occ}
            if len(files) < 2:
                continue
            sigs = {sig for _, _, sig in occ if sig}
            if len(sigs) <= 1:
                print(f"BLOCK duplicate: {name} — same signature "
                      f"in {len(files)} files:")
                blocks += 1
            else:
                print(f"BLOCK semantic-conflict: {name} — DIFFERENT "
                      f"signatures in {len(files)} files "
                      f"(qualify/bridge, never silent-alias):")
                blocks += 1
            for p, kind, sig in sorted(occ):
                print(f"    {p} [{kind}] sig={sig!r}")
    print(f"\n{'FAIL: %d block(s)' % blocks if blocks else 'PASS: no duplicate blocks'}")
    return 1 if blocks else 0


if __name__ == "__main__":
    raise SystemExit(main())
