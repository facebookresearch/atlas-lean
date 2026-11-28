#!/usr/bin/env bash
# Import every compiled module of the libraries the compiled audit checks, test
# libraries included, into one environment, and fail if they do not load together,
# which a name declared by two modules that never import each other can cause. The
# audit imports these modules in groups, and the wiki's dependency dump imports every
# v2 module at once.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

modules="$(mktemp "${TMPDIR:-/tmp}/atlas-v2-modules.XXXXXX")"
trap 'rm -f "$modules" "${roots:-}"' EXIT
roots="$(mktemp "${TMPDIR:-/tmp}/atlas-audited-libraries.XXXXXX")"

# The libraries scripts/audit_compiled_modules.py audits, one per line. They include the
# five that the "Dump declaration dependencies" step of .github/workflows/blueprint-pages.yml
# imports, which scripts/list_v2_modules.sh lists by default.
python3 - "$roots" <<'PY' || {
import re
import sys

sys.path.insert(0, "scripts")
import audit_compiled_modules as audit

libraries = audit.ROOTS
if not libraries or len(set(libraries)) != len(libraries) or not all(
        isinstance(library, str) and re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", library)
        for library in libraries):
    sys.exit(f"invalid audited libraries: {libraries!r}")
with open(sys.argv[1], "w", encoding="utf-8") as output:
    output.write("".join(library + "\n" for library in libraries))
PY
  echo "FAIL [declaration collisions]: could not read the audited libraries" >&2
  exit 1
}
libraries=()
while IFS= read -r library; do
  libraries+=("$library")
done <"$roots"
scripts/list_v2_modules.sh "$modules" "${libraries[@]}" || {
  echo "FAIL [declaration collisions]: could not list the compiled modules" >&2
  exit 1
}
# The list names tracked files; the audit reads every source path that its directory walk
# finds in its libraries.
# Compare the paths themselves: `A/B.lean` and `A.B.lean` flatten to one module name, and
# the .olean of a deleted source can outlive it.
python3 - "$modules" <<'PY'
import sys
from pathlib import Path

sys.path.insert(0, "scripts")
import audit_compiled_modules as audit

root = Path(".")
# The listed modules' directory and file names hold no dot, so each names one path.
# One module per LF-terminated line; `splitlines` would also split at other separators.
modules = Path(sys.argv[1]).read_text(encoding="utf-8").split("\n")
if modules[-1] == "":
    modules.pop()
listed = {module.replace(".", "/") + ".lean" for module in modules}
# The paths audit.inventory reads its module names from.
walked = {path.relative_to(root).as_posix(): path
          for library in audit.ROOTS for path in (root / library).rglob("*.lean")}
problems = [f"{path} is not tracked by Git, but the compiled audit reads it; add it, or "
            "remove it." for path in sorted(walked.keys() - listed)]
problems += [f"{path} is tracked by Git, but the compiled audit's walk of its libraries does "
             "not find it." for path in sorted(listed - walked.keys())]
problems += [f"{path} is not a regular file." for path in sorted(listed & walked.keys())
             if walked[path].is_symlink() or not walked[path].is_file()]
for problem in problems:
    print(f"FAIL [declaration collisions]: {problem}", file=sys.stderr)
if problems:
    sys.exit(1)
# The audit's own checks of its inventory, symlinks and line breaks among them.
try:
    audit.inventory(root)
except audit.AuditFailure as error:
    sys.exit(f"FAIL [declaration collisions]: {error}")
PY
lake env lean --run scripts/check_declaration_collisions.lean "$modules"
