#!/usr/bin/env bash
# Import every compiled v2 module together, as the wiki's dependency dump does, so
# that two modules which never import each other cannot declare the same name.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

olean_root=.lake/build/lib/lean
[ -d "$olean_root" ] || olean_root=.lake/build/lib
modules="$(mktemp "${TMPDIR:-/tmp}/atlas-v2-modules.XXXXXX")"
trap 'rm -f "$modules"' EXIT

# The same modules as the "Dump declaration dependencies" step of
# .github/workflows/blueprint-pages.yml.
while IFS= read -r -d '' source; do
  module="${source%.lean}"
  module="${module//\//.}"
  test -f "$olean_root/${source%.lean}.olean" || {
    echo "FAIL [declaration collisions]: missing compiled module: $source" >&2
    exit 1
  }
  echo "$module" >> "$modules"
done < <(git ls-files -z 'MathlibExt/*.lean' 'CSLibExt/*.lean' 'PhyslibExt/*.lean' 'Domains/*.lean' 'WantedExt/*.lean')
test -s "$modules" || {
  echo "FAIL [declaration collisions]: no v2 module is tracked" >&2
  exit 1
}
lake env lean --run scripts/check_declaration_collisions.lean "$modules"
