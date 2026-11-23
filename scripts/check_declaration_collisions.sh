#!/usr/bin/env bash
# Import every compiled v2 module together, as the wiki's dependency dump does, so
# that two modules which never import each other cannot declare the same name.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

modules="$(mktemp "${TMPDIR:-/tmp}/atlas-v2-modules.XXXXXX")"
trap 'rm -f "$modules"' EXIT

# The same list as the "Dump declaration dependencies" step of
# .github/workflows/blueprint-pages.yml.
scripts/list_v2_modules.sh "$modules" || {
  echo "FAIL [declaration collisions]: could not list the compiled v2 modules" >&2
  exit 1
}
lake env lean --run scripts/check_declaration_collisions.lean "$modules"
