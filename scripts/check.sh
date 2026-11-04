#!/usr/bin/env bash
# Canonical validation entry point for the top-level extension libraries.
#
#   scripts/check.sh            run every check
#   scripts/check.sh preflight  run deterministic repository checks
#   scripts/check.sh build      build the Lean libraries
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

scope="${1:-all}"
if [[ $# -gt 1 ]]; then
  echo "usage: scripts/check.sh [preflight|build]" >&2
  exit 2
fi
case "$scope" in
  all|preflight|build) ;;
  -h|--help)
    sed -n '2,6p' "${BASH_SOURCE[0]}"
    exit 0
    ;;
  *)
    echo "unknown check scope: $scope (expected preflight or build)" >&2
    exit 2
    ;;
esac

status=0
run_check() {
  local label="$1"
  shift
  echo "==> $label"
  "$@" || status=1
}

check_structure() {
  local path
  for path in CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest WantedExt scripts; do
    if [[ ! -d "$path" ]]; then
      echo "missing required directory: $path" >&2
      return 1
    fi
  done
  for path in \
    lakefile.toml lake-manifest.json lean-toolchain README.md REVIEWING.md \
    scripts/check_axioms.sh scripts/check_diagnostics.sh scripts/check_health.sh \
    scripts/check_lake_surface.py scripts/check_copyright.py scripts/test_scripts.sh; do
    if [[ ! -f "$path" ]]; then
      echo "missing required file: $path" >&2
      return 1
    fi
  done
}

if [[ "$scope" == all || "$scope" == preflight ]]; then
  run_check "repository structure" check_structure
  run_check "shell syntax" \
    bash -n \
      scripts/check.sh scripts/check_axioms.sh scripts/check_diagnostics.sh \
      scripts/check_health.sh scripts/test_scripts.sh
  run_check "maintenance script regressions" scripts/test_scripts.sh
  run_check "library policy" scripts/check_health.sh
  run_check "copyright headers" python3 scripts/check_copyright.py --all
fi

if [[ "$scope" == all || "$scope" == build ]]; then
  run_check "compiler diagnostics" scripts/check_diagnostics.sh
  run_check "compiled environment policy" scripts/check_axioms.sh
fi

exit "$status"
