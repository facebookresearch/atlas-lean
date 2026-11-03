#!/usr/bin/env bash
# Canonical validation entry point for the top-level extension libraries.
#
#   scripts/check.sh            run every check
#   scripts/check.sh preflight  run deterministic repository checks
#   scripts/check.sh build      build the Lean libraries
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

scope="${1:-all}"
[[ $# -gt 0 ]] && shift
build_args=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --root)
      [[ $# -ge 2 ]] || exit 2
      REPO_ROOT="$(cd "$2" && pwd)" || exit 2
      build_args+=(--root "$REPO_ROOT"); shift 2 ;;
    --modules)
      [[ $# -ge 2 ]] || exit 2
      if [[ "$2" == /* ]]; then
        build_args+=(--modules "$2")
      else
        build_args+=(--modules "$PWD/$2")
      fi
      shift 2 ;;
    *)
      echo "usage: scripts/check.sh [preflight|build] [--root DIR] [--modules FILE]" >&2
      exit 2 ;;
  esac
done
if [[ "$scope" != build && ${#build_args[@]} -gt 0 ]]; then
  echo "--root and --modules are supported only for build checks" >&2
  exit 2
fi
cd "$REPO_ROOT" || exit 2
case "$scope" in
  all|preflight|build) ;;
  -h|--help)
    sed -n '2,6p' "$SCRIPT_DIR/check.sh"
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
  for path in CSLibExt CSLibExtTest MathlibExt MathlibExtTest WantedExt scripts; do
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
  run_check "compiler diagnostics" bash "$SCRIPT_DIR/check_diagnostics.sh" ${build_args[@]+"${build_args[@]}"}
  run_check "compiled environment policy" bash "$SCRIPT_DIR/check_axioms.sh" ${build_args[@]+"${build_args[@]}"}
fi

exit "$status"
