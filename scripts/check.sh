#!/usr/bin/env bash
# Canonical validation entry point for the top-level extension libraries.
#
#   scripts/check.sh            run every check
#   scripts/check.sh preflight  run deterministic repository checks
#   scripts/check.sh build      build the Lean libraries
#
# Every check runs and every failure is reported, unless ATLAS_CHECK_FAIL_FAST=1:
# then the script stops at the first failing check. CI sets it for merge groups.
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
    sed -n '2,9p' "${BASH_SOURCE[0]}"
    exit 0
    ;;
  *)
    echo "unknown check scope: $scope (expected preflight or build)" >&2
    exit 2
    ;;
esac
fail_fast="${ATLAS_CHECK_FAIL_FAST-0}"
case "$fail_fast" in
  0|1) ;;
  *)
    echo "ATLAS_CHECK_FAIL_FAST must be 0 or 1, not '${fail_fast}'" >&2
    exit 2
    ;;
esac

status=0
run_check() {
  local label="$1"
  shift
  echo "==> $label"
  if ! "$@"; then
    status=1
    if [[ "$fail_fast" == 1 ]]; then
      echo "Stopped at the first failing check, $label (ATLAS_CHECK_FAIL_FAST=1); the checks after it did not run." >&2
      exit "$status"
    fi
  fi
}

check_structure() {
  local path
  for path in CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest Domains DomainsTest WantedExt scripts; do
    if [[ ! -d "$path" ]]; then
      echo "missing required directory: $path" >&2
      return 1
    fi
  done
  for path in \
    lakefile.toml lake-manifest.json lean-toolchain README.md REVIEWING.md \
    scripts/check_axioms.sh scripts/check_axioms.lean scripts/audit_compiled_modules.py \
    scripts/check_diagnostics.sh scripts/check_health.sh \
    scripts/check_declaration_collisions.sh scripts/check_declaration_collisions.lean \
    scripts/list_v2_modules.sh \
    scripts/check_lake_surface.py scripts/check_copyright.py scripts/test_scripts.sh; do
    if [[ ! -f "$path" ]]; then
      echo "missing required file: $path" >&2
      return 1
    fi
  done
}

# `bash -n` parses only its first operand (the others become its arguments),
# so parse each script separately.
check_shell_syntax() {
  local path failed=0
  for path in "$@"; do
    bash -n "$path" || failed=1
  done
  return "$failed"
}

if [[ "$scope" == all || "$scope" == preflight ]]; then
  run_check "repository structure" check_structure
  run_check "shell syntax" check_shell_syntax scripts/*.sh
  run_check "maintenance script regressions" scripts/test_scripts.sh
  run_check "library policy" scripts/check_health.sh
  run_check "copyright headers" python3 scripts/check_copyright.py --all
  # Scoped to files synced from formal-math (see provenance/README.md): files without a manifest
  # row are ignored, so only a PR that changes or deletes a synced file must record it.
  run_check "formal-math sync manifest" python3 scripts/check_formal_math_sync.py
fi

if [[ "$scope" == all || "$scope" == build ]]; then
  run_check "compiler diagnostics" scripts/check_diagnostics.sh
  # This check loads every module the compiled-policy audit checks into one environment,
  # so that modules which do not load together fail the build. It needs the .olean files
  # that the build above writes and nothing that the audit produces, so it runs first: the
  # audit takes longer, and imports modules in groups, where a name that two modules
  # declare can make it split a group, which only slows it down.
  run_check "declaration collisions" scripts/check_declaration_collisions.sh
  run_check "compiled environment policy" scripts/check_axioms.sh
fi

exit "$status"
