#!/usr/bin/env bash
# Build every audited library and reject trust-related Lean diagnostics.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

LOG="$(mktemp "${TMPDIR:-/tmp}/atlas-build.XXXXXX.log")"
trap 'rm -f "$LOG"' EXIT

if ! lake build MathlibExt CSLibExt PhyslibExt WantedExt MathlibExtTest CSLibExtTest PhyslibExtTest 2>&1 | tee "$LOG"; then
  echo "FAIL [build]: audited libraries do not build." >&2
  exit 1
fi

violations="$(grep -E \
  "declaration uses .sorry.|Using .native_decide. is not allowed in mathlib" \
  "$LOG" || true)"
if [[ -n "$violations" ]]; then
  echo "FAIL [diagnostics]: forbidden compiler diagnostic:" >&2
  printf '%s\n' "$violations" >&2
  exit 1
fi

echo "ok [diagnostics]: audited libraries build without proof holes or native_decide."
