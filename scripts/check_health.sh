#!/usr/bin/env bash
# Guard the declared-library list against policy drift.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

LIBRARIES=(CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest WantedExt)

check_build_surface() {
  PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_lake_surface.py
}

check_declared_libraries() {
  local declared expected
  declared="$(awk '
    /^\[\[lean_lib\]\]/ { inlib = 1; next }
    /^\[/               { inlib = 0 }
    inlib && /^name[[:space:]]*=/ {
      match($0, /"[^"]+"/)
      print substr($0, RSTART + 1, RLENGTH - 2)
      inlib = 0
    }' lakefile.toml | LC_ALL=C sort | tr '\n' ' ')"
  expected="$(printf '%s\n' "${LIBRARIES[@]}" | LC_ALL=C sort | tr '\n' ' ')"
  if [[ "$declared" != "$expected" ]]; then
    echo "FAIL [libraries]: lakefile libraries ($declared) do not match policy ($expected)." >&2
    return 1
  fi
  echo "ok [libraries]: every declared library has a policy."
}

check_no_symlinks() {
  local hits
  hits="$(find CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest WantedExt \
    -type l -print | LC_ALL=C sort)"
  if [[ -n "$hits" ]]; then
    echo "FAIL [symlinks]: audited libraries must not contain symlinked paths." >&2
    printf '%s\n' "$hits" | sed 's/^/  /' >&2
    return 1
  fi
  echo "ok [symlinks]: audited libraries contain no symlinked paths."
}

status=0
check_build_surface || status=1
check_declared_libraries || status=1
check_no_symlinks || status=1
exit "$status"
