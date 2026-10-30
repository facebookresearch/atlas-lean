#!/usr/bin/env bash
# Regression tests for repository-maintenance scripts. These tests need only
# Bash, Python 3.11, and standard Unix tools; they intentionally do not invoke
# Lean.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/atlas-scripts.XXXXXX")"
trap 'rm -rf "$TMP_ROOT"' EXIT

fail() {
  echo "FAIL [scripts]: $*" >&2
  exit 1
}

reset_fixture() {
  rm -rf "$TMP_ROOT/repo"
  mkdir -p "$TMP_ROOT/repo"/{CSLibExt,CSLibExtTest,MathlibExt,MathlibExtTest,PhyslibExt,PhyslibExtTest,WantedExt,scripts,v1}
  cp "$REPO_ROOT/lakefile.toml" "$TMP_ROOT/repo/"
  cp "$REPO_ROOT/lake-manifest.json" "$TMP_ROOT/repo/"
  cp \
    "$REPO_ROOT/scripts/check_axioms.sh" \
    "$REPO_ROOT/scripts/check_health.sh" \
    "$REPO_ROOT/scripts/check_lake_surface.py" \
    "$TMP_ROOT/repo/scripts/"
  printf '%s\n' 'def archived : Nat := 1' >"$TMP_ROOT/repo/v1/Archived.lean"
}

expect_pass() {
  local description="$1"
  if ! "$TMP_ROOT/repo/scripts/check_health.sh" >"$TMP_ROOT/output.log" 2>&1; then
    cat "$TMP_ROOT/output.log" >&2
    fail "$description failed"
  fi
}

expect_failure() {
  local description="$1" pattern="$2"
  if "$TMP_ROOT/repo/scripts/check_health.sh" >"$TMP_ROOT/output.log" 2>&1; then
    fail "$description unexpectedly passed"
  fi
  grep -q -- "$pattern" "$TMP_ROOT/output.log" || {
    cat "$TMP_ROOT/output.log" >&2
    fail "$description produced the wrong diagnostic"
  }
}

replace_once() {
  python3 - "$TMP_ROOT/repo/lakefile.toml" "$1" "$2" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
old, new = sys.argv[2:]
source = path.read_text()
if source.count(old) != 1:
    raise SystemExit(f"expected one occurrence of {old!r}")
path.write_text(source.replace(old, new))
PY
}

reset_fixture
expect_pass "empty scaffold"

reset_fixture
printf '%s\n' '@[default_target] lean_exe Archive where' '  root := `v1.Archived' \
  >"$TMP_ROOT/repo/lakefile.lean"
expect_failure "archived Lean lakefile target" 'build surface'

reset_fixture
python3 - "$TMP_ROOT/repo/lake-manifest.json" <<'PY'
import json
import sys

path = sys.argv[1]
with open(path) as source:
    manifest = json.load(source)
mathlib = next(
    package for package in manifest["packages"] if package["name"] == "mathlib"
)
mathlib.clear()
mathlib.update({
    "type": "path",
    "name": "mathlib",
    "scope": "leanprover-community",
    "dir": "v1",
    "manifestFile": "lake-manifest.json",
    "inherited": False,
    "configFile": "lakefile.toml",
})
with open(path, "w") as output:
    json.dump(manifest, output)
PY
expect_failure "archived manifest dependency" 'build surface'

reset_fixture
replace_once \
  'defaultTargets = ["MathlibExt", "CSLibExt", "PhyslibExt", "WantedExt"]' \
  'defaultTargets = ["v1"]'
expect_failure "archived default target" 'build surface'

reset_fixture
replace_once 'testDriver = "MathlibExtTest"' 'testDriver = "v1"'
expect_failure "archived test driver" 'build surface'

reset_fixture
replace_once 'globs = ["MathlibExt.+"]' 'globs = ["v1.+"]'
expect_failure "archived library glob" 'build surface'

reset_fixture
printf '%s\n' 'srcDir = "v1"' >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "archived library source directory" 'build surface'

reset_fixture
printf '%s\n' '"srcDir" = "v1"' >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "quoted archived library source directory" 'build surface'

reset_fixture
printf '%s\n' '"src\u0044ir" = "v1"' >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "escaped archived library source directory" 'build surface'

reset_fixture
printf '%s\n' "'roots' = ['v1']" >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "quoted archived library roots" 'build surface'

reset_fixture
printf '%s\n' '[[require]]' 'name = "archive"' 'path = "v1"' \
  >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "archived local requirement" 'build surface'

reset_fixture
printf '%s\n' '[[require]]' 'name = "archive"' 'path = "././v1/dependency"' \
  >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "nested archived local requirement" 'build surface'

reset_fixture
printf '%s\n' '[[require]]' 'name = "archive"' '"path" = "v1/dependency"' \
  >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "quoted archived local requirement" 'build surface'

reset_fixture
printf '%s\n' \
  '[[require]]' \
  'name = "archive"' \
  'source = { type = "path", dir = "v1" }' \
  >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "archived source-table requirement" 'build surface'

reset_fixture
printf '%s\n' '[[ "lean_lib" ]]' 'name = "Archive"' 'globs = ["v1.+"]' \
  >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "quoted archived library table" 'build surface'

reset_fixture
printf '%s\n' \
  'needs = ["Archive"]' \
  '[[lean_exe]]' \
  'name = "Archive"' \
  'root = "v1.Archived"' \
  >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "archived dependency target" 'build surface'

reset_fixture
printf '%s\n' '[[lean_lib]]' 'name = "Undocumented"' >>"$TMP_ROOT/repo/lakefile.toml"
expect_failure "library without policy" 'do not match policy'

reset_fixture
printf '%s\n' 'axiom hidden : Prop' >"$TMP_ROOT/linked.lean"
ln -s "$TMP_ROOT/linked.lean" "$TMP_ROOT/repo/MathlibExt/Linked.lean"
expect_failure "symlinked Lean source" 'symlinked paths'

reset_fixture
ln -s "$TMP_ROOT/linked.lean" "$TMP_ROOT/repo/CSLibExt/Linked.lean"
expect_failure "symlinked CSLibExt source" 'symlinked paths'

reset_fixture
ln -s "$TMP_ROOT/linked.lean" "$TMP_ROOT/repo/CSLibExtTest/Linked.lean"
expect_failure "symlinked CSLibExtTest source" 'symlinked paths'

reset_fixture
ln -s "$TMP_ROOT/linked.lean" "$TMP_ROOT/repo/PhyslibExt/Linked.lean"
expect_failure "symlinked PhyslibExt source" 'symlinked paths'

FAKE_BIN="$TMP_ROOT/bin"
FAKE_LAKE_LOG="$TMP_ROOT/lake.log"
mkdir -p "$FAKE_BIN"
cat >"$FAKE_BIN/lake" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "$*" >>"$FAKE_LAKE_LOG"
if [[ "${1:-}" == "env" && "${2:-}" == "lean" ]]; then
  cp "$3" "$FAKE_LEAN_INPUT"
fi
printf '%s\n' "${FAKE_LAKE_OUTPUT:-Build completed successfully.}"
exit "${FAKE_LAKE_STATUS:-0}"
SH
chmod +x "$FAKE_BIN/lake"
FAKE_LEAN_INPUT="$TMP_ROOT/lean-input.lean"
export FAKE_LAKE_LOG FAKE_LEAN_INPUT

if ! PATH="$FAKE_BIN:$PATH" "$REPO_ROOT/scripts/check_diagnostics.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  cat "$TMP_ROOT/output.log" >&2
  fail "clean compiler diagnostics failed"
fi
grep -qx 'build MathlibExt CSLibExt PhyslibExt WantedExt MathlibExtTest CSLibExtTest PhyslibExtTest' "$FAKE_LAKE_LOG" ||
  fail "compiler diagnostics built the wrong targets"
[[ "$(wc -l <"$FAKE_LAKE_LOG")" -eq 1 ]] ||
  fail "compiler diagnostics invoked Lake more than once"
grep -q 'Build completed successfully' "$TMP_ROOT/output.log" ||
  fail "compiler diagnostics hid live build output"

if env PATH="$FAKE_BIN:$PATH" FAKE_LAKE_STATUS=17 \
  "$REPO_ROOT/scripts/check_diagnostics.sh" >"$TMP_ROOT/output.log" 2>&1; then
  fail "failed Lake build unexpectedly passed"
fi
grep -q 'FAIL \[build\]' "$TMP_ROOT/output.log" ||
  fail "failed Lake build produced the wrong diagnostic"

if env PATH="$FAKE_BIN:$PATH" \
  FAKE_LAKE_OUTPUT="warning: MathlibExt/Bad.lean:1:1: declaration uses 'sorry'" \
  "$REPO_ROOT/scripts/check_diagnostics.sh" >"$TMP_ROOT/output.log" 2>&1; then
  fail "sorry diagnostic unexpectedly passed"
fi
grep -q 'forbidden compiler diagnostic' "$TMP_ROOT/output.log" ||
  fail "sorry diagnostic produced the wrong failure"

if env PATH="$FAKE_BIN:$PATH" \
  FAKE_LAKE_OUTPUT='warning: Using `native_decide` is not allowed in mathlib' \
  "$REPO_ROOT/scripts/check_diagnostics.sh" >"$TMP_ROOT/output.log" 2>&1; then
  fail "native_decide diagnostic unexpectedly passed"
fi
grep -q 'forbidden compiler diagnostic' "$TMP_ROOT/output.log" ||
  fail "native_decide diagnostic produced the wrong failure"

reset_fixture
for library in CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest WantedExt; do
  printf '%s\n' 'def sentinel : Nat := 1' \
    >"$TMP_ROOT/repo/$library/Sentinel.lean"
done
: >"$FAKE_LAKE_LOG"
if ! PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_axioms.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  cat "$TMP_ROOT/output.log" >&2
  fail "scoped axiom input failed"
fi
for module in \
  CSLibExt.Sentinel CSLibExtTest.Sentinel \
  MathlibExt.Sentinel MathlibExtTest.Sentinel \
  PhyslibExt.Sentinel PhyslibExtTest.Sentinel WantedExt.Sentinel; do
  grep -qx "import $module" "$FAKE_LEAN_INPUT" ||
    fail "axiom input omitted $module"
done
if grep -q '^import v1\.' "$FAKE_LEAN_INPUT"; then
  fail "axiom input included archived v1 source"
fi

if grep -q 'github\.event\.pull_request\.draft' \
  "$REPO_ROOT/.github/workflows/ci.yml"; then
  fail "CI build excludes draft pull requests"
fi

# Copyright headers: the Meta header or another project's copyright and license
# header passes, anything else fails, and --base checks only changed files.
COPY="$TMP_ROOT/copyright"
rm -rf "$COPY" && mkdir -p "$COPY"
python3 - "$REPO_ROOT/scripts/check_copyright.py" "$COPY" <<'PY'
import importlib.util, sys
from pathlib import Path
spec = importlib.util.spec_from_file_location("c", sys.argv[1]); c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
d = Path(sys.argv[2]); body = "import Mathlib\n\ndef x : Nat := 1\n"
apache = "/-\nCopyright 2026 The Formal Conjectures Authors.\n\nLicensed under the Apache License, Version 2.0.\n-/\n"
(d / "Meta.lean").write_text(c.META + "\n" + body)
(d / "Apache.lean").write_text(apache + "\n" + body)
(d / "None.lean").write_text(body)
(d / "Doc.lean").write_text("/-! module doc -/\n" + body)
(d / "Altered.lean").write_text(c.META.replace("All rights reserved.\n", "") + "\n" + body)
PY
check_copyright() { (cd "$COPY" && python3 "$REPO_ROOT/scripts/check_copyright.py" "$@") >"$TMP_ROOT/output.log" 2>&1; }
check_copyright Meta.lean Apache.lean || { cat "$TMP_ROOT/output.log" >&2; fail "valid copyright headers were rejected"; }
for case in "None.lean:missing copyright header" "Doc.lean:missing copyright header" \
    "Altered.lean:differs from the standard text"; do
  if check_copyright "${case%%:*}"; then fail "${case%%:*} passed the copyright check"; fi
  grep -q -- "${case#*:}" "$TMP_ROOT/output.log" || { cat "$TMP_ROOT/output.log" >&2; fail "${case%%:*}: wrong diagnostic"; }
done
check_copyright --fix None.lean && check_copyright None.lean ||
  fail "--fix did not add an accepted header"
grep -q '^def x : Nat := 1$' "$COPY/None.lean" || fail "--fix changed the file body"
(cd "$COPY" && git init -q && git add Meta.lean Doc.lean && git -c user.name=t -c user.email=t@t commit -qm base &&
  printf 'def y : Nat := 2\n' >New.lean && git add New.lean && git -c user.name=t -c user.email=t@t commit -qm new)
if check_copyright --base HEAD~1; then fail "--base passed a new file without a header"; fi
grep -q 'New.lean' "$TMP_ROOT/output.log" || fail "--base did not report the new file"
if grep -q 'Doc.lean' "$TMP_ROOT/output.log"; then fail "--base checked an unchanged file"; fi
if check_copyright --all; then fail "--all passed a repository with a file without a header"; fi
grep -q 'New.lean' "$TMP_ROOT/output.log" || fail "--all did not report the file without a header"
(cd "$COPY" && git rm -q --cached Doc.lean New.lean && rm -f Doc.lean New.lean)
check_copyright --all || { cat "$TMP_ROOT/output.log" >&2; fail "--all rejected a repository whose files all have headers"; }
grep -q 'check_copyright.py --all' "$REPO_ROOT/scripts/check.sh" ||
  fail "preflight does not check every file's copyright header"

echo "ok [scripts]: repository policy regression tests passed."
