#!/usr/bin/env bash
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

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
  mkdir -p "$TMP_ROOT/repo"/{CSLibExt,CSLibExtTest,MathlibExt,MathlibExtTest,PhyslibExt,PhyslibExtTest,Domains,DomainsTest,WantedExt,scripts,v1}
  cp "$REPO_ROOT/lakefile.toml" "$TMP_ROOT/repo/"
  cp "$REPO_ROOT/lake-manifest.json" "$TMP_ROOT/repo/"
  cp \
    "$REPO_ROOT/scripts/check_axioms.sh" \
    "$REPO_ROOT/scripts/check_axioms.lean" \
    "$REPO_ROOT/scripts/audit_compiled_modules.py" \
    "$REPO_ROOT/scripts/audit_rebuilt_modules.py" \
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

# An older PR may add a standalone model that imports nothing from the old tree.
for roots in MathlibExt:Domains MathlibExtTest:DomainsTest; do
  old="${roots%:*}/Transport/NewArea"
  new="${roots#*:}/Transport/NewArea"
  mkdir -p "$TMP_ROOT/repo/$old" "$TMP_ROOT/repo/$new"
  touch "$TMP_ROOT/repo/$old/NewModel.lean"
  expect_failure "addition to a migrated subject" "move $old/NewModel.lean to $new/NewModel.lean"
  mv "$TMP_ROOT/repo/$old/NewModel.lean" "$TMP_ROOT/repo/$new/"
  expect_pass "addition at the new path"
done

# The fixture runs preflight without recursively running this test suite.
cp "$REPO_ROOT/scripts/"{check.sh,check_diagnostics.sh,check_declaration_collisions.sh,check_declaration_collisions.lean,list_v2_modules.sh} \
  "$TMP_ROOT/repo/scripts/"
touch "$TMP_ROOT/repo/"{lean-toolchain,README.md,REVIEWING.md}
touch "$TMP_ROOT/repo/scripts/"{check_copyright.py,check_formal_math_sync.py}
printf '#!/usr/bin/env bash\nexit 0\n' >"$TMP_ROOT/repo/scripts/test_scripts.sh"
chmod +x "$TMP_ROOT/repo/scripts/test_scripts.sh"
# LC_ALL=C keeps bash's syntax-error messages untranslated for the greps below.
run_preflight() {
  LC_ALL=C "$TMP_ROOT/repo/scripts/check.sh" preflight \
    >"$TMP_ROOT/output.log" 2>&1
}
if ! run_preflight; then
  cat "$TMP_ROOT/output.log" >&2
  fail "preflight failed with valid shell scripts"
fi
printf '\nif then\n' >>"$TMP_ROOT/repo/scripts/check_diagnostics.sh"
if run_preflight; then
  fail "preflight did not detect a syntax error in check_diagnostics.sh"
fi
grep -q 'check_diagnostics.sh:.*syntax error' "$TMP_ROOT/output.log" || {
  cat "$TMP_ROOT/output.log" >&2
  fail "preflight reported the wrong shell syntax diagnostic"
}
# A script added to scripts/ is checked without being listed anywhere.
cp "$REPO_ROOT/scripts/check_diagnostics.sh" "$TMP_ROOT/repo/scripts/"
printf 'if then\n' >"$TMP_ROOT/repo/scripts/new_check.sh"
if run_preflight; then
  fail "preflight did not detect a syntax error in a new script"
fi
grep -q 'new_check.sh:.*syntax error' "$TMP_ROOT/output.log" || {
  cat "$TMP_ROOT/output.log" >&2
  fail "preflight reported the wrong diagnostic for a new script"
}

PHYSLIB_SOURCE='git = "https://github.com/leanprover-community/physlib"'
PHYSLIB_REV="$(python3 - "$REPO_ROOT/lakefile.toml" <<'PY'
import sys
import tomllib

with open(sys.argv[1], "rb") as source:
    config = tomllib.load(source)
print(next(dep["rev"] for dep in config["require"] if dep["name"] == "Physlib"))
PY
)"

reset_fixture
replace_once "$PHYSLIB_SOURCE" 'git = "https://github.com/example/physlib"'
expect_failure "Physlib requirement with wrong repository" 'build surface'

reset_fixture
replace_once "$PHYSLIB_SOURCE" 'scope = "leanprover-community"'
expect_failure "scoped Physlib requirement" 'build surface'

reset_fixture
replace_once "$PHYSLIB_SOURCE" "$PHYSLIB_SOURCE"$'\nscope = "leanprover-community"'
expect_failure "Physlib requirement with both git and scope" 'build surface'

reset_fixture
replace_once "$PHYSLIB_SOURCE"$'\n'"rev = \"$PHYSLIB_REV\"" "$PHYSLIB_SOURCE"$'\nrev = "main"'
expect_failure "unpinned Physlib requirement" 'build surface'

reset_fixture
replace_once "$PHYSLIB_SOURCE" 'path = "v1"'
expect_failure "redirected Physlib requirement" 'build surface'

for field in url scope rev subDir; do
  reset_fixture
  python3 - "$TMP_ROOT/repo/lake-manifest.json" "$field" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
field = sys.argv[2]
manifest = json.loads(path.read_text())
physlib = next(package for package in manifest["packages"] if package["name"] == "Physlib")
value = {
    "url": "https://github.com/example/physlib",
    "scope": "leanprover-community",
    "rev": "main",
    "subDir": "v1",
}[field]
assert physlib[field] != value
physlib[field] = value
path.write_text(json.dumps(manifest))
PY
  expect_failure "Physlib manifest with altered $field" 'build surface'
done

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
  'defaultTargets = ["MathlibExt", "CSLibExt", "PhyslibExt", "Domains", "WantedExt"]' \
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
  cp "${@: -1}" "$FAKE_LEAN_INPUT"
elif [[ "${1:-}" == "env" && $# -gt 1 ]]; then
  # Any other command runs in the workspace environment, whose Lean is the fake one.
  shift
  LEAN="$FAKE_BIN/fake-lean" exec "$@"
fi
printf '%s\n' "${FAKE_LAKE_OUTPUT:-Build completed successfully.}"
exit "${FAKE_LAKE_STATUS:-0}"
SH
cat >"$FAKE_BIN/fake-lean" <<'SH'
#!/usr/bin/env bash
printf 'lean %s\n' "$*" >>"$FAKE_LAKE_LOG"
cp "${@: -1}" "$FAKE_LEAN_INPUT"
exit "${FAKE_LAKE_STATUS:-0}"
SH
chmod +x "$FAKE_BIN/lake" "$FAKE_BIN/fake-lean"
FAKE_LEAN_INPUT="$TMP_ROOT/lean-input.lean"
export FAKE_BIN FAKE_LAKE_LOG FAKE_LEAN_INPUT

if ! PATH="$FAKE_BIN:$PATH" "$REPO_ROOT/scripts/check_diagnostics.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  cat "$TMP_ROOT/output.log" >&2
  fail "clean compiler diagnostics failed"
fi
grep -qx 'build MathlibExt CSLibExt PhyslibExt Domains WantedExt MathlibExtTest CSLibExtTest PhyslibExtTest DomainsTest' "$FAKE_LAKE_LOG" ||
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
for library in CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest Domains DomainsTest WantedExt; do
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
  PhyslibExt.Sentinel PhyslibExtTest.Sentinel Domains.Sentinel DomainsTest.Sentinel WantedExt.Sentinel; do
  grep -qx "import $module" "$FAKE_LEAN_INPUT" ||
    fail "axiom input omitted $module"
done
if grep -q '^import v1\.' "$FAKE_LEAN_INPUT"; then
  fail "axiom input included archived v1 source"
fi

# A pull request audits only the modules whose .olean is missing, new,
# rewritten or not audited at the restored commit, and only under its policy.
OLEANS="$TMP_ROOT/repo/.lake/build/lib/lean"
for library in CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest Domains DomainsTest WantedExt; do
  mkdir -p "$OLEANS/$library" && : >"$OLEANS/$library/Sentinel.olean"
done
# The restored commit has no WantedExt.Sentinel, which left a stale .olean.
git -C "$TMP_ROOT/repo" init -q && git -C "$TMP_ROOT/repo" add scripts \
  CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest Domains DomainsTest &&
  git -C "$TMP_ROOT/repo" -c user.name=t -c user.email=t@t commit -qm restored
python3 "$TMP_ROOT/repo/scripts/audit_rebuilt_modules.py" record "$TMP_ROOT/restored.json" HEAD
printf 'x' >"$OLEANS/MathlibExt/Sentinel.olean"
rm "$OLEANS/DomainsTest/Sentinel.olean"
if ! env PATH="$FAKE_BIN:$PATH" ATLAS_AUDIT_RESTORED="$TMP_ROOT/restored.json" \
  "$TMP_ROOT/repo/scripts/check_axioms.sh" >"$TMP_ROOT/output.log" 2>&1; then
  cat "$TMP_ROOT/output.log" >&2
  fail "scoped compiled audit failed"
fi
grep -q 'compiled audit: 3 modules rebuilt since the restored build, 3 with their importers, 9 modules in their batches' \
  "$TMP_ROOT/output.log" || fail "scoped compiled audit found the wrong rebuilt modules"
[[ "$(grep -c -x 'import [A-Za-z]*\.Sentinel' "$FAKE_LEAN_INPUT")" == 9 ]] ||
  fail "scoped compiled audit did not run the whole batch"
PYTHONPATH="$TMP_ROOT/repo/scripts" python3 -c '
import audit_rebuilt_modules as scoped
assert scoped.batches_with(list("abcde"), {"d"}, 2) == list("cd")
assert scoped.batches_with(list("abcde"), {"a", "e"}, 2) == list("abe")
assert scoped.batches_with(list("abcde"), set(), 2) == []' || fail "scoped compiled audit chose the wrong batches"
mkdir -p "$TMP_ROOT/graph/MathlibExt" "$TMP_ROOT/graph/WantedExt"
printf 'module\n' >"$TMP_ROOT/graph/MathlibExt/A.lean"
printf 'module\nimport MathlibExt.A\n' >"$TMP_ROOT/graph/MathlibExt/B.lean"
printf 'module\npublic import\n  MathlibExt.B--note\n' >"$TMP_ROOT/graph/WantedExt/C.lean"
printf 'module\nimport MathlibExt.D\n' >"$TMP_ROOT/graph/WantedExt/E.lean"
printf 'module\nimport «WantedExt».C\n' >"$TMP_ROOT/graph/WantedExt/F.lean"
printf 'module\nimport /- a /- nested -/ note -/ WantedExt.F -- why\n' >"$TMP_ROOT/graph/WantedExt/G.lean"
PYTHONPATH="$TMP_ROOT/repo/scripts" python3 -c '
import sys; from pathlib import Path
import audit_rebuilt_modules as scoped
assert scoped.importers(Path(sys.argv[1]), {"MathlibExt.A"}) == {"MathlibExt.A", "MathlibExt.B", "WantedExt.C", "WantedExt.F", "WantedExt.G"}
assert scoped.importers(Path(sys.argv[1]), set()) == set()' "$TMP_ROOT/graph" ||
  fail "scoped compiled audit missed an importer"
: >"$OLEANS/DomainsTest/Sentinel.olean"
git -C "$TMP_ROOT/repo" add WantedExt && git -C "$TMP_ROOT/repo" -c user.name=t -c user.email=t@t commit -qm audited
python3 "$TMP_ROOT/repo/scripts/audit_rebuilt_modules.py" record "$TMP_ROOT/restored.json" HEAD
: >"$FAKE_LAKE_LOG"
if ! env PATH="$FAKE_BIN:$PATH" ATLAS_AUDIT_RESTORED="$TMP_ROOT/restored.json" \
  "$TMP_ROOT/repo/scripts/check_axioms.sh" >"$TMP_ROOT/output.log" 2>&1 || [[ -s "$FAKE_LAKE_LOG" ]]; then
  fail "scoped compiled audit of an unchanged build ran Lean or failed"
fi
for policy in audit_compiled_modules.py check_axioms.lean audit_rebuilt_modules.py; do
  cp "$TMP_ROOT/repo/scripts/$policy" "$TMP_ROOT/$policy"
  printf '\n' >>"$TMP_ROOT/repo/scripts/$policy"
  if python3 "$TMP_ROOT/repo/scripts/audit_rebuilt_modules.py" record "$TMP_ROOT/changed.json" HEAD \
    >/dev/null || [[ -e "$TMP_ROOT/changed.json" ]]; then
    fail "a restored build audited under another $policy was recorded"
  fi
  cp "$TMP_ROOT/$policy" "$TMP_ROOT/repo/scripts/$policy"
done

# Declaration collisions: every tracked module of the audited libraries, and nothing
# else, is imported into one environment; a module without its .olean, or a failing
# `git ls-files`, fails before Lean runs; and the module list is the one the wiki's
# dependency dump imports, extended to the libraries the compiled audit checks.
reset_fixture
cp "$REPO_ROOT/scripts/"{check_declaration_collisions.sh,list_v2_modules.sh} "$TMP_ROOT/repo/scripts/"
for library in CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest Domains DomainsTest WantedExt; do
  mkdir -p "$TMP_ROOT/repo/$library/Nested" "$TMP_ROOT/repo/.lake/build/lib/lean/$library/Nested"
  printf '%s\n' 'def sentinel : Nat := 1' >"$TMP_ROOT/repo/$library/Nested/Sentinel.lean"
  : >"$TMP_ROOT/repo/.lake/build/lib/lean/$library/Nested/Sentinel.olean"
done
git -C "$TMP_ROOT/repo" init -q
git -C "$TMP_ROOT/repo" add CSLibExt CSLibExtTest MathlibExt MathlibExtTest PhyslibExt PhyslibExtTest Domains DomainsTest WantedExt v1
# A non-ASCII path is read literally, not as Git's quoted form.
printf '%s\n' 'def accented : Nat := 1' >"$TMP_ROOT/repo/MathlibExt/Nested/Étale.lean"
: >"$TMP_ROOT/repo/.lake/build/lib/lean/MathlibExt/Nested/Étale.olean"
git -C "$TMP_ROOT/repo" add MathlibExt/Nested/Étale.lean
# The compiled audit imports untracked sources too, so the check refuses to leave one out.
printf '%s\n' 'def untracked : Nat := 1' >"$TMP_ROOT/repo/MathlibExt/Untracked.lean"
: >"$FAKE_LAKE_LOG"
if PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  fail "collision check passed with an untracked audited source"
fi
grep -qF 'FAIL [declaration collisions]: MathlibExt/Untracked.lean is not tracked by Git, but the compiled audit reads it; add it, or remove it.' \
  "$TMP_ROOT/output.log" ||
  { cat "$TMP_ROOT/output.log" >&2; fail "collision check reported an untracked source wrongly"; }
[[ ! -s "$FAKE_LAKE_LOG" ]] || fail "collision check ran Lean without an untracked source"
rm "$TMP_ROOT/repo/MathlibExt/Untracked.lean"
if ! PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  cat "$TMP_ROOT/output.log" >&2
  fail "collision check failed on distinct modules"
fi
grep -Eqx 'env lean --run scripts/check_declaration_collisions\.lean .+' "$FAKE_LAKE_LOG" ||
  fail "collision check did not run its Lean checker"
printf '%s\n' CSLibExt.Nested.Sentinel CSLibExtTest.Nested.Sentinel Domains.Nested.Sentinel \
  DomainsTest.Nested.Sentinel MathlibExt.Nested.Sentinel MathlibExt.Nested.Étale \
  MathlibExtTest.Nested.Sentinel PhyslibExt.Nested.Sentinel PhyslibExtTest.Nested.Sentinel \
  WantedExt.Nested.Sentinel |
  LC_ALL=C sort >"$TMP_ROOT/expected-modules"
LC_ALL=C sort "$FAKE_LEAN_INPUT" | diff -u "$TMP_ROOT/expected-modules" - >&2 ||
  fail "collision check imported the wrong modules"
# Pathspec settings in the caller's environment do not change which sources are listed. An
# index entry under a library name in another case would match only case-insensitively.
blob="$(git -C "$TMP_ROOT/repo" hash-object -w MathlibExt/Nested/Sentinel.lean)"
git -C "$TMP_ROOT/repo" update-index --add --cacheinfo "100644,$blob,mathlibext/Nested/Sentinel.lean"
for setting in GIT_GLOB_PATHSPECS GIT_NOGLOB_PATHSPECS GIT_LITERAL_PATHSPECS GIT_ICASE_PATHSPECS; do
  : >"$FAKE_LAKE_LOG"
  env "$setting=1" PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
    >"$TMP_ROOT/output.log" 2>&1 ||
    { cat "$TMP_ROOT/output.log" >&2; fail "collision check failed with $setting=1"; }
  LC_ALL=C sort "$FAKE_LEAN_INPUT" | diff -u "$TMP_ROOT/expected-modules" - >&2 ||
    fail "collision check listed the wrong modules with $setting=1"
done
git -C "$TMP_ROOT/repo" rm -q --cached mathlibext/Nested/Sentinel.lean
# The module list is split at line feeds only: a path holding U+2028 stays one path, as the
# audit reads it (Lean then rejects its name).
separated="WantedExt/Nested/Line"$'\xe2\x80\xa8'"Separator"
printf '%s\n' 'def separated : Nat := 1' >"$TMP_ROOT/repo/$separated.lean"
: >"$TMP_ROOT/repo/.lake/build/lib/lean/$separated.olean"
git -C "$TMP_ROOT/repo" add "$separated.lean"
: >"$FAKE_LAKE_LOG"
PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1 ||
  { cat "$TMP_ROOT/output.log" >&2; fail "collision check split a module path at U+2028"; }
grep -qxF "${separated//\//.}" "$FAKE_LEAN_INPUT" ||
  fail "collision check did not list a module whose path holds U+2028 as one line"
git -C "$TMP_ROOT/repo" rm -q --cached "$separated.lean"
rm "$TMP_ROOT/repo/$separated.lean" "$TMP_ROOT/repo/.lake/build/lib/lean/$separated.olean"
# A passing check leaves no temporary file behind.
mkdir -p "$TMP_ROOT/collision-tmp-pass"
TMPDIR="$TMP_ROOT/collision-tmp-pass" PATH="$FAKE_BIN:$PATH" \
  "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" >"$TMP_ROOT/output.log" 2>&1 ||
  { cat "$TMP_ROOT/output.log" >&2; fail "collision check failed with its own TMPDIR"; }
# Other tools may write there too; the check's own files all start with `atlas-`.
! compgen -G "$TMP_ROOT/collision-tmp-pass/atlas-*" >/dev/null ||
  fail "a passing collision check left a temporary file behind"
# A tracked source missing from the working tree is not imported by the audit either.
mv "$TMP_ROOT/repo/WantedExt/Nested/Sentinel.lean" "$TMP_ROOT/Sentinel.lean"
: >"$FAKE_LAKE_LOG"
if PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  fail "collision check passed without a tracked source"
fi
grep -qF "FAIL [declaration collisions]: WantedExt/Nested/Sentinel.lean is tracked by Git, but the compiled audit's walk of its libraries does not find it." \
  "$TMP_ROOT/output.log" ||
  { cat "$TMP_ROOT/output.log" >&2; fail "collision check reported a missing source wrongly"; }
[[ ! -s "$FAKE_LAKE_LOG" ]] || fail "collision check ran Lean without a tracked source"
mv "$TMP_ROOT/Sentinel.lean" "$TMP_ROOT/repo/WantedExt/Nested/Sentinel.lean"
# Nor is one under a symlinked directory, which the audit's walk does not enter.
mv "$TMP_ROOT/repo/WantedExt/Nested" "$TMP_ROOT/repo/WantedExt/Linked"
ln -s Linked "$TMP_ROOT/repo/WantedExt/Nested"
: >"$FAKE_LAKE_LOG"
if PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  fail "collision check passed a source under a symlinked directory"
fi
grep -qF "FAIL [declaration collisions]: WantedExt/Nested/Sentinel.lean is tracked by Git, but the compiled audit's walk of its libraries does not find it." \
  "$TMP_ROOT/output.log" ||
  { cat "$TMP_ROOT/output.log" >&2; fail "collision check reported a symlinked directory wrongly"; }
[[ ! -s "$FAKE_LAKE_LOG" ]] || fail "collision check ran Lean with a symlinked directory"
rm "$TMP_ROOT/repo/WantedExt/Nested"
mv "$TMP_ROOT/repo/WantedExt/Linked" "$TMP_ROOT/repo/WantedExt/Nested"
# A path with the flattened module name of a tracked source is a different module, both
# beside that source and in its place.
cp "$TMP_ROOT/repo/WantedExt/Nested/Sentinel.lean" "$TMP_ROOT/repo/WantedExt/Nested.Sentinel.lean"
: >"$FAKE_LAKE_LOG"
if PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  fail "collision check passed a source beside one with its module name"
fi
grep -qF 'FAIL [declaration collisions]: WantedExt/Nested.Sentinel.lean is not tracked by Git' \
  "$TMP_ROOT/output.log" ||
  { cat "$TMP_ROOT/output.log" >&2; fail "collision check reported a same-name source wrongly"; }
[[ ! -s "$FAKE_LAKE_LOG" ]] || fail "collision check ran Lean with a same-name source"
rm "$TMP_ROOT/repo/WantedExt/Nested/Sentinel.lean"
: >"$FAKE_LAKE_LOG"
if PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  fail "collision check passed a renamed source"
fi
grep -qF 'FAIL [declaration collisions]: WantedExt/Nested.Sentinel.lean is not tracked by Git' \
  "$TMP_ROOT/output.log" ||
  { cat "$TMP_ROOT/output.log" >&2; fail "collision check reported a renamed source wrongly"; }
[[ ! -s "$FAKE_LAKE_LOG" ]] || fail "collision check ran Lean with a renamed source"
mv "$TMP_ROOT/repo/WantedExt/Nested.Sentinel.lean" "$TMP_ROOT/repo/WantedExt/Nested/Sentinel.lean"
# When its second temporary file cannot be made, the check leaves the first one behind
# neither.
FAKE_MKTEMP="$TMP_ROOT/fake-mktemp"
mkdir -p "$FAKE_MKTEMP" "$TMP_ROOT/collision-tmp"
printf '#!/usr/bin/env bash\ncase "$*" in *atlas-audited-libraries*) exit 1 ;; esac\nexec %q "$@"\n' \
  "$(command -v mktemp)" >"$FAKE_MKTEMP/mktemp"
chmod +x "$FAKE_MKTEMP/mktemp"
: >"$FAKE_LAKE_LOG"
if TMPDIR="$TMP_ROOT/collision-tmp" PATH="$FAKE_MKTEMP:$FAKE_BIN:$PATH" \
  "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" >"$TMP_ROOT/output.log" 2>&1; then
  fail "collision check passed without its temporary files"
fi
! compgen -G "$TMP_ROOT/collision-tmp/atlas-*" >/dev/null ||
  fail "collision check left a temporary file behind"
[[ ! -s "$FAKE_LAKE_LOG" ]] || fail "collision check ran Lean without its temporary files"
# The audited libraries are read from the audit; a malformed list fails before Lean runs.
cp "$TMP_ROOT/repo/scripts/audit_compiled_modules.py" "$TMP_ROOT/audit_compiled_modules.py"
for roots in '()' "('MathlibExt\\nMathlibExtTest',)" "('MathlibExt', 'MathlibExt')" \
  "('MathlibExt', 'Bad/Name')" "('MathlibExt', 1)"; do
  cp "$TMP_ROOT/audit_compiled_modules.py" "$TMP_ROOT/repo/scripts/"
  printf 'ROOTS = %s\n' "$roots" >>"$TMP_ROOT/repo/scripts/audit_compiled_modules.py"
  : >"$FAKE_LAKE_LOG"
  if PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
    >"$TMP_ROOT/output.log" 2>&1; then
    fail "collision check accepted ROOTS = $roots"
  fi
  grep -q 'could not read the audited libraries' "$TMP_ROOT/output.log" ||
    { cat "$TMP_ROOT/output.log" >&2; fail "collision check reported ROOTS = $roots wrongly"; }
  [[ ! -s "$FAKE_LAKE_LOG" ]] || fail "collision check ran Lean with ROOTS = $roots"
done
# Other valid libraries are imported as given.
cp "$TMP_ROOT/audit_compiled_modules.py" "$TMP_ROOT/repo/scripts/"
printf '%s\n' "ROOTS = ('WantedExt', 'MathlibExt')" >>"$TMP_ROOT/repo/scripts/audit_compiled_modules.py"
: >"$FAKE_LAKE_LOG"
PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1 ||
  { cat "$TMP_ROOT/output.log" >&2; fail "collision check failed on other audited libraries"; }
printf '%s\n' MathlibExt.Nested.Sentinel MathlibExt.Nested.Étale WantedExt.Nested.Sentinel |
  LC_ALL=C sort >"$TMP_ROOT/expected-modules"
LC_ALL=C sort "$FAKE_LEAN_INPUT" | diff -u "$TMP_ROOT/expected-modules" - >&2 ||
  fail "collision check ignored the audited libraries"
cp "$TMP_ROOT/audit_compiled_modules.py" "$TMP_ROOT/repo/scripts/"
if env PATH="$FAKE_BIN:$PATH" FAKE_LAKE_STATUS=1 \
  "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" >"$TMP_ROOT/output.log" 2>&1; then
  fail "collision check passed a failed Lean import"
fi
rm "$TMP_ROOT/repo/.lake/build/lib/lean/Domains/Nested/Sentinel.olean"
: >"$FAKE_LAKE_LOG"
if PATH="$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  fail "collision check passed without a compiled module"
fi
grep -q 'Missing compiled module: Domains/Nested/Sentinel.lean' "$TMP_ROOT/output.log" ||
  fail "collision check reported a missing compiled module wrongly"
[[ ! -s "$FAKE_LAKE_LOG" ]] || fail "collision check ran Lean without every compiled module"
: >"$TMP_ROOT/repo/.lake/build/lib/lean/Domains/Nested/Sentinel.olean"
# A `git ls-files` that fails after listing some modules must not pass a partial list.
FAKE_GIT="$TMP_ROOT/fake-git"
mkdir -p "$FAKE_GIT"
cat >"$FAKE_GIT/git" <<'SH'
#!/usr/bin/env bash
printf 'MathlibExt/Nested/Sentinel.lean\0'
exit 74
SH
chmod +x "$FAKE_GIT/git"
: >"$FAKE_LAKE_LOG"
if PATH="$FAKE_GIT:$FAKE_BIN:$PATH" "$TMP_ROOT/repo/scripts/check_declaration_collisions.sh" \
  >"$TMP_ROOT/output.log" 2>&1; then
  fail "collision check passed a partial module list"
fi
grep -q 'could not list the compiled modules' "$TMP_ROOT/output.log" ||
  fail "collision check reported a failed module listing wrongly"
[[ ! -s "$FAKE_LAKE_LOG" ]] || fail "collision check ran Lean on a partial module list"
# The list fails, and leaves no list behind, on a missing .olean, and on a directory or
# file name with a dot or a line break, which would change the module name read back.
printf '%s\n' stale >"$TMP_ROOT/repo/modules.txt"
rm "$TMP_ROOT/repo/.lake/build/lib/lean/WantedExt/Nested/Sentinel.olean"
if (cd "$TMP_ROOT/repo" && scripts/list_v2_modules.sh modules.txt) >"$TMP_ROOT/output.log" 2>&1; then
  fail "module list passed without a compiled module"
fi
[[ ! -e "$TMP_ROOT/repo/modules.txt" ]] || fail "failed module list left a list behind"
: >"$TMP_ROOT/repo/.lake/build/lib/lean/WantedExt/Nested/Sentinel.olean"
for name in 'Dotted.Name' $'Line\nBreak' $'Carriage\rReturn'; do
  printf '%s\n' 'def odd : Nat := 1' >"$TMP_ROOT/repo/MathlibExt/Nested/$name.lean"
  : >"$TMP_ROOT/repo/.lake/build/lib/lean/MathlibExt/Nested/$name.olean"
  git -C "$TMP_ROOT/repo" add "MathlibExt/Nested/$name.lean"
  if (cd "$TMP_ROOT/repo" && scripts/list_v2_modules.sh modules.txt) >"$TMP_ROOT/output.log" 2>&1; then
    fail "module list accepted the file name ${name@Q}"
  fi
  grep -qF "Module path is not a Lean module name (a directory or file name contains a dot or a line break): MathlibExt/Nested/${name%%[$'\n\r']*}" \
    "$TMP_ROOT/output.log" || { cat "$TMP_ROOT/output.log" >&2; fail "module list reported ${name@Q} wrongly"; }
  [[ ! -e "$TMP_ROOT/repo/modules.txt" ]] || fail "failed module list left a list behind"
  git -C "$TMP_ROOT/repo" rm -q --cached "MathlibExt/Nested/$name.lean"
done
(cd "$TMP_ROOT/repo" && scripts/list_v2_modules.sh modules.txt) >"$TMP_ROOT/output.log" 2>&1 ||
  { cat "$TMP_ROOT/output.log" >&2; fail "module list failed on valid modules"; }
grep -qx 'MathlibExt.Nested.Étale' "$TMP_ROOT/repo/modules.txt" ||
  fail "module list dropped a non-ASCII module"
# Without libraries, the list is the wiki's: the five v2 libraries, without the tests.
printf '%s\n' CSLibExt.Nested.Sentinel Domains.Nested.Sentinel MathlibExt.Nested.Sentinel \
  MathlibExt.Nested.Étale PhyslibExt.Nested.Sentinel WantedExt.Nested.Sentinel |
  LC_ALL=C sort >"$TMP_ROOT/expected-modules"
LC_ALL=C sort "$TMP_ROOT/repo/modules.txt" | diff -u "$TMP_ROOT/expected-modules" - >&2 ||
  fail "module list does not default to the five v2 libraries"
(cd "$TMP_ROOT/repo" && scripts/list_v2_modules.sh modules.txt DomainsTest WantedExt) \
  >"$TMP_ROOT/output.log" 2>&1 ||
  { cat "$TMP_ROOT/output.log" >&2; fail "module list failed on named libraries"; }
printf '%s\n' DomainsTest.Nested.Sentinel WantedExt.Nested.Sentinel |
  diff -u - "$TMP_ROOT/repo/modules.txt" >&2 || fail "module list ignored the named libraries"
for library in 'MathlibExt/Nested' '*' '' '-x'; do
  if (cd "$TMP_ROOT/repo" && scripts/list_v2_modules.sh modules.txt "$library") \
    >"$TMP_ROOT/output.log" 2>&1; then
    fail "module list accepted the library name ${library@Q}"
  fi
  grep -qF "Not a library name: " "$TMP_ROOT/output.log" ||
    { cat "$TMP_ROOT/output.log" >&2; fail "module list reported ${library@Q} wrongly"; }
  [[ ! -e "$TMP_ROOT/repo/modules.txt" ]] || fail "failed module list left a list behind"
done
# A named library that is not a directory of its own fails instead of listing nothing.
ln -s MathlibExt "$TMP_ROOT/repo/Linked"
for library in NotALibrary Linked; do
  if (cd "$TMP_ROOT/repo" && scripts/list_v2_modules.sh modules.txt MathlibExt "$library") \
    >"$TMP_ROOT/output.log" 2>&1; then
    fail "module list accepted the missing library $library"
  fi
  grep -qx "No library directory: $library" "$TMP_ROOT/output.log" ||
    { cat "$TMP_ROOT/output.log" >&2; fail "module list reported $library wrongly"; }
  [[ ! -e "$TMP_ROOT/repo/modules.txt" ]] || fail "failed module list left a list behind"
done
rm "$TMP_ROOT/repo/Linked"
grep -qx '          scripts/list_v2_modules.sh v2-modules.txt' \
  "$REPO_ROOT/.github/workflows/blueprint-pages.yml" ||
  fail "wiki dump does not use the shared module list"
grep -qx 'scripts/list_v2_modules.sh "$modules" "${libraries\[@\]}" || {' \
  "$REPO_ROOT/scripts/check_declaration_collisions.sh" ||
  fail "collision check does not use the shared module list"
grep -qx '  run_check "declaration collisions" scripts/check_declaration_collisions.sh' \
  "$REPO_ROOT/scripts/check.sh" || fail "build checks do not run the collision check"

# Build checks run diagnostics, then collisions, then the compiled audit, which takes
# longer than the collision check. By default every check runs and every failure is
# reported; with ATLAS_CHECK_FAIL_FAST=1, which CI sets for merge groups only, check.sh
# stops at the first failing check.
ORDER="$TMP_ROOT/build-order"
rm -rf "$ORDER" && mkdir -p "$ORDER/scripts"
cp "$REPO_ROOT/scripts/check.sh" "$ORDER/scripts/"
for check in check_diagnostics check_declaration_collisions check_axioms; do
  printf '#!/usr/bin/env bash\necho %s >>"$CHECK_LOG"\nexit "${FAIL_%s:-0}"\n' "$check" "$check" \
    >"$ORDER/scripts/$check.sh"
  chmod +x "$ORDER/scripts/$check.sh"
done
run_build_checks() {
  : >"$TMP_ROOT/check-calls"
  env -u ATLAS_CHECK_FAIL_FAST -u FAIL_check_diagnostics -u FAIL_check_declaration_collisions \
    -u FAIL_check_axioms CHECK_LOG="$TMP_ROOT/check-calls" "$@" "$ORDER/scripts/check.sh" build \
    >"$TMP_ROOT/output.log" 2>&1
}
expect_calls() {
  printf '%s\n' "$@" | diff -u - "$TMP_ROOT/check-calls" >&2 ||
    fail "build checks ran the wrong checks or in the wrong order"
}
run_build_checks || { cat "$TMP_ROOT/output.log" >&2; fail "build checks failed when every check passed"; }
expect_calls check_diagnostics check_declaration_collisions check_axioms
for failing in check_diagnostics check_declaration_collisions check_axioms; do
  for mode in "" ATLAS_CHECK_FAIL_FAST=0; do
    if run_build_checks ${mode:+"$mode"} "FAIL_$failing=1"; then
      fail "build checks passed when $failing failed"
    fi
    expect_calls check_diagnostics check_declaration_collisions check_axioms
  done
done
if run_build_checks ATLAS_CHECK_FAIL_FAST=1 FAIL_check_diagnostics=1; then
  fail "fail-fast build checks passed when the diagnostics failed"
fi
expect_calls check_diagnostics
if run_build_checks ATLAS_CHECK_FAIL_FAST=1 FAIL_check_declaration_collisions=1; then
  fail "fail-fast build checks passed when the collision check failed"
fi
expect_calls check_diagnostics check_declaration_collisions
grep -q 'Stopped at the first failing check, declaration collisions' "$TMP_ROOT/output.log" ||
  fail "fail-fast build checks did not name the check they stopped at"
run_build_checks ATLAS_CHECK_FAIL_FAST=1 ||
  { cat "$TMP_ROOT/output.log" >&2; fail "fail-fast build checks failed when every check passed"; }
expect_calls check_diagnostics check_declaration_collisions check_axioms
for value in true ""; do
  fail_fast_status=0
  run_build_checks "ATLAS_CHECK_FAIL_FAST=$value" || fail_fast_status=$?
  [[ "$fail_fast_status" -eq 2 && ! -s "$TMP_ROOT/check-calls" ]] ||
    fail "build checks accepted ATLAS_CHECK_FAIL_FAST='$value'"
done
grep -A2 -x '      - name: Build extension libraries' "$REPO_ROOT/.github/workflows/ci.yml" |
  grep -qxF "          ATLAS_CHECK_FAIL_FAST: \${{ github.event_name == 'merge_group' && '1' || '0' }}" ||
  fail "CI does not stop a merge group's build checks at the first failure"

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

PYTHONPATH="$REPO_ROOT/scripts${PYTHONPATH:+:$PYTHONPATH}" \
  python3 -m unittest discover \
    -s "$REPO_ROOT/scripts/import_optimizer" -p 'test_*.py' -v
python3 -m unittest discover -s "$REPO_ROOT/scripts" -p test_quality_eval.py -v
python3 -m unittest discover -s "$REPO_ROOT/scripts" -p test_audit_parallel.py -v
python3 -m unittest discover -s "$REPO_ROOT/scripts" -p test_formal_math_sync.py -v
python3 -m unittest discover -s "$REPO_ROOT/scripts" -p test_public_references.py -v
python3 -m unittest discover -s "$REPO_ROOT/scripts" -p test_public_reference_workflow.py -v
python3 -m unittest discover -s "$REPO_ROOT/scripts" -p test_merge_queue_checks.py -v
python3 -m unittest discover -s "$REPO_ROOT/scripts" -p test_ci_build_trims.py -v
python3 -m unittest discover -s "$REPO_ROOT/scripts" -p test_bump_cache_workflow.py -v
python3 -m unittest discover -s "$REPO_ROOT/scripts" -p test_next_task.py -v
python3 "$REPO_ROOT/scripts/bump/test_pinned_bump.py"
python3 "$REPO_ROOT/scripts/bump/test_bump_branch.py"
python3 -m unittest discover -s "$REPO_ROOT/scripts/queue" -p 'test_*.py' -v

echo "ok [scripts]: repository policy regression tests passed."
