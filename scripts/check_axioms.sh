#!/usr/bin/env bash
# Inspect parsed sources and compiled declarations for repository-policy violations.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODULES=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --root) [[ $# -ge 2 ]] || exit 2; REPO_ROOT="$2"; shift 2 ;;
    --modules) [[ $# -ge 2 ]] || exit 2; MODULES="$2"; shift 2 ;;
    *) echo "usage: check_axioms.sh [--root DIR] [--modules FILE]" >&2; exit 2 ;;
  esac
done
if [[ -n "$MODULES" && "$MODULES" != /* ]]; then
  MODULES="$PWD/$MODULES"
fi
cd "$REPO_ROOT"

CHECK_FILE="$(mktemp "${TMPDIR:-/tmp}/atlas-axioms.XXXXXX.lean")"
trap 'rm -f "$CHECK_FILE"' EXIT

python3 - "$MODULES" >>"$CHECK_FILE" <<'PY'
from pathlib import Path
import sys, tomllib
config = tomllib.loads(Path("lakefile.toml").read_text())
if sys.argv[1]:
    modules = [m for m in Path(sys.argv[1]).read_text().splitlines() if m]
else:
    modules = []
    for library in config["lean_lib"]:
        root = library["name"]
        paths = list(Path(root).rglob("*.lean"))
        if Path(root + ".lean").is_file():
            paths.append(Path(root + ".lean"))
        for path in sorted(paths):
            modules.append(".".join("«" + p + "»" for p in path.with_suffix("").parts))
for module in modules:
    print("import " + module)
PY

cat >>"$CHECK_FILE" <<'LEAN'
import Batteries.Util.ProofWanted
import Lean.Compiler.ImplementedByAttr
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean.Elab.Command

private def trustedAxioms : Array Lean.Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

private def libraryRoots : Array Lean.Name :=
  #[`CSLibExt, `CSLibExtTest, `MathlibExt, `MathlibExtTest, `WantedExt]

private def libraryOf? (name : Lean.Name) : Option Lean.Name :=
  libraryRoots.find? (·.isPrefixOf name)

private def mayImport (source target : Lean.Name) : Bool :=
  (source == `CSLibExt && target == `MathlibExt) ||
    (source == `CSLibExtTest && (target == `CSLibExt || target == `MathlibExt)) ||
    (source == `MathlibExtTest && target == `MathlibExt) ||
    (source == `WantedExt && (target == `CSLibExt || target == `MathlibExt))

private def containsWantedWrapper (type : Lean.Expr) : Bool :=
  (type.find? fun
    | .const name _ =>
      name == ``ProofWanted || name == ``DefWanted || name == ``DerivedWanted
    | _ => false).isSome

run_cmd do
  let env ← Lean.getEnv
  let mut failed := false

  for i in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    let some library := libraryOf? moduleName | continue
    let moduleData := env.header.moduleData[i]!

    for imported in moduleData.imports do
      let some importedLibrary := libraryOf? imported.module | continue
      if importedLibrary != library && !mayImport library importedLibrary then
        Lean.logError m!"{moduleName} must not import {imported.module}"
        failed := true

    let mut hasWantedDeclaration := false
    for name in moduleData.constNames do
      let some info := env.find? name | continue
      if info.isUnsafe then
        Lean.logError m!"{name} is an unsafe declaration"
        failed := true
      if (Lean.Compiler.getImplementedBy? env name).isSome then
        Lean.logError m!"{name} uses implemented_by"
        failed := true
      if containsWantedWrapper info.type then
        hasWantedDeclaration := true

      let axioms ← Lean.collectAxioms name
      let forbidden :=
        (axioms.filter fun ax => !trustedAxioms.contains ax).qsort Lean.Name.quickLt
      unless forbidden.isEmpty do
        Lean.logError m!"{name} depends on forbidden axioms: {forbidden}"
        failed := true

    if hasWantedDeclaration then
      if library != `WantedExt then
        Lean.logError m!"{moduleName} contains a wanted declaration outside WantedExt"
        failed := true
      unless moduleData.imports.any (·.module == `Batteries.Util.ProofWanted) do
        Lean.logError m!"{moduleName} must directly import Batteries.Util.ProofWanted"
        failed := true

  if failed then
    throwError
      "audited libraries violate the axiom, safety, wanted-declaration, or import policy"
LEAN

# Configuration is input data. The actual trust/layering policy is defined
# once above; refuse to silently omit a newly declared, unregistered root.
python3 >>"$CHECK_FILE" <<'PY'
from pathlib import Path
import tomllib
roots = [x["name"] for x in tomllib.loads(Path("lakefile.toml").read_text())["lean_lib"]]
names = ", ".join(chr(96) + "«" + x + "»" for x in roots)
print("run_cmd do")
print("  let configured : Array Lean.Name := #[" + names + "]")
print("  unless configured.all libraryRoots.contains do")
print('    throwError "declared library is not covered by the canonical trust policy"')
PY

lake env lean "$CHECK_FILE"
echo "ok [environment]: compiled libraries satisfy trust and dependency policies."
