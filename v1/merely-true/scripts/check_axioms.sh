#!/usr/bin/env bash
# Check that every declaration of the merely-true variant is gap-free: no unsafe
# declarations, no implemented_by, and no axioms beyond propext, Quot.sound and
# Classical.choice. Books are independent developments (some top-level names
# clash across books), so each book is loaded and checked separately.
# Usage: scripts/check_axioms.sh [Book ...]   (default: all books; run after `lake build`)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [ "$#" -gt 0 ]; then books=("$@"); else
  mapfile -t books < <(find Atlas -mindepth 1 -maxdepth 1 -type d -printf '%f\n' | LC_ALL=C sort)
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/merely-true-axioms.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

check_book() {
  local book="$1" file="$WORK/Check_$1.lean"
  find "Atlas/$book" -type f -name '*.lean' -print | LC_ALL=C sort |
    sed 's|\.lean$||; s|/|.|g; s|^|import |' >"$file"
  cat >>"$file" <<'LEAN'
import Lean.Compiler.ImplementedByAttr
import Lean.Util.CollectAxioms

private def trustedAxioms : Array Lean.Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

run_cmd do
  let env ← Lean.getEnv
  let mut names : Array Lean.Name := #[]
  for i in [0:env.header.moduleNames.size] do
    unless (`Atlas).isPrefixOf env.header.moduleNames[i]! do continue
    for name in env.header.moduleData[i]!.constNames do
      let some info := env.find? name | continue
      names := names.push name
      if info.isUnsafe then
        Lean.logError m!"{name} is an unsafe declaration"
      if (Lean.Compiler.getImplementedBy? env name).isSome then
        Lean.logError m!"{name} uses implemented_by"
  -- One shared traversal gives the union of all axioms reachable from the book.
  let mut st : Lean.CollectAxioms.State := {}
  for name in names do
    st := (((Lean.CollectAxioms.collect name).run env).run st).2
  unless (st.axioms.filter (!trustedAxioms.contains ·)).isEmpty do
    -- Something non-standard is reachable: name the offending declarations.
    for name in names do
      let forbidden := (← Lean.collectAxioms name).filter (!trustedAxioms.contains ·)
      unless forbidden.isEmpty do
        Lean.logError m!"{name} depends on forbidden axioms: {forbidden}"
  Lean.logInfo m!"checked {names.size} declarations; axioms reached: {st.axioms.toList}"
LEAN
  if lake env lean "$file" >"$file.log" 2>&1; then
    echo "ok    $book: $(grep -o 'checked [0-9]* declarations.*' "$file.log")"
  else
    echo "FAIL  $book"; grep -E 'error' "$file.log" | head -20; return 1
  fi
}

status=0
for book in "${books[@]}"; do check_book "$book" || status=1; done
exit "$status"
