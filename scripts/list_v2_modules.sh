#!/usr/bin/env bash
# Write the module name of every tracked source file of MathlibExt, CSLibExt,
# PhyslibExt, Domains and WantedExt to OUTPUT, one per line, after checking that
# each has been compiled. Run it from the repository root.
#
#   scripts/list_v2_modules.sh OUTPUT
#
# The declaration-collision check and the blueprint's dependency dump both import
# exactly this list.
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: scripts/list_v2_modules.sh OUTPUT" >&2
  exit 2
fi
output="$1"

# A failed run leaves no list behind, neither a partial one nor an older one.
rm -f "$output"
olean_root=.lake/build/lib/lean
[ -d "$olean_root" ] || olean_root=.lake/build/lib
sources="$(mktemp "${TMPDIR:-/tmp}/atlas-v2-sources.XXXXXX")"
trap 'rm -f "$sources" "${modules:-}"' EXIT
modules="$(mktemp "$output.XXXXXX")"

# Git's output goes to a file, not a pipe or a process substitution, so that a
# failing `git ls-files` stops this script instead of leaving a partial list.
# -z keeps non-ASCII paths literal instead of quoting them.
git ls-files -z -- 'MathlibExt/*.lean' 'CSLibExt/*.lean' 'PhyslibExt/*.lean' 'Domains/*.lean' 'WantedExt/*.lean' \
  > "$sources"

while IFS= read -r -d '' source; do
  module="${source%.lean}"
  # Lake turns each directory and file name into one component of the module name.
  # A dot or a line break inside one would change the name read back from this list.
  case "$module" in
    *.* | *$'\n'* | *$'\r'*)
      echo "Module path is not a Lean module name (a directory or file name contains a dot or a line break): $source" >&2
      exit 1
      ;;
  esac
  test -f "$olean_root/$module.olean" || {
    echo "Missing compiled module: $source" >&2
    exit 1
  }
  printf '%s\n' "${module//\//.}" >> "$modules"
done < "$sources"
test -s "$modules" || {
  echo "No v2 module is tracked" >&2
  exit 1
}
chmod 644 "$modules"
mv "$modules" "$output"
