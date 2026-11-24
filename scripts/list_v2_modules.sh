#!/usr/bin/env bash
# Write the module name of every tracked source file of LIBRARY... to OUTPUT, one
# per line, after checking that each has been compiled. The libraries default to
# MathlibExt, CSLibExt, PhyslibExt, Domains and WantedExt. Run it from the
# repository root.
#
#   scripts/list_v2_modules.sh OUTPUT [LIBRARY...]
#
# The blueprint's dependency dump imports the default list; the declaration-
# collision check imports the list of every library the compiled audit checks.
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: scripts/list_v2_modules.sh OUTPUT [LIBRARY...]" >&2
  exit 2
fi
output="$1"
shift

# A failed run leaves no list behind, neither a partial one nor an older one.
rm -f "$output"
libraries=("$@")
if [[ ${#libraries[@]} -eq 0 ]]; then
  libraries=(MathlibExt CSLibExt PhyslibExt Domains WantedExt)
else
  for library in "${libraries[@]}"; do
    # A library is one top-level directory, named like a Lean identifier. A missing
    # one would otherwise drop out of the list unnoticed.
    if [[ ! "$library" =~ ^[A-Za-z][A-Za-z0-9_]*$ ]]; then
      printf 'Not a library name: %q\n' "$library" >&2
      exit 2
    fi
    if [[ ! -d "$library" || -L "$library" ]]; then
      echo "No library directory: $library" >&2
      exit 2
    fi
  done
fi
pathspecs=()
for library in "${libraries[@]}"; do
  pathspecs+=("$library/*.lean")
done
olean_root=.lake/build/lib/lean
[ -d "$olean_root" ] || olean_root=.lake/build/lib
sources="$(mktemp "${TMPDIR:-/tmp}/atlas-v2-sources.XXXXXX")"
trap 'rm -f "$sources" "${modules:-}"' EXIT
modules="$(mktemp "$output.XXXXXX")"

# Git's output goes to a file, not a pipe or a process substitution, so that a
# failing `git ls-files` stops this script instead of leaving a partial list.
# -z keeps non-ASCII paths literal instead of quoting them. The pathspecs are
# wildcards whose `*` also matches `/`; Git reads them otherwise under pathspec
# settings that a caller's environment can hold.
env -u GIT_GLOB_PATHSPECS -u GIT_NOGLOB_PATHSPECS -u GIT_LITERAL_PATHSPECS \
  -u GIT_ICASE_PATHSPECS git ls-files -z -- "${pathspecs[@]}" > "$sources"

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
  echo "No tracked Lean source in the selected libraries: ${libraries[*]}" >&2
  exit 1
}
chmod 644 "$modules"
mv "$modules" "$output"
