#!/usr/bin/env bash

# Install CI's build of ATLAS as .lake/build, so that `lake build` compiles only
# what changed since that build instead of every module, which takes hours:
#
#   lake exe cache get     # Mathlib
#   scripts/get_build.sh   # ATLAS
#   lake build             # what is left
#
# Each merge-group CI run uploads its build as the artifact lake-build-<sha>
# (ci.yml), kept for one day. This installs the one of the nearest first-parent
# ancestor of HEAD built with the same toolchain and packages. Needs a `gh`
# login, unzip and zstd. A miss or a failed download leaves .lake/build as it
# was, and `lake build` then compiles from source.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"
repo=facebookresearch/atlas-lean

for tool in gh unzip zstd; do
  command -v "$tool" > /dev/null || { echo "get_build.sh needs $tool" >&2; exit 1; }
done
gh auth status > /dev/null 2>&1 || { echo "get_build.sh needs a gh login: run gh auth login" >&2; exit 1; }

id=""
for sha in $(git rev-list --first-parent --max-count=100 HEAD); do
  # A build made with another toolchain or other packages is of no use here.
  git diff --quiet "$sha" HEAD -- lean-toolchain lake-manifest.json || break
  # Take only the build of a successful merge-group run of ci.yml for this
  # commit, as build-cache.yml does: a pull request's run can upload an
  # artifact under any name.
  run="$(gh api "repos/$repo/actions/workflows/ci.yml/runs?event=merge_group&head_sha=$sha&status=success" \
    --jq '.workflow_runs[0].id // empty')" || run=""
  if [[ -n "$run" ]]; then
    id="$(gh api "repos/$repo/actions/runs/$run/artifacts?name=lake-build-$sha" \
      --jq '[.artifacts[] | select(.expired | not)][0].id // empty')" || id=""
  fi
  if [[ -n "$id" ]]; then break; fi
done

if [[ -z "$id" ]]; then
  echo "No CI build of a recent ancestor of HEAD (they are kept for a day)."
  echo "Update your branch from main and run this again, or lake build compiles from source."
  exit 0
fi

mkdir -p .lake
tmp="$(mktemp -d .lake/get-build.XXXXXX)"
trap 'rm -rf "$tmp"' EXIT
echo "Downloading CI's build of $sha (about 2 GB)..."
if gh api "repos/$repo/actions/artifacts/$id/zip" > "$tmp/build.zip" &&
  unzip -p "$tmp/build.zip" lake-build.tar.zst | zstd -dc | tar -x -C "$tmp" &&
  [[ -d "$tmp/build" ]]; then
  if [[ -d .lake/build ]]; then mv .lake/build "$tmp/old"; fi
  mv "$tmp/build" .lake/build
  echo "Installed CI's build of $sha in .lake/build; now run lake build."
else
  echo "Could not download or unpack the build; .lake/build is unchanged." >&2
fi
