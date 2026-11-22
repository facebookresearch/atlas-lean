#!/usr/bin/env bash
# In GitHub Actions, check that the workspace is exactly the commit GitHub
# reports results for (GITHUB_SHA): HEAD is that commit, the checkout is not
# sparse, and no file differs from it or has been added (files that .gitignore
# lists, such as build outputs, are allowed). A step that checked out or edited
# another tree before the required checks would otherwise let them pass for a
# tree they did not test. Outside GitHub Actions this does nothing.
set -euo pipefail
[[ "${GITHUB_ACTIONS:-}" == true ]] || exit 0
cd "$(dirname "${BASH_SOURCE[0]}")/.."
fail() {
  echo "checkout check: $*" >&2
  exit 1
}
[[ -n "${GITHUB_SHA:-}" ]] || fail "GITHUB_SHA is not set"
head="$(git rev-parse --verify HEAD)" || fail "cannot read HEAD"
[[ "$head" == "$GITHUB_SHA" ]] ||
  fail "HEAD is $head, but GitHub reports these checks for $GITHUB_SHA"
[[ "$(git config --type=bool --default=false core.sparseCheckout)" == false ]] ||
  fail "the checkout is sparse"
changes="$(git status --porcelain --untracked-files=all)" || fail "cannot read the workspace"
[[ -z "$changes" ]] || fail "the workspace differs from $GITHUB_SHA:"$'\n'"$changes"
