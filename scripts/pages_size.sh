#!/usr/bin/env bash
# Usage: scripts/pages_size.sh SITE LIMIT
#
# Measures SITE as actions/upload-pages-artifact packs it, with the same tar options, and fails when the archive
# has more than LIMIT bytes. GitHub Pages publishes sites of up to 1 GB; the archive is larger than the site's files,
# which it carries with their headers and padding. Writes both measures to the job summary when there is one.
set -euo pipefail
site="$1"
limit="$2"
files="$(find "$site" -type f | wc -l)"
bytes="$(find "$site" -type f -printf '%s\n' | awk '{ total += $1 } END { print total + 0 }')"
archive="$(tar --dereference --hard-dereference --directory "$site" -cf - --exclude=.git --exclude=.github \
  --exclude='.[^/]*' . | wc -c)"
receipt="$site: $files files, $bytes bytes; Pages archive $archive bytes; limit $limit bytes"
echo "$receipt"
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  echo "- $receipt" >> "$GITHUB_STEP_SUMMARY"
fi
if (( archive > limit )); then
  echo "::error::$site would make a Pages archive of $archive bytes, over the limit of $limit"
  exit 1
fi
