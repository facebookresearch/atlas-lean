# Formal-Math sync manifest

`formal-math-sync.json` records which Lean files under `MathlibExt`, `MathlibExtTest`, `CSLibExt`,
`CSLibExtTest` and `WantedExt` come from
[`fairinternal/formal-math`](https://github.com/fairinternal/formal-math), and how each relates to
it. Formal-Math is an upstream source snapshot, not a Lake dependency: files arrive through
reviewed ATLAS pull requests, and Formal-Math never depends on ATLAS.

## Schema (version 1)

Top level: `schema_version`, `upstream` (`repository`, always `fairinternal/formal-math`, and the
full `commit`), `lean_toolchain` (the ATLAS
toolchain when the sync ran; a later Lean bump does not invalidate the recorded provenance, and the
next sync updates it), `roots`, and `rows`, sorted by path, one per line. Files that never came from Formal-Math (ATLAS-only work
and third-party FLT content, which keeps its own header) have no row. Totals are computed by the
sync report, not stored, so concurrent pull requests touching different rows do not conflict.

Each row has `path` and `disposition`. `published_sha256` is the SHA-256 of the ATLAS file's bytes;
`upstream_sha256` is the SHA-256 of an upstream file's body: the text after Formal-Math's own leading
header, without leading blank lines. Formal-Math's own header is a block whose copyright holders
and `Author:`/`Authors:` names are all Formal-Math's own (`FORMAL_MATH_HOLDERS` and
`FORMAL_MATH_AUTHORS` in `scripts/check_formal_math_sync.py`: Meta, its employees, and the agents and
models formal-math is written with); a block without a copyright line must also carry no license
text, and a copyright line naming no holder does not count. `Author:`, `Authors:` and `Author(s):`
lines are read, and a parenthetical that is not all-lowercase description counts as more names. ATLAS replaces that header with the Meta header. Any other copyright or
license block is third-party and part of the body, so ATLAS keeps it byte for byte or records a
divergence.

| Disposition | Meaning | Fields |
| --- | --- | --- |
| `identical` | Meta header, then the body of the upstream file at `upstream.commit`. With `"header": "upstream"`, the upstream file byte for byte, keeping its own copyright and license header (then `upstream_sha256` hashes the whole file). | `published_sha256`, `upstream_sha256`, optional `header` |
| `attributed` | As `identical`, with an attribution notice (one block comment naming provenance or licensing, for example Apache 2.0 Section 4) between the Meta header and the body. | `published_sha256`, `upstream_sha256`, `notice` |
| `behind` | Header-only copy of an older upstream version of the same path; the next sync brings it current. | `published_sha256`, `upstream_commit` (the commit that introduced that version), `upstream_sha256` (its body), optional `notice` or `header` |
| `diverged` | Reviewed ATLAS-side difference from upstream, including a file deleted upstream that ATLAS still publishes. | `published_sha256` (the reviewed bytes), `rationale`, `backport` (`pending`, `not-needed`, or the Formal-Math backport PR URL); informational `upstream_sha256`, `upstream_commit` |
| `retired` | A synced or diverged file ATLAS removed on purpose; the file must stay absent. | the row's last `published_sha256`, `upstream_sha256` and `upstream_commit`, and `line_fingerprint` (sorted 12-hex hashes of the file's distinct lines of 8+ characters) |

## What preflight enforces

`scripts/check.sh preflight` runs `scripts/check_formal_math_sync.py`, which is offline, uses only
the Python standard library, and fails on:

- a malformed manifest: schema, upstream pin, roots, or paths that are not unique, sorted, relative
  and under the roots (absolute, escaping and symlinked paths are rejected);
- an `identical`, `attributed` or `behind` row whose file is missing or whose SHA-256 differs from
  `published_sha256`, or whose header is not the recorded header-only transformation of
  `upstream_sha256`;
- a `diverged` row whose file is missing or differs from `published_sha256` (refresh the row and
  its rationale), or that lacks a non-empty `rationale` and `backport`;
- a `retired` row whose file exists;
- compared with the base manifest: a row that disappears or changes path (rows are never dropped;
  a deleted file keeps its row as `retired`), and, while the upstream pin is unchanged, any change
  to a synced row or a new one. With the pin unchanged a row may only become `retired`, become
  `diverged` (keeping its `upstream_sha256` and `upstream_commit`), or, if diverged, take a new `published_sha256` with a
  new rationale or a rationale/backport update; its `upstream_sha256` and `upstream_commit` stay.
  A tracked (synced or diverged) file that git sees as renamed (50% similar) or copied (90%
  similar, searched from every base file) to a path without a row fails until the new path gets
  one (`--record-divergence NEW`, then `--retire OLD` if it was deleted): a tracked file stays
  tracked when it moves or is copied.
- a file without a row whose bytes equal a synced, diverged or retired row's `published_sha256` (an
  exact copy), or that contains 90% of a retired row's `line_fingerprint` lines (a near copy of a
  file retired earlier); both are checked without a base commit. Only a sync moves the pin and says
  what upstream contains. CI cannot read the private upstream, so a pin change is authorized
  rather than verified: a pull request that moves the pin needs the `formal-math-sync` label, which
  only maintainers (triage or write access) can add, and is reviewed through its sync report. After
  adding the label, push a commit or close and reopen the pull request; adding a label does not
  start CI, and re-running a job reuses the old event. Pushes and merge groups are maintainer-only
  and may move the pin; a local run allows it with a warning. In CI the base is the push's `before` commit, the merge
  group's base, or for a pull request the merge ref's first parent, fetched if the checkout is
  shallow; if it cannot be read the check fails. Locally it is
  the merge-base with `origin/main`, and the comparison is skipped with a warning when neither can
  be read. `--base REV` names it explicitly. The base manifest is looked up at every path the
manifest has had (`MANIFEST_PATHS`); a base without one is accepted only before the cutover, that is
when it also lacks `scripts/check_formal_math_sync.py`.

Files without a row are ATLAS-only and ignored; new upstream files enter at sync time. So the set
of upstream-derived paths cannot change silently (every row's bytes are checked) or shrink silently
(the base comparison), and a pull request fails only if it touches one of those files. The failure
prints the command that records the change:

```bash
python3 scripts/check_formal_math_sync.py --record-divergence PATH... \
    --rationale 'why ATLAS differs' --backport pending   # or not-needed, or the backport PR URL
python3 scripts/check_formal_math_sync.py --retire PATH...   # for a deleted synced or diverged file
```

Neither needs a Formal-Math checkout. Prefer landing a fix in Formal-Math first and syncing; record
a divergence when ATLAS needs the change before that.

## Refreshing

```bash
python3 scripts/sync_formal_math.py --formal-math <formal-math checkout> --commit <sha> \
    [--rationales divergences.json] [--report sync-report.md]
```

The script reads Formal-Math only through `git` in the given local repository: it never fetches
(lazy partial-clone fetches and `git replace` refs are disabled) and refuses shallow clones. It
regenerates the manifest and prints a report with totals and the added, removed, changed and
diverged rows. It writes neither the manifest nor the report when a file newly diverges without a
rationale; pass those as `{"<path>": {"rationale": "...", "backport": "..."}}` in `--rationales`.
A row already diverged keeps its rationale only while its published and upstream hashes are
unchanged. Rows never disappear: a file that left ATLAS keeps its row as `retired`, and the script
stops if a file with a row no longer looks upstream-derived. A periodic sync picks up
upstream changes and new upstream files.
