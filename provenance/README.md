# Formal-Math sync manifest

`formal-math-sync.json` records which Lean files under `MathlibExt`, `MathlibExtTest`, `CSLibExt`,
`CSLibExtTest` and `WantedExt` come from
[`fairinternal/formal-math`](https://github.com/fairinternal/formal-math), and how each relates to
it. Formal-Math is an upstream source snapshot, not a Lake dependency: files arrive through
reviewed ATLAS pull requests, and Formal-Math never depends on ATLAS.

## Schema (version 1)

Top level: `schema_version`, `upstream` (`repository`, full `commit`), `lean_toolchain`, `roots`,
and `rows`, sorted by path, one per line. Files that never came from Formal-Math (ATLAS-only work
and third-party FLT content, which keeps its own header) have no row. Totals are computed by the
sync report, not stored, so concurrent pull requests touching different rows do not conflict.

Each row has `path` and `disposition`. `published_sha256` is the SHA-256 of the ATLAS file's bytes;
`upstream_sha256` is the SHA-256 of an upstream file's body: the text after its leading license or
authorship block comment, without leading blank lines.

| Disposition | Meaning | Fields |
| --- | --- | --- |
| `identical` | Meta header, then the body of the upstream file at `upstream.commit`. With `"header": "upstream"`, the upstream file byte for byte, keeping its third-party copyright and license header. | `published_sha256`, `upstream_sha256`, optional `header` |
| `attributed` | As `identical`, with an attribution notice (one block comment naming provenance or licensing, for example Apache 2.0 Section 4) between the Meta header and the body. | `published_sha256`, `upstream_sha256`, `notice` |
| `behind` | Header-only copy of an older upstream version of the same path; the next sync brings it current. | `published_sha256`, `upstream_commit` (the commit that introduced that version), `upstream_sha256` (its body), optional `notice` or `header` |
| `diverged` | Reviewed ATLAS-side difference from upstream, including a file deleted upstream that ATLAS still publishes. | `rationale`, `backport` (`pending`, `not-needed`, or the Formal-Math backport PR URL); informational `published_sha256`, `upstream_sha256`, `upstream_commit` |
| `retired` | A synced file ATLAS removed on purpose. | none |

## What preflight enforces

`scripts/check.sh preflight` runs `scripts/check_formal_math_sync.py`, which is offline, uses only
the Python standard library, and fails on:

- a malformed manifest: schema, upstream pin, roots, or paths that are not unique, sorted, relative
  and under the roots (absolute, escaping and symlinked paths are rejected);
- an `identical`, `attributed` or `behind` row whose file is missing or whose SHA-256 differs from
  `published_sha256`, or whose header is not the recorded header-only transformation of
  `upstream_sha256`;
- a `retired` row whose file exists;
- a `diverged` row without a non-empty `rationale` and `backport`.

It does not compare diverged files' hashes, and it ignores files without a row. So a pull request
fails only if it changes or deletes a file synced from Formal-Math, and the failure prints the
command that records it:

```bash
python3 scripts/check_formal_math_sync.py --record-divergence PATH... \
    --rationale 'why ATLAS differs' --backport pending   # or the Formal-Math backport PR URL
python3 scripts/check_formal_math_sync.py --retire PATH...   # for a deleted synced file
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
unchanged; `retired` rows carry over while their file stays absent. A periodic sync also catches
upstream changes and drift in diverged files, which preflight does not compare.
