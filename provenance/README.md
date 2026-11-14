# Formal-Math sync manifest

`formal-math-sync.json` records how each Lean file under `MathlibExt`, `MathlibExtTest`, `CSLibExt`,
`CSLibExtTest` and `WantedExt` relates to
[`fairinternal/formal-math`](https://github.com/fairinternal/formal-math), the upstream source of
much of that code. Formal-Math is an upstream source snapshot, not a Lake dependency: files arrive
through reviewed ATLAS pull requests, and Formal-Math never depends on ATLAS.

## Schema (version 1)

Top level: `schema_version`, `upstream` (`repository`, full `commit`), `lean_toolchain`, `roots`,
`counts` per disposition, `total`, `rows_digest` (SHA-256 over the rows, each serialized as
sorted-key compact JSON followed by a newline), and `rows`, sorted by path, one per line.

Each row has `path`, `disposition` and `published_sha256` (SHA-256 of the ATLAS file's bytes).
`upstream_sha256` is the SHA-256 of an upstream file's body: the text after its leading license or
authorship block comment, without leading blank lines.

| Disposition | Meaning | Extra fields |
| --- | --- | --- |
| `identical` | Meta header, then the body of the upstream file at `upstream.commit`. With `"header": "upstream"`, the file is the upstream file byte for byte, keeping its third-party copyright and license header. | `upstream_sha256`, optional `header` |
| `attributed` | As `identical`, with a recorded attribution notice (for example Apache 2.0 Section 4 provenance) between the Meta header and the body. | `upstream_sha256`, `notice` |
| `behind` | Header-only copy of an older upstream version of the same path; the next sync brings it current. | `upstream_commit` (the commit that introduced that version), `upstream_sha256` (its body), optional `notice` or `header` |
| `diverged` | Reviewed ATLAS-side change to a file that exists upstream. | `upstream_sha256` (current upstream body), `rationale`, `backport` |
| `local` | Not taken from Formal-Math: the path was never upstream, or the file is third-party FLT content that keeps its own header. | optional `rationale` |
| `retired` | Deleted upstream; ATLAS still publishes it. | `upstream_commit` (the deleting commit) |

## Checking

`scripts/check_formal_math_sync.py` verifies the manifest offline, using only the Python standard
library: one row per root-library file (no missing, extra, duplicate, absolute, escaping or
symlinked paths), every `published_sha256`, the header-only transformation of `identical`,
`attributed` and `behind` rows, and a rationale and backport status on every `diverged` row.
`scripts/check.sh preflight` runs it in report-only mode: it prints every mismatch and exits 0.
`--strict` exits 1 on any mismatch; `FORMAL_MATH_SYNC_STRICT=1 scripts/check.sh preflight` runs
preflight that way. Report-only is the default so that open pull requests editing synced files are
not blocked before they can record a divergence; making it blocking is a maintainer decision.

A pull request that edits a synced file should either land the fix in Formal-Math first and sync,
or mark the row `diverged` with a rationale and the Formal-Math backport pull request in
`backport`. The next sync clears the divergence once upstream has the change.

## Refreshing

```bash
scripts/sync_formal_math.py --formal-math <formal-math checkout> --commit <sha> \
    [--rationales divergences.json] [--report sync-report.md]
```

The script reads Formal-Math only through `git` in the given local repository and never fetches.
It regenerates the manifest and prints a report of added, removed, changed and diverged rows. It
refuses to write the manifest when a file newly diverges without a rationale; pass those as
`{"<path>": {"rationale": "...", "backport": "..."}}` in `--rationales`. Rows already diverged in
the manifest keep their rationale.
