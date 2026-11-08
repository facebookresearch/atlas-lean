# v1 target/report inventory

`inventory_v1.py` joins archived target metadata to historical report rows at
an immutable Git commit. It does not scan, compile or accept Lean declarations,
resolve source semantics, compute a helper closure, or generate a blueprint.

## Setup and runs

Use Python 3.11+ on Linux and the pinned dependency below. Atomic no-overwrite
publication requires libc/kernel support for `renameat2(RENAME_NOREPLACE)`;
unsupported platforms/filesystems fail rather than fall back to a replacing
rename.

```sh
python3 -m pip install -r scripts/requirements-inventory.txt
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s scripts -p test_inventory_v1.py -v
```

From the repository root, supply a commit or local ref and a **new** output
directory. Refs are resolved to full commit hashes before reading files; no
fetch, checkout, index changes, network requests or Git writes are performed.

```sh
python3 scripts/inventory_v1.py --base HEAD --book AlgebraNotes --output /tmp/atlas-inventory-pilot
python3 scripts/inventory_v1.py --base HEAD --output /tmp/atlas-inventory-full
```

For optional pointers to an existing source roadmap, also pass
`--prior <local-blueprint-commit>`. This matches existing paths by book and
one-based filename ordinal. Zero or multiple candidates remain explicit; paths
and blobs are pointers, not proof evidence. No article content is read.

`--repo` defaults to the current directory. Output directories are never
reused or overwritten. Both JSON outputs are fully serialized before the output
directory is created, so invalid input or a serialization failure leaves no
partial inventory. The source scope is enumerated and file sizes recorded from Git metadata;
only `targets.yaml` and `report.json` contents are read.

## Output contract

`inventory.jsonl` has one row per source target, in book/ordinal order:

- `schema`: `atlas-v1-inventory/2`.
- `key`: `(book, zero-based target_ordinal, source_sha256)`. The SHA-256 is
  computed over canonical UTF-8 JSON of the four decoded source fields, with
  sorted keys, compact separators and Unicode retained. Formatting changes do
  not change this hash; decoded value changes do. Ordinals prevent duplicate
  targets from being silently collapsed.
- `source` and `source_fields`: frozen file path, revision, Git blob, file
  SHA-256 and decoded `description`, `kind`, `location`, `name`.
- `source_span`: zero-based byte offsets `[byte_start, byte_end)` and
  **inclusive, one-based citation lines** `line_start` through `line_end`, plus
  a raw-span SHA-256. A block record runs from its first key through its final
  key/value lexical extent; a flow mapping includes its braces. Value-node
  extents preserve quoted and block-scalar data, including `#` text and
  keep-chomping blank lines, while excluding inter-target separator trivia.
  The sequence dash and first-line indentation are outside the span, so its
  byte slice need not be standalone YAML.
- `legacy_matches`: all report rows for the ordinal, preserving report-row
  position/hash, declared-name arrays, file hints/blob provenance and the
  unmodified historical claims. This is a relation: multiple names or rows
  must not be zipped, deduplicated or resolved by taking the first one.
- `duplicate_source_ordinals`, `prior_roadmap_candidates`, `gaps`: exact
  decoded-source duplicates, optional existing-path candidates and explicit
  missing/ambiguous/mismatched metadata. Report text differences are compared
  after whitespace folding; a difference is not itself a mathematical defect.

`manifest.json` records exact base/prior hashes, runtime PyYAML version, tool
code SHA-256, file sizes/hashes, Git commands, output hash and per-book counts. It retains
out-of-range report rows and books missing a metadata file. Duplicate report
ordinals stay attached to their source row and are marked ambiguous. A run with
no source targets fails rather than producing an apparently complete empty
inventory.

Both files are written and fsynced in an owned sibling temporary directory,
then the completed directory is published atomically without replacing an
existing destination, even an empty one created concurrently. Write or publish
failures clean up staging and leave no partial output directory. Consumers must
treat `manifest.json` as the completion marker and verify `inventory_sha256`
against `inventory.jsonl` before consuming a run.

All report rows and repository/summary assertions are wrapped with
`evidence: "HISTORICAL ONLY"`. Pass, proof, axiom and compiler assertions never
become current validation results. Missing declared files are reported, but
file existence does not establish that a declaration is defined there.

Counts distinguish target rows, report rows, declaration references, distinct
reported names within each book, and report-mentioned non-target dependency
names. The last category is a historical dependency hint, **not** a full
helper count or transitive dependency closure. There is no lexical or compiler
declaration count.

## Parsing and regression boundary

Targets must be a nonempty YAML sequence of mappings with exactly the four
string fields above. PyYAML's safe loader handles quoted, folded, block and
flow scalars. Aliases, merges, duplicate mapping keys and unsafe tags are
rejected. Reports must contain `statements.details`; each row needs the four
string fields and a nonnegative integer `idx` (not a boolean). Optional
`lean_declaration`, `lean_file` and `deps` fields are strings or null. JSON
duplicate keys and non-finite numbers are rejected. Other report fields are
retained as historical data, not interpreted. Non-finite numbers are rejected
throughout the report, including overflow literals such as `1e9999` in nested
header or row fields.

The existing CI preflight job runs these tests in a temporary Python venv with
the pinned requirements, then checks a populated inventory from `HEAD`. The
existing deterministic repository policy checks remain unchanged.

The tests use invented fixtures only. They exercise Unicode/CRLF byte spans,
safe parsing failures, stable source hashes, many-to-many matching, missing
files/rows, duplicate ordinals, orphan reports, ambiguous prior paths and a
populated CLI run with no-overwrite protection. Real corpus outputs belong in
separate run directories, not in source control.

Before relying on a parser change, compare every `(book, ordinal)` decoded
source/hash against a frozen prior inventory and retain any differences in the
run output. Raw-span hashes may legitimately change when the span definition
changes; they must not be confused with source-identity hashes. Primary-source
fidelity and any later VMVM/semantic review are separate workflows.
