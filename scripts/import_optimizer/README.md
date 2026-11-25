# Lean import optimizer

The optimizer proposes smaller import headers with the pinned Lean `lake shake`
and ImportGraph tools. It compiles the original and candidate in isolated roots,
then compares owned declarations, visibility, types, definition values, universe
parameters, and axiom dependencies. It saves patches; **it never applies them to
tracked sources**.

The command-line entry points are `scripts/generate_import_inventory.py` and
`scripts/optimize_imports.py`. This directory contains their native Lean helpers
and the optional source-reference proposal helper.

## Requirements

Use Python 3.10 or newer, a POSIX host, GNU `time` (`gtime` on macOS), and the
repository's pinned Lean toolchain. Prepare the root package's dependencies and
compiled artifacts using the normal
ATLAS build setup before optimizing library modules. No dependency versions are
changed by these scripts.

Build every dependency package before optimizing. Each Lake preparation watches
the module paths it may add under every captured `LEAN_PATH` entry, including
entries that do not exist yet, so a preparation that creates a dependency's
artifact root is rejected, and the output directory refuses later preparations.
Build the root package's own modules up to date as well: a preparation may
rebuild an existing artifact of a requested module only while nothing has pinned
it, so a stale root artifact that an earlier batch pinned blocks the run when a
later batch's Lake rebuilds it.

Run from the repository root. The inventory includes tracked root-package Lean
sources and read-only helpers under `scripts/`. It excludes `Atlas/`, `v1/`, and
Lean examples under `docs/`: those are not part of the root Lake build.

## Inventory

```sh
python3 scripts/generate_import_inventory.py \
  --root . --lean "$(elan which lean)" \
  --output .lake/import-manifest.jsonl
```

The generator uses Lean's native header parser, checks raw UTF-8 token positions,
and freezes each source's full SHA-256. It records the local dependency graph,
topological order, toolchain and project pins, plus checks that have not run yet.
`scripts/` helpers and generated sources are read-only. Use repeated `--reserve`
arguments to protect a tracked file or directory and every transitive local
consumer; `--checkpoint` protects one tracked file.

The manifest's companion `.meta.json` records the stamped header cache path and
hash. To reuse that cache on unchanged sources, pass `--headers PATH` and its
recorded `--headers-sha256 HASH` to the inventory generator. Changed or missing
inputs fail validation rather than silently refreshing evidence.

## Optimize a bounded batch

```sh
python3 scripts/optimize_imports.py \
  --manifest .lake/import-manifest.jsonl --output .lake/import-results \
  --lake "$(elan which lake)" --batch-size 32 --max-batches 1

python3 scripts/optimize_imports.py \
  --manifest .lake/import-manifest.jsonl --output .lake/import-results \
  --lake "$(elan which lake)" --batch-size 32 --max-batches 1 --resume
```

Positional repository-relative Lean paths select a subset of the frozen
inventory. The entire inventory is still source-checked. `--retry-blocked`
retries failed files while resuming; otherwise they stay recorded as blocked.
A bounded invocation can exit successfully with a nonzero `pending_count`.

One bulk Lake build prepares a batch and one Shake pass analyzes its modern
modules. A private Lake configuration under `.lake` limits compiler concurrency
without changing the production Lean options. Preparation uses the normal
`.lake/build` cache: the bounded compiler arguments can rebuild local dependency
closures, and a later ordinary build can rebuild them again. Use a separate
worktree for optimization runs if preserving a developer's warm cache matters.
Compatible modules share snapshot
processes; failed groups fall back to singleton verification.

A later batch's Lake preparation may add artifacts to root-package namespaces
an earlier batch pinned. Around each preparation (batched or per row):

- Before it, every cached inventory is checked again; every root-package
  artifact pinned so far in this process must keep the device, inode, ctime,
  mtime, size, mode and bytes it had when first pinned; and the root artifact
  root's top-level namespaces and module files must be those the last accepted
  preparation left.
- Also before it, whatever is cached, every artifact path of each module the
  build may add is probed under every searched root: each captured `LEAN_PATH`
  entry as written and resolved (missing entries included), the root artifact
  root and the compiler library.
- During it, on Linux, the root namespaces and the artifact root's ancestors
  are watched for moves and attribute changes, and the nearest existing
  directory of each probed path outside the root artifact root is watched for
  that name.
- After it, each root namespace keeps its directory node and resolved path,
  pinned artifacts are checked again, compiler and dependency inventories must
  be unchanged, probed paths outside the root artifact root keep their state,
  and Lake may remove nothing. It may only add artifacts of new modules among
  the requested targets and their frozen local dependencies, in existing or new
  namespaces or at the top level. An addition's module must have had no
  artifact under any searched root, and the addition may not be visible as
  another module under a nested or enclosing searched root. Every existing root
  artifact is stated before the build (no hashing); one whose identity changed,
  even with the same bytes, was rewritten. The state of a symlink, here and for
  probed paths, includes the file it resolves to, so a write through the link
  or a change of where it leads counts. Only artifacts of the requested
  targets and their frozen local dependencies may be rewritten, never a pinned
  one, and a rewritten artifact may not be visible as another module. A root
  namespace that resolves outside the root artifact root is checked like the
  compiler and dependency libraries, by its directories, not file by file.

The first rejection blocks that batch, and every later preparation is refused,
in this invocation and in later `--resume` invocations of the same output
directory; nothing taken during the rejected attempt is trusted. The rejection
and the top-level listing after the last accepted preparation are recorded
under `lake-custody/`, and accepted additions and rewrites under `lake-growth/`,
in the output directory. Accepted additions and rewrites are under custody from
their preparation on, like pinned artifacts. A root artifact present before the
run that nothing pinned or rewrote is trusted when first used, as at the start
of a run. A resumed invocation starts from that listing, and
before any child process runs, whatever its journal holds, every root-package
artifact an earlier invocation recorded under `lake-growth/` or pinned in a
compilation input manifest under `inputs/` must still have its saved bytes; the
identities read then are this invocation's custody. On resume, a
saved row's inputs may differ from the current tree only by recorded additions
with their recorded bytes, for modules none of its inputs provided and no searched root
outside the root artifact root provides now. Custody and
growth records are trusted run state: removing or changing them invalidates
these record-based checks. Recover from a rejection with a new output directory.

Each preparation writes `lake-custody/pending.json` before its Lake process
starts and removes it only after its listing and growth records, or its
rejection record, are saved. If the optimizer stops in between, for example on
SIGTERM or SIGKILL, the marker remains: a resume stops before running any child
process, and the output directory runs no further preparation. This covers the
optimizer process being terminated; it relies on atomic file replacement and
makes no claim about host crashes, power loss, or filesystems without atomic
rename. A killed optimizer can leave its Lake process group running. Make sure
that group has exited before using the worktree for another run; a new output
directory does not check artifacts that an interrupted preparation wrote.
`--retry-blocked` does not relax custody: if Lake rebuilds a stale or partial
artifact that an earlier row pinned, the retry is rejected too.

Each resume parses every saved compilation input manifest to recover root
receipts, then hashes each distinct root artifact. Startup cost therefore grows
with accumulated manifest data. Repeated short `--max-batches` invocations pay
that cost each time; avoid unnecessary resumes in long campaigns.

These checks compare identities and listings at the boundaries of each Lake
window, plus the Linux watch during it. They do not see a new file name created
and removed inside one window under the root artifact root, or for a probed
module on platforms without inotify; unpinned sidecars such as `.hash` and
`.trace`; changes by a privileged clock or on filesystems without stable inode
or ctime; a namespace, or a symlinked searched root, moved and restored inside
a window where only endpoints are compared; module search paths other than the
captured `LEAN_PATH` and the compiler library; or identity changes between
processes (a resume compares bytes, so a same-byte replacement between
invocations is accepted). Another output directory's run on the same worktree
can cause resume to fail closed. Use a new output directory after such a
rejection.

During validation, a phase retains compilation-input derivations and the
filesystem facts used to derive them. The facts are reread at native-command
boundaries and phase close; shared dependencies are checked once per window.
The retained data grows with both batch size and dependency-closure size.
For broad Mathlib imports, start with `--batch-size 4` and measure memory before
increasing it. More compiler threads and concurrent Lake jobs add to that memory
budget. Independent optimizer workers need separate writable worktrees, package
caches and output directories; do not modify their pinned inputs during a run.

Two options set the concurrency of one invocation:

| Option | Default | Effect |
| --- | --- | --- |
| `--lean-threads N` | 2 | `lean -jN` for every compiler and helper process, and for root-package modules that Lake builds (`.lake/lakefile-lean-jN.toml`) |
| `--lake-jobs N` | 1 | Lake runs up to `N` build jobs at once (`LEAN_NUM_THREADS=N` for every child) |

Each accepts an integer from 1 to 1024. A Lake build of root-package modules can
run up to `N * --lean-threads` compiler threads at once. Lean writes the same artifacts at
any thread count, but Lake's build trace includes the compiler arguments, so a
new `--lean-threads` value rebuilds the root-package modules in `.lake/build`.
`run.json` records both values (`lean_threads`, `lake_scheduler_threads`), and the
saved compiler, helper, and Shake receipts carry them. A resume must repeat the
original values; changed values stop before any child process runs. Start a new
output directory to use other settings. The run lock still allows one optimizer
per worktree.

Legacy files retain all imports because their imports also re-export transitive
dependencies. Their ImportGraph analysis is recorded as `no_change`, not as a
verified import reduction.

## Evidence and limits

`results.jsonl` journals per-file results; `summary.json` reports `verified`,
`no_change`, `blocked`, `readonly`, and pending counts. Verified candidates retain
their original and candidate sources, patch, compiler receipts, artifact hashes,
and declaration snapshots. Module names and source bytes after the import header
are preserved, as are import visibility modifiers. Modern candidate compilations
must produce all seven artifact parts; legacy compilations require their three
parts.

Resume requires the same source, manifest, compiler, helpers, project settings,
and pinned native inputs. It verifies saved evidence before accepting completed
work. Source edits, changed artifact bytes, failed commands, timeouts, and
incomplete subprocess cleanup are not accepted as successful checks. An
unrecovered source transaction from an older run stops with its backup intact.

A verified row establishes the individual module checks, **not** downstream
consumer compatibility, a whole-project build, or globally minimal imports.
Review a saved patch before applying it; then run the affected consumer builds
and `scripts/check.sh`. Import changes to files in the sync manifest also need
the normal [provenance update](../../provenance/README.md).

## Source-reference proposals

```sh
python3 scripts/import_optimizer/reference_imports.py original-seeds.jsonl \
  > reference-proposals.jsonl
```

This optional helper combines an official declaration-owner proposal with
constant owners recorded in native Ilean version 5 references. A seed contains
`module`, `original_guest_source_path`, and five pinned `files`: `source`,
`ilean`, `native_header`, `compiler_prefix`, and `owner_proposal`. Each pin has
`path`, `bytes`, and `sha256`. The original successful compiler prefix must be
bound to the owner output and actual compiled `.olean` with
`bind_owner_proposal`. Inputs from different compilations are rejected.

Reference proposals can preserve imports needed only by unused section binders,
but omit some notation, tactic, instance, and generated-syntax dependencies.
They remain suggestions and require candidate compilation and consumer checks.
Do not treat the historical replay fixture as evidence that current project
sources compile; see [testdata/README.md](testdata/README.md).

## Tests

The Python regressions in `scripts/import_optimizer/test_*.py` run without Lean
or downloads and are part of `scripts/check.sh preflight`. They execute small
subprocess fixtures, so `TMPDIR` must permit execution. `PYTHONPATH` exposes the
command-line modules in the parent `scripts/` directory:

```sh
PYTHONPATH=scripts python3 -m unittest discover \
  -s scripts/import_optimizer -p 'test_*.py' -v
```

Run the native smoke test explicitly with the current pinned toolchain:

```sh
python3 scripts/import_optimizer/smoke_test.py --lake "$(elan which lake)"
```

It creates a temporary Git/Lake project using only Lean's bundled `Std` library,
runs inventory generation and optimization, requires a populated verified result
and a patch removing unused imports, checks that the source stays unchanged, and
resumes the saved run. It then checks that a resume with other thread settings
is refused, and repeats the optimization and resume with `--lean-threads 3
--lake-jobs 2`. A second project runs three batches whose preparations build
into a namespace the first batch pinned, requires each to verify, resumes, and
checks that a resume refuses an artifact no preparation recorded. It performs
real compilation and declaration comparison;
it does not download packages or rewrite any ATLAS library.

To also exercise the legacy ImportGraph API, first build the pinned dependency
with the normal project setup, then pass its checkout:

```sh
python3 scripts/import_optimizer/smoke_test.py --lake "$(elan which lake)" \
  --import-graph .lake/packages/importGraph
```

That optional test verifies the checkout's commit against `lake-manifest.json`
and analyzes a real compiled legacy declaration.
