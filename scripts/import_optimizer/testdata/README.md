# Import optimizer test data

`reference_actual037.tar.gz` is a recorded replay fixture for
`scripts/import_optimizer/test_reference_imports.py` and
`scripts/import_optimizer/test_import_optimizer_snapshot_inputs.py`. It holds
native outputs saved from one earlier `lake build` of a single statement module,
plus the metadata that ties them together. The tests read it without running Lean.

## What it is not

- It is not an untouched or authenticated compile receipt. Host paths in the
  JSON metadata were rewritten after recording (see below), so the metadata
  files are not the bytes the original run wrote.
- It is not evidence that current ATLAS sources compile, or that the module
  builds with the Lean toolchain this repository pins today. The outputs were
  produced by Lean 4.34.1 (the version string in the `.olean` header). The
  recorded build environment values are kept as observed.
- The module source is not part of the ATLAS library; it is test input only.

## Members

| Member | Content | Changed after recording |
| --- | --- | --- |
| `input/original-source.lean` | Module source, including its source citation | No |
| `input/Statement.olean` | Compiled native module data | No |
| `input/Statement.ilean` | Native Ilean version 5 references | No |
| `input/header.json` | Parsed module header with byte spans | No |
| `input/official-owner-proposal.json` | `ImportGraph.Tools.MinImports` owner proposal | `resolved_olean` path relocated |
| `input/original-compiler-prefix.json` | Compiler command, artifact receipts, setup fields | Path fields relocated |
| `input/reference-compiler-prefix.json` | The prefix above bound to the proposal by `bind_owner_proposal` | Regenerated |
| `case-inputs.jsonl` | Seed pinning the unbound prefix | Path and pins recomputed |
| `bound-case-inputs.jsonl` | Seed pinning the bound prefix | Path and pins recomputed |

## Path relocation

Only string values that are filesystem paths were changed. Each recorded root
was replaced by a neutral root, keeping the rest of the path:

| Recorded root | Fixture root |
| --- | --- |
| Project checkout | `/fixture/project` |
| Toolchain home directory | `/fixture/user` |
| Timing output directory | `/fixture/results` |
| Mathlib cache directory | `/fixture/cache/mathlib` |
| CA bundle file | `/fixture/etc/ca-bundle.crt` |

Standard system directories (`/usr/bin`, `/bin`, and so on) are unchanged.
The relocated fields are the seed `original_guest_source_path`, the prefix
`source_path`, artifact and setup paths, compiler and `lake` arguments, the
working directory, path-valued environment variables, and the proposal's
`resolved_olean`. Module names, declaration names, byte counts, digests of
the included native files, timestamps and exit status are unchanged.

After relocation, the bound prefix was rebuilt with `bind_owner_proposal`
from the relocated prefix, the relocated proposal and the unchanged `.olean`,
and every dependent `bytes`/`sha256` pin and the archive checksum in
`test_reference_imports.py` were recomputed. Archive members use fixed
ownership, mode and zero timestamps.

The `bytes`/`sha256` receipts for build outputs that are not in the archive
(`.olean.private`, `.olean.server`, `.ir`, `.ir.sig`, `.c`, the setup JSON,
and process output) are the values recorded at build time. Some of those
files can embed build paths, so a rebuild under the fixture paths is not
expected to reproduce them.

The `.olean` records the Lake package name `formal-math`, matching
`native_setup_fields.package`; it is native data and was left as is.
