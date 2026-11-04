# Binary64 add/multiply conformance diagnostic

This core-only diagnostic compares Lean 4.35 `Float.Model`, MPFR and scalar
hardware binary64 add/multiply, round-to-nearest ties-to-even. Non-NaNs match
exact bits, including signed zero. NaNs match only by class: payload, sign,
signaling, exception flags and traps are outside the contract. No other
operations, formats, rounding modes or numerical-stability claims are covered.
Finite test evidence is not an exhaustive correctness proof or a C2/C3 claim.

## Run

Requirements: x86_64 Linux, Python 3.9+, a C compiler supporting the supplied
GCC/Clang flags, `ldd`, GNU `objdump`, GDB with Python and debuginfod controls,
installed Lean 4.35, and matching MPFR/GMP development
headers and runtime libraries. Nothing is downloaded or installed by the driver.
It uses no Lake build or Mathlib cache.

```
python3 scripts/float_conformance/run.py --out /tmp/float-conformance-run
python3 scripts/float_conformance/test_compare.py \
  --dataset /tmp/float-conformance-run --out /tmp/float-controls-normal
python3 -O scripts/float_conformance/test_compare.py \
  --dataset /tmp/float-conformance-run --out /tmp/float-controls-optimized
```

Output directories must be new. `--lean` and `--leanc` select installed tools;
`CC`, `CPPFLAGS`, `CFLAGS` and `LDFLAGS` support a private header/library prefix.
Numerical-safety flags follow user C flags. For example:

```
CPPFLAGS=-I/prefix/include LDFLAGS=-L/prefix/lib64 CFLAGS=-DNDEBUG \
  python3 scripts/float_conformance/run.py --out /tmp/float-run-ndebug
```

The driver checks at least 10 GiB free and write/fsync capability, pins execution
to one allowed CPU, builds into the output directory, runs a populated one-pair
smoke, then the full corpus. Lean can create runtime helper threads. Each child
command has a 180-second timeout; its exact argv is recorded before launch and
its complete output, exit and elapsed time are retained. Missing dependencies,
bad environment, incomplete/invalid results and mismatches fail the process.
Checks do not depend on Python `assert` or C `assert`.

The default corpus has 8,192 distinct ordered operand pairs (`--pairs` permits
8,192..16,384). It contains the F-1 pairs, an ordered 16-value special-value grid,
ties of both signs/parities, cancellation, boundary neighbors, 4,096 SplitMix64
pairs and nearby-exponent pairs. Duplicate candidates are counted and suppressed;
the emitted input has no duplicates. `corpus.json` records group counts and the
SHA-256 of `inputs.bin` (big-endian uint64 A then B); text and labeled JSON retain
the same operands. `rows.jsonl`, `mismatches.jsonl` and `summary.json` retain every
comparison and output-class count. The default elan launcher reports the selected
toolchain prefix; the driver then executes and hashes that prefix's actual Lean
compiler and its resolved dynamic libraries. `tool-provenance.json` binds selected
tool entries to their command receipts, and `runtime-hashes.json` includes the
emitted `Model.c`, sources, headers, executables and resolved dynamic libraries.
The launcher is recorded separately. Tool lookup preserves the invoked path and
basename, including symlink names that select elan or compiler-wrapper behavior.
Hashes read the actual file bytes through that path; canonical targets are also
recorded and hashed, without substituting their names into the invocation.
This applies to the launcher, toolchain compiler, `--leanc` and `CC` entries;
arbitrary hidden wrapper chains are not pinned.
`evidence.py test --dataset RUN --out NEW_DIRECTORY` checks the actual compiler
hash and rejects omitted/wrong hashes through real normal and optimized processes.
The CI path runs these provenance negatives and `test_tools.py`: real-process
direct/hard-link/symlink dispatch cases for each tool role, real Lean/elan cases,
and missing/non-executable failures in both Python modes. Their command receipts,
outputs and selected-path/hash records are included in the evidence package.

## Why the paths differ

`Model.lean` calls `Float.Model.ofBits/add/mul/toBits` directly, which use core's
integer mantissas, exponent arithmetic and explicit rounding. It never calls
`Float.add`/`Float.mul` C externs. Generated C preserves model calls.

`oracle.c` includes the installed `mpfr.h`/`gmp.h` definitions. MPFR operands and
results have 2200-bit precision. Every finite binary64 value is a multiple of
2^-1074 below 2^1024 in magnitude, so exact addition needs at most 2099 bits;
multiplication needs at most 106 significant bits. MPFR's exponent range is
checked, every finite intermediate must report exactness, and `mpfr_get_d` makes
the sole lossy binary64 rounding. Operand roundtrips are checked. Header/runtime
versions must match for both MPFR and GMP. The oracle reports GMP's header
version macros and runtime version, and rejects a mismatch before arithmetic.
Version equality is a provenance check, not proof of arbitrary ABI compatibility.
No hand-declared MPFR ABI is used.

Separate non-inlined `hw_add` and `hw_mul` functions use scalar SSE2 arithmetic.
The process checks RNE, FTZ=0 and DAZ=0 before/after execution and counts hardware
calls. Source and native disassembly/live traces must accompany an independence
claim; different wrapper names or agreement alone are insufficient. Every driver
now retains and validates disassembly plus live GDB traces of its newly built
model and oracle on the one-pair smoke input. The trace is distinct from the
full 8,192-pair comparison. It checks actual scalar instructions, core integer
and rounding call paths, observed stacks, direct MPFR callers and matching raw
smoke outputs. Missing symbols, unhit breakpoints, tracer errors and invalid
evidence fail the driver, including under Python `-O`. GDB launches only these
new processes, with initialization/auto-load and debuginfod disabled. MPFR can
recursively enter `mpfr_mul`, so trace direct calls from `oracle_pair` separately.
These paths still share the host and may share low-level GMP ancestry.

The CI path also exercises normal and optimized native-evidence controls:
missing/malformed trace records, changed instructions/callers, failed receipts,
an actually missing breakpoint, missing/failing tracers, and matching/mismatched
GMP versions. The GMP negative compiles a private copied header with only one
version macro changed, then requires the intended runtime guard to fail.
Full native traces, disassembly, inputs, compiler receipts, copied-header
controls and their real exit codes are selected into the CI evidence package.
Unsupported debugger/ptrace environments fail rather than skip this evidence.

The regression command runs the real comparator CLI on the full positive corpus,
a permitted NaN-payload change, three isolated arithmetic output corruptions,
and missing/duplicate/malformed/out-of-range/empty records in each input stream.
Each child argv and exit is retained. These are parser/comparator controls, not
faults injected into the arithmetic libraries.

## Provenance and remaining gates

Sole diagnostic author: Codex, requested gpt-6-astra/high; exact serving identity
was not exposed. `Model.lean` reuses this author's earlier diagnostic
`ModelProbe.lean`, SHA-256
`5a906d92d471101395bea13ab84e4fa9b18aa48ecb05e9f016038ce64b1a9332`.
The repair evidence contains a standalone `PREDECESSOR.json` receipt checking
the actual predecessor bytes against this digest, plus a retained source copy.
The 26 operand pairs in `fixtures.json` are explicitly reused from F-1 #1035's
`FLOAT-1035-TESTS.lean`, SHA-256
`edc8137705c534bcb63a9a6c948cb81db0c2c0e47dd41d69dda9da5221367c36`.
No F-1 proof, production library, new float model or reviewer-authored Lean is
copied or changed. The corpus generator defines inputs, not a rounding oracle.

Draft publication may be used to obtain CI. Acceptance or release readiness
requires review of the current source and passing CI for that exact commit;
this diagnostic does not establish human approval, C2/C3 or Day90 acceptance.
The workflow checks out the PR head SHA (the event SHA for non-PR runs), verifies
and records HEAD, and retains selected evidence for 14 days using a pinned
official upload action. Inputs, full outputs, comparisons, source and compiler
hashes, command receipts and comparator controls are selected by exact filenames;
temporary directories and caches are excluded. Partial failed-run evidence is
also retained; a failed test or evidence step still fails the job. A local package
check is not an executed GitHub workflow. Support for another platform/compiler
needs fresh runtime/ABI and call-path evidence.
