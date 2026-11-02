# Tau Ceti quality indicator evaluation

`scripts/quality_eval.py` runs the three AI-judge indicators from
[Simple quality indicators for Lean libraries](https://taucetiproject.org/blog/2026-10-28-simple-quality-indicators-for-lean-libraries/):

1. A theorem has a hypothesis that can be **deleted entirely**, leaving the rest of the statement unchanged. Weakening an assumption does not count.
2. A theorem duplicates Mathlib, Batteries or Lean core, or is a one/two-line special case of a single mathematical declaration there. Generic equality, logic and structure laws applied to Atlas's own definitions do not count.
3. A file repeats nontrivial mathematical reasoning in at least two proofs that would benefit from a shared lemma. Short calculations and thin wrappers do not count.

The official scanner, sampling algorithms, prompts, schemas, file-evidence validator and read-only Claude runner are imported from an **external pinned checkout** of
[lean-quality-indicators](https://github.com/RemyDegenne/lean-quality-indicators), at
`0f3f1778e65c3118ffb9bf4644e55b2b406abede`. The upstream implementation is not vendored into Atlas.

## Scope and interpretation

The primary Atlas population is **MathlibExt and CSLibExt**. WantedExt, both test libraries, legacy Atlas, archived v1 and certificate directories are excluded.
Public, nondeprecated source `theorem` and `lemma` declarations are sampled uniformly without replacement, respecting the Lean module system's public-section visibility.
Generated declarations are not in the source population. Private helpers are excluded from the primary theorem rates, as in the article.
Whole-file reviews see every definition, statement and proof, including private helpers.

The control is the **exact Mathlib version Atlas pins**, excluding Tactic, Util, Lean, Testing and Deprecated directories from its population.
Both libraries receive all three indicators, including the inclusive Mathlib duplication control.
Results are reported **per root**, never as one composite Atlas quality score.
CSLibExt's duplication rate means duplicates of Mathlib/Batteries/core only: **CSLib redundancy is not measured**, and CSLibExt has no domain-matched control.

`--private-theorems N` optionally adds a separate duplicate-only sample of N private MathlibExt helpers and N private Mathlib helpers.
Do not mix this supplementary stratum into the public theorem numerator.
The duplication report distinguishes proofs that already call the upstream declaration (**wrappers**) from independent **re-proofs**.
Provenance markers, file composition, initial raw flags and retry/rejection counts are reported separately.

A flag is a **judge claim**, not a demonstrated mathematical defect. `none_found` means no justified finding was identified, not that the target is correct.
Wilson 95% intervals capture sampling uncertainty, not model error, source faithfulness or systematic bias.
Intervals are pointwise, not multiplicity-adjusted. MathlibExt-minus-Mathlib differences use Newcombe intervals.
The article's historical percentages are context, not a controlled comparison with this run.

Missing judgments never count as negative findings. Partially reviewed files count as judged, matching upstream, and the report gives bounds obtained by making every partial negative positive.
Not-applicable whole files remain in the denominator. A secondary rate conditions on at least two named theorem/lemma declarations; this is a composition diagnostic, not the primary indicator, because definitions and instances can contain proofs too.

## Reproducible run

Requirements: Python 3.11+, Git, the pinned official suite and Atlas dependencies already fetched at their exact `lake-manifest.json` revisions.
Judging also needs an authenticated Claude Code CLI supporting `--safe-mode` and `--restricted`.
Preparation, tests and reporting make no model calls. Repository CI never launches inference.

```bash
git clone https://github.com/RemyDegenne/lean-quality-indicators ../lean-quality-indicators
git -C ../lean-quality-indicators checkout 0f3f1778e65c3118ffb9bf4644e55b2b406abede
git clone --depth 1 --branch v4.35.0 https://github.com/leanprover/lean4 ../lean-core

# Optional compiler provenance for generated upstream names. Use only a built
# or verified cached Mathlib at the manifest pins. It does not judge theorems.
QUALITY_SYMBOLS_OUTPUT=/absolute/path/symbols.json \
  lake env lean scripts/quality_symbols.lean

python3 scripts/quality_eval.py prepare \
  --upstream ../lean-quality-indicators --lean-core-repo ../lean-core \
  --declaration-index /absolute/path/symbols.json \
  --run-dir ../atlas-quality-run --theorems 300 --files 100 \
  --private-theorems 100 --seed 0

# Six judgments: one public target per library and indicator.
python3 scripts/quality_eval.py judge \
  --run-dir ../atlas-quality-run --label sonnet-pilot \
  --model claude-sonnet-5-5 --theorem-limit 1 --file-limit 1 \
  --private-limit 0 --jobs 6
python3 scripts/quality_eval.py report \
  --run-dir ../atlas-quality-run --label sonnet-pilot --require-complete

# 1,600 judgments with these sample sizes, including the private supplement.
python3 scripts/quality_eval.py judge \
  --run-dir ../atlas-quality-run --label sonnet-primary \
  --model claude-sonnet-5-5 --jobs 12
python3 scripts/quality_eval.py report \
  --run-dir ../atlas-quality-run --label sonnet-primary --require-complete
```

The compiler index is optional. Without it, citations must match a declaration found by the source scanner; the index additionally recognizes generated names by their originating module.
Supply Lean core sources for a complete reference view. If omitted, their absence is explicit in the report.

Keep runs outside the checkout. A new preparation requires a new directory.
Rerun the same judge command to resume; provisional results left by an interrupted write are preserved and re-judged.
A different model, selection, CLI version, budget or adapter requires a different label.
The adapter's bytes are frozen into the run and checked before re-aggregation; do not edit it during a run.
For a relocated bundle, use the same frozen adapter and `--upstream /new/path/to/pinned-suite` on `judge` or `report`.
Recorded trace and evidence paths are rebased without changing stored verdicts.

Defaults: ten minutes and two API-equivalent dollars per attempt, with one retry.
A failed or invalid judgment stops new admissions and exits nonzero. There is no model fallback.
Rejected source-access attempts never count as successful judgments; bounded fresh retries use the same permitted roots, not wider access.

## Evidence and isolation

Preparation freezes committed Lean sources and package configuration, without Git metadata, scripts, credentials or previous results.
Source archives reject symlinks. Source, input, protocol, compiler-index and adapter hashes bind the run.
Each target is judged in a fresh session with only Read, Grep and Glob, restricted to its frozen sources and pinned dependencies.
Judges cannot run Lean, execute a shell, browse the web, write files or read previous verdicts. Sessions run with `--safe-mode --restricted`; the managed Meta preset still loads, and its directory is the only grant allowed besides the permitted sources. Traces must show every permitted root granted, no grant overlapping the run directory, and every tool path inside a permitted root.
Each library's judges work in `views/<library>/`, which holds hard links (or copies) of exactly that library's permitted sources: Atlas and every pinned dependency for Atlas targets, the same dependencies without Atlas for the Mathlib control.
The message lists that combined directory last, so a judge looking for a declaration anywhere can search one permitted root instead of a parent that also holds other material.
The Mathlib control cannot read Atlas. Preparation and verification check that each view contains exactly the expected files and hashes.
Traces check actual tools, source paths, selection patterns (including absolute or `..` brace alternatives), model and CLI version.

File findings must quote source text within their line ranges. Hypothesis findings must quote a binder from the claimed declaration/variable context.
Duplicate findings must cite a real source declaration, or a compiler-indexed declaration whose module file exists in the permitted Mathlib, Batteries or Lean-core sources. Annotations after the name are ignored and Lean-core paths may omit `src/` (counted as `citation_normalized`); a real, nondeprecated declaration cited in the wrong module is accepted but counted as `citation_module_corrected`. Absolute citations outside the permitted sources are rejected and retried. Derivations must be at most two lines. These checks establish source binding, **not** that the proposed argument or replacement is mathematically valid.
Compilation and independent semantic review remain separate requirements before acting on an individual flag.

Declared adaptations: pinned rather than newer-master Mathlib for hypotheses; instruction-isolation/exact-directory guidance on prompts; one combined per-library source root; at most two-line duplicate derivations; wrong-module citation correction; wanted-command boundaries; module-aware visibility; positive source-binding validation; optional private strata.
Validation/retry asymmetry can change flag rates, so rejected-positive-then-negative and first-attempt statistics are explicit.

## Tests and artifacts

```bash
# Deterministic tests, with explicit skips if the official suite is unavailable:
python3 -m unittest discover -s scripts -p test_quality_eval.py -v

# Also exercise the real pinned scanner, snippets, source binding, preparation,
# relocation, stale protocol/source rejection and populated reports:
QUALITY_INDICATORS_DIR=../lean-quality-indicators \
  python3 -m unittest discover -s scripts -p test_quality_eval.py -v
```

- `manifest.json`: scope, pins, population census, seed and hashes.
- `theorems.json` / `files.json`: selected identities, exact inputs and commit/line-pinned source links.
- `corpus/` / `views/` / `samples/`: frozen sources, the per-library judge views of them, and judge inputs.
- `runner/` / `judges/<label>.json`: frozen adapter, model, effort, CLI and selected tasks.
- `<indicator>/<label>/results/`: accepted verdicts, raw responses, attempt transcripts and rejection logs.
- `reports/<label>/summary.json`: root-level rates, wrapper/re-proof splits, retry diagnostics, partial bounds and difference intervals.
- `reports/<label>/findings.json` / `report.md`: candidate improvements and source evidence.

Do not commit run directories, third-party protocol copies or raw transcripts to the PR.
These indicators do not establish definition fidelity, source faithfulness, nonvacuity, proof completeness, importance or difficulty. Do not use their zero threshold as a land gate.
