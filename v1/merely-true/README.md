# ATLAS v1 — `merely-true` variant

`merely-true` is a derivative of [ATLAS v1](../) that keeps only the
declarations whose **entire transitive dependency cone** is free of `sorry`,
`axiom`, `opaque`, and `native_decide`. Everything in this directory is
therefore checked end to end by the Lean kernel against Mathlib and Lean's
standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

Being *merely true* is a weaker property than being *faithful*: a declaration
here is a correct Lean theorem about the objects it defines, but whether those
definitions and statements faithfully capture the source textbook is assessed
separately (see `report.json` in each book directory of ATLAS v1). Use this
variant when you need a gap-free library to build on.

## How it was obtained

Starting from ATLAS v1:

1. Build the project-local declaration dependency graph.
2. Mark every declaration that is, or transitively depends on, a declaration
   using `sorry`, `axiom`, `opaque`, or `native_decide`, iterating to a fixed
   point.
3. Delete the source of every marked declaration. When a structure field is
   marked, the whole structure is removed.
4. Remove files left without any declaration, and repair the imports of the
   files that used them.
5. Rebuild the whole library with `lake build`.

The procedure only deletes code: apart from `import` lines and one `export`
list, no line was added or changed relative to ATLAS v1.

## Contents

| | ATLAS v1 | `merely-true` |
|---|---:|---:|
| Books | 26 | 26 |
| Lean files | 2,654 | 2,240 |
| Lines of Lean (excluding comments and blank lines) | 483,943 | 336,842 (70%) |
| `sorry` / `axiom` / `opaque` / `native_decide` | present | **none** |

Per-book statement lists (`targets.yaml`) and evaluation reports
(`report.json`) are not duplicated here: see `../Atlas/<Book>/`. The reports
describe ATLAS v1, so some statements they mark as passing are absent from
this variant.

## Building

```bash
cd v1/merely-true
lake exe cache get
lake build
```

The toolchain and Mathlib revision are pinned in `lean-toolchain` and
`lake-manifest.json` (identical to ATLAS v1). As in ATLAS v1, each book is an
independent development: import the modules of one book at a time, since a few
top-level names are defined in more than one book.

## License

Same as ATLAS v1: see [`../LICENSE`](../LICENSE).
