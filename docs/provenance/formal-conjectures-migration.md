# Formal Conjectures migration record

The nine Lean files that lived in `Atlas/FC/` (and, for one revision, in
`OpenConjectures/FormalConjectures/`) are now part of the root Lake build. This
file records the destination of every one of them, the declarations that were
extracted along the way, and how each statement relates to its source in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).

Every destination module keeps the original declaration names and namespaces
(`Erdos138`, `Erdos337`, `Green25`, `OeisA108081`, `OeisA211417`, `OeisA22030`,
`OpenQuantumProblem35`, `WrittenOnTheWallII.GraphConjecture100`,
`WrittenOnTheWallII.GraphConjecture314`), keeps the Meta header and the
Apache-2.0 adaptation notice for the Formal Conjectures portions, and states in
its module docstring which declarations are verbatim copies.

## Destinations

| Source file (`Atlas/FC/`) | Destination |
| --- | --- |
| `Erdos138_dvd_two_pow_solution.lean` | `MathlibExt/Combinatorics/AP/VanDerWaerdenRatio.lean` |
| `Erdos337_ruzsa_turjanyi_solution.lean` | `MathlibExt/Combinatorics/Additive/RuzsaTurjanyi.lean` |
| `Green25_upper_solution.lean` | `MathlibExt/Combinatorics/Additive/RestrictedSumsetPartition.lean` |
| `OeisA108081_count_words_in_x_is_a_shifted.lean` | `MathlibExt/Combinatorics/Words/ReversalShiftWordCount.lean` |
| `OeisA211417_supercongruence_solution.lean` | `MathlibExt/NumberTheory/FactorialRatioSupercongruence.lean` |
| `OeisA22030_conjecture.lean` | `MathlibExt/NumberTheory/NonlinearRecurrenceA22030.lean` |
| `WrittenOnTheWallII_GraphConjecture100_conjecture100.lean` | `MathlibExt/Combinatorics/SimpleGraph/IndependenceNumberCeilingBound.lean` |
| `WrittenOnTheWallII_GraphConjecture314_conjecture314.lean` | `MathlibExt/Combinatorics/SimpleGraph/WellTotallyDominatedP5Free.lean` |
| `OpenQuantumProblem35_ame_9_10_open_solution.lean` | `PhyslibExt/QuantumInfo/AbsolutelyMaximallyEntangled.lean`, with general helpers in `MathlibExt` (below) |

## Replacing `FormalConjecturesUtil`

All nine files imported `FormalConjecturesUtil`, which is not a root dependency.
It supplied two things.

1. **The `@[category ...]` and `AMS` attributes.** These are dropped; each
   migrated statement records its Formal Conjectures category, and the current
   upstream category, in its docstring instead.
2. **Definitions from `FormalConjecturesForMathlib`.** Each one is either reused
   from Mathlib or ported into `MathlibExt` with the Apache-2.0 header of its
   source file.

| Formal Conjectures declaration | Resolution |
| --- | --- |
| `SimpleGraph.indepNum`, `SimpleGraph.IsIndepSet`, `SimpleGraph.IsNIndepSet`, `SimpleGraph.IsIndepSet.card_le_indepNum`, `SimpleGraph.exists_isNIndepSet_indepNum` | Already in Mathlib (`Mathlib/Combinatorics/SimpleGraph/Clique.lean`); reused |
| `Choose.choose_pow_mul_pow_mul_modEq_choose_nat` | Already in Mathlib (`Mathlib/Data/Nat/Choose/Lucas.lean`); reused |
| `Set.IsAsymptoticAddBasis`, `Set.IsAsymptoticAddBasisOfOrder` | Already ported in `MathlibExt/Combinatorics/Additive/Basis.lean` |
| `Set.isAsymptoticAddBasisOfOrder_iff_sum` | Added to `MathlibExt/Combinatorics/Additive/Basis.lean` (additive form of the source's `isAsymptoticMulBasisOfOrder_iff_prod`) |
| `Set.IsAPOfLength`, `Set.IsAPOfLengthWith` | Already ported in `MathlibExt/Combinatorics/AP/Basic.lean` |
| `Set.IsAPOfLength.zero`, `Set.IsAPOfLength.one`, `ContainsMonoAPofLength` | Added to `MathlibExt/Combinatorics/AP/Basic.lean` |
| `Finset.restrictedSumset` | Ported to `MathlibExt/Combinatorics/Additive/RestrictedSumset.lean`, with `Finset.restrictedSumset_eq_metaMathlibExt_two` bridging it to the existing `MetaMathlibExt.restrictedSumset` |
| `SimpleGraph.indepNeighborsCard` | Ported to `MathlibExt/Combinatorics/SimpleGraph/NeighborhoodIndependence.lean` |
| `SimpleGraph.degreeL2Norm` | Ported to `MathlibExt/Combinatorics/SimpleGraph/DegreeL2Norm.lean` |
| `SimpleGraph.IsTotalDominatingSet`, `IsMinimalTotalDominatingSet`, `IsWellTotallyDominated` | Ported to `MathlibExt/Combinatorics/SimpleGraph/TotalDomination.lean` |

## General helpers extracted from the AME development

These were Atlas-original declarations inside
`OpenQuantumProblem35_ame_9_10_open_solution.lean` with no quantum content. They
moved to `MathlibExt` in the `MetaMathlibExt` namespace, which the physics module
opens.

| Declarations | Destination |
| --- | --- |
| `detFinThreeInt`, `detFinFourInt`, `detFinFiveInt` and their `_eq` lemmas | `MathlibExt/LinearAlgebra/Matrix/DetFinSmall.lean` |
| `pasteOn`, `pasteOn_mem`, `pasteOn_not_mem`, `splitOnEquiv`, `finsetMapEquiv`, `finsetMapComplEquiv` | `MathlibExt/Data/Finset/PasteSplit.lean` |
| `sum_stdAddChar_dot`, `sum_stdAddChar_affine`, `stdAddChar_mul_star`, `norm_stdAddChar` | `MathlibExt/Analysis/Fourier/ZModAddCharSum.lean` |
| `sum_four_comm`, `sum_separable`, `sum_product_separable` | `MathlibExt/Algebra/BigOperators/SeparableSum.lean` |

## Statement faithfulness

Each migrated main statement was compared with its source in
google-deepmind/formal-conjectures at `d8d031d`. Eight of the nine are verbatim
copies; `MathlibExtTest`/`PhyslibExtTest` carries, for each of them, an `example`
that writes the upstream statement out and proves it by the migrated
declaration.

The exception is `Green25.green_25.upper`. Upstream states it as a value
question with an opaque `green_25.upper.answer : ℕ → ℕ` left as `sorry`, so the
upstream form cannot be proved without choosing the witness. The migrated
statement quantifies the witness existentially and strengthens the last
conjunct from `¬ ∀ᶠ N, Property25 ..` to `∀ᶠ N, ¬ Property25 ..`; the test file
derives the upstream (weaker) conjunct from it. Upstream records the same
mathematical content, for the explicit witness `k N = ⌈N ^ (23/40)⌉`, as the
`research solved` theorem `green_25.variants.upper_pow_23_40`.

All nine statements carried the Formal Conjectures category `research open` at
the revision these developments were written against. At `d8d031d` upstream
records all nine as `research solved`; four of them
(`erdos_138.variants.dvd_two_pow`, `count_words_in_x_is_a_shifted`,
`supercongruence`, `ame_9_10_open`) cite Lean proofs derived from these Atlas
proofs, and the rest cite independent proofs. The migrated docstrings say so;
nothing here relies on the upstream status, because each statement is proved in
this repository from Lean's standard axioms only.
