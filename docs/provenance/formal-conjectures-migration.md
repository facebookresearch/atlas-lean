# Formal Conjectures migration record

The nine Lean files that lived in `Atlas/FC/` (and, for one revision, in
`OpenConjectures/FormalConjectures/`) are accounted for in the root Lake build.
Eight developments are moved into root libraries; the A022030 result is
already in `MathlibExt`. This file records the destination or disposition of
each file, the declarations extracted along the way, and the relation to
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).

Each moved destination keeps the original main declaration names and namespaces
(`Erdos138`, `Erdos337`, `Green25`, `OeisA108081`, `OeisA211417`,
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
| `OeisA22030_conjecture.lean` | Reuse [`MathlibExt/NumberTheory/OeisA022030.lean`](../../MathlibExt/NumberTheory/OeisA022030.lean); retire the duplicate |
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
opens, or were replaced by existing Mathlib APIs at their use sites.

| Declarations | Destination |
| --- | --- |
| `detFinThreeInt`, `detFinFourInt`, `detFinFiveInt` and their `_eq` lemmas | `MathlibExt/LinearAlgebra/Matrix/DetFinSmall.lean` |
| `pasteOn`, `pasteOn_mem`, `pasteOn_not_mem`, `finsetMapComplEquiv` | `MathlibExt/Data/Finset/PasteSplit.lean` |
| `splitOnEquiv` | Replaced in the normalization proof by the inverse of Mathlib's `Equiv.piEquivPiSubtypeProd`. |
| `finsetMapEquiv` | Replaced at its use site by Mathlib's `Finset.equivMap`. |
| `sum_stdAddChar_dot`, `sum_stdAddChar_affine`, `stdAddChar_mul_star`, `norm_stdAddChar` | `MathlibExt/Analysis/Fourier/ZModAddCharSum.lean` |
| `sum_four_comm`, `sum_separable`, `sum_product_separable` | `MathlibExt/Algebra/BigOperators/SeparableSum.lean` |

## Statement faithfulness

Each main statement was compared with its source in
[google-deepmind/formal-conjectures at `d8d031d4998c78575159ccab9a7a9e95ce043883`](https://github.com/google-deepmind/formal-conjectures/tree/d8d031d4998c78575159ccab9a7a9e95ce043883).
Seven are moved verbatim; the test modules write out each source statement and
prove it using the corresponding declaration.

For OEIS A022030, the existing `MathlibExt.NumberTheory.OeisA022030Wanted.a`
uses the same initial values and recursive equations as the standalone
`OeisA22030.a`. Its `conjecture_holds` proves the same recurrence with
natural-number subtraction for every `n ≥ 4`. The canonical test module
checks that statement and the original initial-term examples. The
[standalone proof](https://github.com/facebookresearch/atlas-lean/blob/c658bb723bf1aee258ccbfe8487c6c5764397432/Atlas/FC/OeisA22030_conjecture.lean)
remains in the repository history; the root build does not register a second
sequence, proof, or roadmap entry.

The statement that differs from its upstream source is `Green25.green_25.upper`.
Upstream states it as a value
question with an opaque `green_25.upper.answer : ℕ → ℕ` left as `sorry`, so the
upstream form cannot be proved without choosing the witness, and at
`d8d031d4998c78575159ccab9a7a9e95ce043883` it is still
`@[category research open, question value, AMS 5 11]`. **Nothing here proves
that upstream statement**: the migrated statement is a different one, inherited
from the Atlas development, which quantifies the witness existentially and
strengthens the last conjunct from `¬ ∀ᶠ N, Property25 ..` to
`∀ᶠ N, ¬ Property25 ..`; the test file derives the upstream (weaker) conjunct
from it. That the least failing admissible `k` (`1 ≤ k ≤ N`) is `o(N / log N)`, below
the `N / log N` scale of the historical [ESS89] upper bound, is recorded upstream for
the explicit witness `k N = ⌈N ^ (23/40)⌉` by
the separate theorem `green_25.variants.upper_pow_23_40`, which *is*
`research solved` there; that is a different declaration from the value question
`green_25.upper`.

All nine statements carried the Formal Conjectures category `research open` at
the revision these developments were written against. At
`d8d031d4998c78575159ccab9a7a9e95ce043883` the upstream categories are:

- `research solved` for the eight results with the upstream statement
  (seven moves and the existing A022030 formalization):
  `erdos_138.variants.dvd_two_pow`, `erdos_337.variants.ruzsa_turjanyi`,
  `count_words_in_x_is_a_shifted`, `supercongruence`, `OeisA22030.conjecture`,
  `conjecture100`, `conjecture314`, and `ame_9_10_open`. Four of them
  (`erdos_138.variants.dvd_two_pow`, `count_words_in_x_is_a_shifted`,
  `supercongruence`, `ame_9_10_open`) cite Lean proofs derived from these Atlas
  proofs; the rest cite independent proofs.
- still `research open, question value` for `green_25.upper`, the value question
  with the opaque answer, which is not the statement proved here. Its solved
  counterpart upstream is the separate `green_25.variants.upper_pow_23_40`.

Nothing here relies on the upstream status either way, because each statement is
proved in this repository from Lean's standard axioms only; the categories are
recorded so that a reviewer can see what each statement is and is not.
