# Relational specifications

This guide fixes the contribution template for the SPECS workstream. Reuse an
existing relation and its implementation; do not add a renamed predicate to
increase the specification count. The inventory below locates existing APIs
and clients. It does not certify their tests or complete the 15-spec target.

## Contribution template

A specification entry contains these six fields:

1. **Relation and scope.** Name the canonical declaration, input and output
   types, universes, hypotheses, and observable result. State whether failure,
   multiplicity, ordering, and unconsumed input are observable. Separate
   functional correctness from cost, stability, termination, and conformance.
2. **Implementation and client.** Name the actual function and a client that
   consumes its result. Use the public API, not a second implementation or an
   oracle that simply calls the function under test again.
3. **Executable checks.** Retain `#eval` checks with asserted expected output,
   or an equivalent failing assertion harness. Printing a value is not a test.
   Use Plausible for decidable fixture properties with available generators;
   record the seed, generator bounds, case count, and replay of any minimized
   counterexample. Decidability alone does not supply a useful generator.
4. **Positive and negative witnesses.** Include a nontrivial valid instance,
   boundary cases, and an input/output pair that violates the relation or an
   input the interface must reject. An unsorted input is not a counterexample
   to a theorem that assumes sortedness. A rejected parser input is not an
   exception to its round-trip theorem.
5. **Discrimination and proof evidence.** Run the unchanged checks against a
   seeded, type-correct wrong implementation or result. Record which assertion
   fails, with a successful baseline on the same input. A mutant that fails to
   compile is a compiler control, not evidence that a runtime check caught it.
   Keep mutation fixtures private; do not weaken production theorems or add
   proof holes. Record source hashes, command outputs, kernel/trust checks,
   reviews, and the exact CI head separately from randomized test results.
6. **README coverage row.** Link the relation, implementation, consuming
   client, executable checks, witnesses, and evidence from the relevant README.
   Give the assurance level and the evidence supporting it, or mark it
   unassessed. Keep source inspection, successful execution, and proof review
   distinct. Do not promote a row merely because its definition was located.

Concrete executable fixtures may need stronger instances than the public
relation. They must not silently narrow that relation's type or hypotheses.
For an abstract interface, choose and name a concrete executable instance;
there need not be a representation-independent notion of malformed input.

## Canonical interfaces

- **Sortedness and permutation:** use `List.Pairwise (· ≤ ·)` and `List.Perm`.
  The [`SortedProp` and `SortingSpec`][sorting] entry points in the
  sorting PR retain `{α : Type u} [LE α]`. `SortingSpec xs ys` is
  `List.Perm ys xs ∧ SortedProp ys`, including duplicate occurrences. It
  assumes no decidability, linear-order laws, stability, or cost model.
- **Do not narrow the sorting relation:** pinned CSLib's
  [`IsSorted`][cslib-sort] unfolds to the same pairwise predicate, but its
  surrounding variables are
  `{α : Type} [LinearOrder α]`. It is not a replacement for the more general
  entry point. Algorithm correctness may still require a linear order, as the
  existing [insertion][insertion] and [selection][selection] bridges do.
- **Maps:** reuse core [`Std.HashMap.getElem?_insert`][map-insert] and
  [`Std.HashMap.getElem?_erase`][map-erase]. Their branch test is `k == a`,
  with `BEq`, `Hashable`, `EquivBEq`, and `LawfulHashable` assumptions. Do not
  silently replace Boolean key equivalence with propositional equality.
- **Other interfaces:** use the declarations in the inventory directly. A
  module under `CSLibExt/Specs` is justified by a reusable connection between
  existing APIs, not by restating a theorem under a new name. Keep tests in
  `CSLibExtTest` or `MathlibExtTest`, following the production API's library.

## Coverage inventory

This is a nine-row starting inventory, not nine accepted specifications.
**Source-only** means the named source was inspected; this memo awards no L2
assurance, runtime pass, mutation-test pass, or new formal proof. Consumer
coverage marked *not inventoried* is a gap in this memo, not a claim that no
consumer exists. In particular, different implementations of the same
language predicate must not share runtime credit.

| Contract and source | Relation and important scope | Used by / client location | Assurance in this memo |
| --- | --- | --- | --- |
| [`CSLibExt.Specs.Sorting.SortingSpec`][sorting] | Output is a permutation of the input and pairwise nondecreasing; arbitrary `Type u` with `LE`. | [Canonical insertion bridge][insertion] and [selection bridge][selection], both with their algorithm's stronger order assumptions. Available at the pinned sorting PR head, not the pinned main snapshot. | Source-only |
| [`Cslib.Algorithms.Lean.TimeM.lowerBound_spec`][lower-bound] | Requires `LinearOrder`. On a sorted array, the returned index is at most the size, all earlier values are below the key, and all later values are at least the key. The law concerns `.ret`; `.time` counts key comparisons and is separate cost evidence, not machine time. | [LowerBoundTests][lower-client], including empty arrays, duplicates, and a `Nat` restatement of `lowerBound_spec`. | Source-only |
| [`MinHeap.extractMin_mem`][heap-member], [`MinHeap.extractMin_le`][heap-min], and [`MinHeap.extractMin_elements`][heap-elements] in `Cslib.Algorithms.Lean` | A successful extraction returns a **stored** minimum and erases exactly one occurrence from the multiset. Membership plus erasure establishes the one-occurrence claim. Requires `LinearOrder`; [failure iff empty][heap-empty] is another branch of the same operation. | [BinaryHeapTests][heap-client], including empty, singleton, and duplicate minima. | Source-only |
| [`Cslib.Language.cykAccepts_iff`][cyk] | Boolean acceptance iff language membership under `IsChomskyNormalForm` and decidable terminal/nonterminal equality. Empty-word acceptance checks an initial epsilon production. | [ContextFreeCYKTests][cyk-client]: `anbn` and `epsAB` give both rejection and acceptance of the empty word under different valid grammars. | Source-only |
| [`RegularExpression.rmatch_iff_matches'`][regex] | The Boolean derivative matcher agrees with the denoted language, with decidable alphabet equality. | Direct matcher witnesses are planned. [Existing encoded-regex tests][regex-client] exercise a CFG decider, not this matcher. | Source-only |
| [`Cslib.CookLevin.decodeCNF_eq_some_iff`][cnf] | Full decoding returns `some φ` iff the entire input equals `encodeCNF φ`; malformed or trailing bits are rejected. This is stronger than the [round trip alone][cnf-roundtrip]. | [CookLevinTests][cnf-client], with empty/nonempty formulas and missing/trailing-bit cases. | Source-only |
| [`MetaMathlibExt.BitstringEncoding.bitDecode_bitEncode`][bit-codec] | A left-inverse law for the chosen encoding instance. It does not by itself specify which other bitstrings are rejected. | Concrete-instance consumer coverage not inventoried here. | Source-only |
| [`Std.HashMap.getElem?_insert`][map-insert] | Lookup after insertion returns the new value for an equivalent key and preserves other lookups. | Atlas consumer coverage not inventoried here. | Source-only |
| [`Std.HashMap.getElem?_erase`][map-erase] | Lookup after erasure is absent for an equivalent key and preserves other lookups. | Atlas consumer coverage not inventoried here. | Source-only |

## Worked entry: heap extraction

- **Relation:** combine [stored membership][heap-member], the
  [minimum law][heap-min], [erasure][heap-elements], and
  [failure iff empty][heap-empty]. Membership plus erasure gives exactly one
  removed occurrence. Heap order is carried by `MinHeap`; multiplicity is not
  set membership.
- **Implementation/client:** `MinHeap.extractMin`, projected to the returned
  value and backing array by `BinaryHeapTests.extractedData`. The existing
  [client source][heap-client] builds a heap by pushing `3, 1, 1, 2`; its
  stated extraction result is `some (1, #[1, 2, 3])`.
- **Positive and boundary witnesses:** that duplicate-minimum example,
  extraction from a singleton, and `none` from the empty heap are present as
  propositions in the source. Their location is not a new execution receipt.
- **Negative witnesses to add:** on that nonempty heap, `none` violates the
  failure-if-and-only-if-empty contract. Returning `some (0, unchangedHeap)`
  satisfies the minimum and erasure conditions, since `0` is a lower bound
  and erasing a nonmember changes nothing; the membership law rejects it.
  Returning `1` with no `1` in the remainder instead violates the erasure law.
- **Executable/Plausible obligation:** run the public operation on these
  fixtures and bounded generated lists of naturals. Assert the result and
  multiplicities, using independently computed input counts. Preserve the
  seed and ensure nonempty and duplicate cases were actually generated.
- **Discrimination obligation:** an always-`none` mutant and a mutant returning
  `(0, unchangedHeap)` must both reach and fail the unchanged assertions. The
  first tests the empty-case law; the second tests membership, which the
  minimum-plus-erasure fragment misses. Also test dropping both copies of the
  actual minimum to discriminate the multiplicity law. A production-proof
  compilation failure is recorded separately.
- **README/evidence:** the inventory row is the starting entry. Add links to
  the retained checks and their evidence before awarding executable assurance.
  This document-only change does not run those checks or promote that row.

## Next witness unit and remaining scope

The next bounded unit targets heap extraction, CYK, direct `rmatch`, and full
CNF decoding. Reuse their existing tests rather than replacing the algorithms.
For CYK, preserve the normal-form hypothesis and cover `epsAB`'s epsilon case;
for regex, test the actual derivative matcher; for CNF, distinguish a valid
empty formula from empty or trailing-bit input. Each operation needs positive
and negative executable witnesses, applicable Plausible checks, a discriminating
seeded mutation, and a README row. That unit is not implemented by this memo.

The full program still requires at least 15 qualified specs, a semantic audit
of competing sortedness/permutation/map definitions, the LOGICS client and
at least 10 SWV tasks, and a CSLib pilot batch. Graph, set/multiset, protocol,
parser-unambiguity, and stability coverage remain separate work. A name search
is only a duplicate candidate finder; it cannot certify the absence of
competing semantics. Human expert review and external coordination remain
separate from this contribution template.

## Source snapshots

Locators below point to declaration lines or the named client section, not to
moving branches. The sorting contract is taken from PR #903 at
`e226c7cb8f75b7bcb5f37de8b09ea4de447f13f7`; those files are not present at the
main snapshot used here. Main sources use
`d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4`. Pinned upstreams are Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, CSLib
`5b56df99362532c46e1175381fbbdd755bd56030`, and Lean 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

[sorting]: https://github.com/facebookresearch/atlas-lean/blob/e226c7cb8f75b7bcb5f37de8b09ea4de447f13f7/CSLibExt/Specs/Sorting.lean#L26-L37
[insertion]: https://github.com/facebookresearch/atlas-lean/blob/e226c7cb8f75b7bcb5f37de8b09ea4de447f13f7/CSLibExt/Specs/InsertionSort.lean#L36-L54
[selection]: https://github.com/facebookresearch/atlas-lean/blob/e226c7cb8f75b7bcb5f37de8b09ea4de447f13f7/CSLibExt/Specs/SelectionSort.lean#L28-L31
[cslib-sort]: https://github.com/leanprover/cslib/blob/5b56df99362532c46e1175381fbbdd755bd56030/Cslib/Algorithms/Lean/MergeSort/MergeSort.lean#L36-L73
[lower-bound]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExt/Algorithms/Lean/Search/LowerBound.lean#L130-L137
[lower-client]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExtTest/Algorithms/Lean/Search/LowerBoundTests.lean#L24-L96
[heap-member]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExt/Algorithms/Lean/DataStructures/BinaryHeap.lean#L760-L769
[heap-min]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExt/Algorithms/Lean/DataStructures/BinaryHeap.lean#L771-L782
[heap-elements]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExt/Algorithms/Lean/DataStructures/BinaryHeap.lean#L784-L793
[heap-empty]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExt/Algorithms/Lean/DataStructures/BinaryHeap.lean#L755-L757
[heap-client]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExtTest/Algorithms/Lean/DataStructures/BinaryHeapTests.lean#L48-L88
[cyk]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExt/Computability/Languages/ContextFree/CYK.lean#L379-L405
[cyk-client]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExtTest/Computability/Languages/ContextFreeCYKTests.lean#L28-L72
[regex]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/RegularExpressions.lean#L299-L320
[regex-client]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExtTest/Computability/Decidability/RegularExpressionTests.lean#L48-L53
[cnf]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExt/Computability/CookLevin.lean#L337-L353
[cnf-roundtrip]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExt/Computability/CookLevin.lean#L193-L197
[cnf-client]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/CSLibExtTest/Computability/CookLevinTests.lean#L50-L78
[bit-codec]: https://github.com/facebookresearch/atlas-lean/blob/d8af6fb34cfc6ef3f22e3c2157dda8abb8b47ac4/MathlibExt/Computability/Complexity.lean#L48-L64
[map-insert]: https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/Data/HashMap/Lemmas.lean#L264-L271
[map-erase]: https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/Data/HashMap/Lemmas.lean#L312-L318
