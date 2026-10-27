---
kind: source
status: adopted
---

# MIT 18.785 Number Theory I (Fall 2021)

Stable public record: <https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/>.

ATLAS v1 selected 576 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

1500 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/NumberTheoryI.json`](book-dependencies/NumberTheoryI.json).

3 candidate dependencies are not drawn because adding
them would create a cycle between source statements. Every other verified
dependency is retained, including relations in both directions between chapters.

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Definition 1.10 | `DiscreteValuation` |
| Corollary 3.17 (Finite approximation) | `Ideal.exists_elem_eq_valuation_at_primes` |
| Definition 4.17 | `mem_separableClosure_iff_isSeparable` |
| Definition 4.22 | `EtaleAlgebras.isPurelyInseparable_iff_finSepDegree` |
| Definition 6.5 | `idealNorm` |
| Definition 6.16 | `Subalgebra.conductorIdeal` |
| Definition 6.19 | `IsOrder` |
| Definition 7.16 | `frobeniusElement` |
| Definition 12.9 | `latticeDiscriminant` |
| Lemma 12.10 | `latticeDiscriminant_eq_imp_eq` |
| Proposition 12.11 | `latticeDiscriminant_isFractional_and_ne_bot` |
| Definition 12.12 | `extensionDiscriminant` |
| Definition 13.1 | `Place` |
| Definition 16.18 | `ConvergesLocallyNormallyOn` |
| Theorem 16.27 (Liouville's theorem) | `liouville_theorem` |
| Definition 23.38 | `TateCohomology.herbrandQuotient` |
