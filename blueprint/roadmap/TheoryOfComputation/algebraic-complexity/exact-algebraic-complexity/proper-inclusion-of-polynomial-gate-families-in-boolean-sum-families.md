# Proper inclusion for polynomial gate-list families

Over every field $F$, the exact gate-list class $\mathrm{VP}(F)$ is a **proper subset** of the Boolean-sum class $\mathrm{VNP}(F)$ of the stated polynomial families. This asserts both inclusion and that at least one $\mathrm{VNP}(F)$ family lies outside $\mathrm{VP}(F)$. It uses the explicit degree bound, and does not impose multiplicative disjointness on the witness circuit.

## Depends on

- [Gate-list circuits and polynomial families](gate-lists-for-polynomial-families.md)

## Proof depends on

- [Exact gate bounds](hamiltonian-cycle-and-permanent-exact-gate-bound.md)

## Proof outline

Isolate the inclusion and the polynomial-family witness for strictness. Identify this model with another formulation of Valiant’s classes only after proving the polynomial-size and variable-renaming bridges.

## Related formulations

See the [overview of Valiant’s classes](../valiant-s-vp-versus-vnp-conjecture.md) for the formulation using multiplicatively disjoint circuits. A [fixed-variable arithmetic-gate formulation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VPVNP.lean) instead allows subtraction, treats inputs as free, and uses $2n$ indeterminates at index $n$. Identifying its separation with this one requires size-preserving-up-to-polynomial translations, reindexing and padding the variable sets, and translating inequality of predicates to proper inclusion. The formula and branching-program inclusions of an arithmetic hierarchy, and noncontainment in the Laurent-series closure, are separate statements.

## Sources

- Anthropic, [Solution.separation](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Challenge.lean#L23-L24).
- [The gate-list class separation](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L64-L93).
