# Boolean-sum families outside the Laurent-series closure

For every field $F$, $\mathrm{VNP}(F)$ is **not contained** in $\overline{\mathrm{VP}}(F)$ with the specified Laurent-series approximation; that is, some Boolean-sum family over $F$ does not have polynomially bounded Laurent-series approximating circuits in this model. This is a noncontainment, not an assertion that the closure is a subset of $\mathrm{VNP}$.

## Depends on

- [Gate-list circuits, Laurent approximation and families](../exact-algebraic-complexity/gate-lists-for-polynomial-families.md)

## Proof depends on

- [Approximate gate bounds](hamiltonian-cycle-and-permanent-laurent-gate-bound.md)

## Proof outline

Specify the witnessing polynomial family and degree and size estimates. A bridge to a closure defined by another approximation model requires proof in the direction needed for the noncontainment.

## Sources

- Anthropic, [Solution.separationClosure](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Challenge.lean#L26-L27).
- [The closure noncontainment](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean#L64-L96).
