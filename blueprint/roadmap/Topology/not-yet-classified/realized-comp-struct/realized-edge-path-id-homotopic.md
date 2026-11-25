# Realized Edge Path id homotopic

Degenerate realized edge path is null-homotopic (universe-polymorphic).

For `x : X _⦋0⦌` in `SSet.{u}`, the realized identity edge path is endpoint-fixed
homotopic to the constant path at the realized vertex. Orientation matches
`SSet.realizedEdgePath` (`δ 1` source at `0 : TopCat.I`, `δ 0` target at
`1 : TopCat.I`) and `_root_.Path.trans` (first path on `[0, 1/2]`, second on
`[1/2, 1]`); both sides are `_root_.Path (realizedVertex x) (realizedVertex x)`.

Proof factors the identity edge through `Δ[0]` via `SSet.Edge.id_edge` and
`SSet.stdSimplex.σ_comp_yonedaEquiv_symm`, shows the realized path equals
`Path.refl` by `Path.ext` with the subsingleton `|Δ[0]|` domain, and concludes
by reflexive homotopy.
No K-theory-specific assumption.

Nonclaims: no general realization-of-simplicial-homotopy,
no additivity or `π₀` claim.
