# Degree-one cup pairing in two-variable coordinates

Let `A,B` be representations of a group `G` over a commutative ring `k`, and let `x : G → A`,
`y : G → B` be arbitrary functions. Convert them to degree-one cochains with
`cochainsIso₁.inv`, apply `inhomogeneousCupPairing` in degrees `(1,1)`, and convert the result
by `cochainsIso₂.hom`. The resulting function equals `cupCochainOneOne A B x y`, namely `(g,h)
↦ x(g) ⊗ₜ[k] g·y(h)`.
