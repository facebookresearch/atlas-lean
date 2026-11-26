# One-two cup pairing in three-variable coordinates

Let `A,B` be representations of a group `G` over a commutative ring `k`, with arbitrary
functions `x : G → A` and `y : G × G → B`. Convert them to cochains with `cochainsIso₁.inv`
and `cochainsIso₂.inv`, apply `inhomogeneousCupPairing` in degrees `(1,2)`, and convert the
output by `cochainsIso₃.hom`. The result equals `cupCochainOneTwo A B x y`, the function
`(g,h,j) ↦ x(g) ⊗ₜ[k] g·y(h,j)`.
