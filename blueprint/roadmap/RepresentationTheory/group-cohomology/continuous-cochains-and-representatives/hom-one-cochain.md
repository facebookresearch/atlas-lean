# Hom One Cochain

Homogeneous degree-one cochain from an inhomogeneous cocycle.

Given `c` with `c (g * h) = X.ρ g (c h) + c g` and continuity of the uncurried
`Ψ`, this packages `Ψ x y = X.ρ x (c (x⁻¹ * y))` as an invariant element of
`TopRep.homogeneousCochains`. Reuses `TopRep.homogeneousCochains` and
`ContRepresentation.coind₁_apply_apply` for the invariance computation.
