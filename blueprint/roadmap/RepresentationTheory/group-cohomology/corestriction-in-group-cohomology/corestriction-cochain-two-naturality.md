# Coefficient naturality of two-cochain transfer

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `φ : A → B` a morphism of
representations, and `T` a right transversal. For every cochain `z : H × H → A`, `φ ∘
corestrictionCochainTwo A T z = corestrictionCochainTwo B T (φ ∘ z)`. The transfer sends
`(g₁,g₂)` to `∑ t∈T, ρ(t⁻¹) z(h_T(t,g₁),h_T(r_T(t,g₁),g₂))`, using `t g=h_T(t,g)r_T(t,g)`.
