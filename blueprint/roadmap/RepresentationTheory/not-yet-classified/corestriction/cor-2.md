# Corestriction of 2-cochains

For a subgroup `H` of finite index, a representation `A` of
`G` and a transversal `τ` of the left cosets of `H`, the 2-cochain of `G` given by
`cor₂ u (g₁, g₂) = ∑ q : G ⧸ H, ρ (σ q) (u (h₁, h₁⁻¹ * τ.lam ((σ q)⁻¹ * g₁ * g₂)))` for a
2-cochain `u` of `H`, where `h₁ = τ.lam ((σ q)⁻¹ * g₁)` and `ρ` is the action of `G` on `A`.
The second argument of `u` equals `τ.lam ((σ (g₁⁻¹ • q))⁻¹ * g₂)`.
