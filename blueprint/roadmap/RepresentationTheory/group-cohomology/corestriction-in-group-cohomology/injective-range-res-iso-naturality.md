# Coefficient naturality of the domain-range comparison

Let `k` be a commutative ring, `f : H →* G` injective, and `φ : A → B` a morphism of
representations. Put `e=MonoidHom.ofInjective hf`, `i=f.range.subtype`, and
`Γ_A=(injectiveRangeResIso f hf A).hom`. The coefficient morphisms satisfy `Γ_A ≫ i^*(φ) =
(e⁻¹)^*(f^*(φ)) ≫ Γ_B`, from `(e⁻¹)^*(f^*A)` to `i^*B`.
