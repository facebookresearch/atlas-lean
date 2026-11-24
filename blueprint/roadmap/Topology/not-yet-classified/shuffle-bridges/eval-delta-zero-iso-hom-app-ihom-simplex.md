# Evaluation at `Δ(0)` on a prism simplex is the vertical value

**Evaluation at `Δ[0]` on a prism simplex is the vertical
value.** For `F₀ : Δ[0] ⊗ Δ[1] ⟶ C`, evaluating
`ihomSimplexOfPrism F₀` at `Δ[0]` gives `F₀` at the vertical
simplex over the unique vertex. After Yoneda both sides are
`(λ_ Δ[1]).inv ≫ (Δ0IsoUnit.inv ▷ Δ[1]) ≫ F₀`, by
`evalDeltaZeroIso_hom`, `curry_pre_app` and
`curry_unitIsoSelf` on one side and the classifying-map
computation on the other.
