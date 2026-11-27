# Homotopy Rel

A homotopy relative to a subcomplex `S ≤ X`, stationary on `S`.

For `f g : X ⟶ Y`, a witness `H : HomotopyRel f g S` consists of
`h : X ⊗ Δ[1] ⟶ Y` with `ι₀ ≫ h = f`, `ι₁ ≫ h = g`,
and `h` constant on `S` in the interval direction:
`∀ x ∈ S, ∀ t : Δ[1], h (x, t) = f x`.

This reuses `SSet.Homotopy` (`RelativeMorphism.Homotopy` with `⊥`)
but adds the relative stationarity condition, modelling
`TopCat`'s `ContinuousMap.HomotopyRel` with interval `Δ[1]`.
