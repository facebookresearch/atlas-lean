# Trans

Transitivity for relative homotopies over a base.

Given `H₀₁ : HomotopyRelOver p f g A` and `H₁₂ : HomotopyRelOver p g h A`,
the composite `HomotopyRelOver.trans H₀₁ H₁₂` has start `f` and end `h`
(`ι₀` is `f`, `ι₁` is `h`), is stationary at `f` on `A`, and satisfies the
over-base equation `fst _ _ ≫ (f ≫ p)` (i.e. its underlying homotopy
`transHomotopy H₀₁ H₁₂` satisfies
`(transHomotopy H₀₁ H₁₂) ≫ p = fst _ _ ≫ (f ≫ p)`).

The `[Fibration p]` hypothesis is required for this construction via inner-horn
`Λ[2,1]` lifting. This declaration asserts no associativity, unit, or coherence
law for repeated composition.
