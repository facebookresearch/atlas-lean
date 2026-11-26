# Composition with an edge constant over the base

For a simplicial fibration `p : X ⟶ Y` in universe `u`, suppose `x₀₁, x₁₂ : Δ[1] ⟶ X` satisfy
`δ 0 ≫ x₀₁ = δ 1 ≫ x₁₂`, and `x₀₁ ≫ p = const b` for `b : Y _⦋0⦌`. Then there is `x₀₂ : Δ[1] ⟶
X` with `δ 1 ≫ x₀₂ = δ 1 ≫ x₀₁`, `δ 0 ≫ x₀₂ = δ 0 ≫ x₁₂`, and `x₀₂ ≫ p = x₁₂ ≫ p`. Here `δ`
denotes `stdSimplex.δ`.
