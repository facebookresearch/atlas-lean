# Composition of edges above a two-simplex

Let `p : X ⟶ Y` be a simplicial fibration in universe `u`. Suppose edges `x₀₁, x₁₂ : Δ[1] ⟶ X`
satisfy `δ 0 ≫ x₀₁ = δ 1 ≫ x₁₂`, and `s : Δ[2] ⟶ Y` satisfies `δ 2 ≫ s = x₀₁ ≫ p` and `δ 0 ≫ s
= x₁₂ ≫ p`, where `δ` denotes `stdSimplex.δ`. There is `x₀₂ : Δ[1] ⟶ X` with `δ 1 ≫ x₀₂ = δ 1
≫ x₀₁`, `δ 0 ≫ x₀₂ = δ 0 ≫ x₁₂`, and `x₀₂ ≫ p = δ 1 ≫ s`.
