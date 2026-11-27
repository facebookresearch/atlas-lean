# Reduction of a single diagonal coordinate

Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. For `i : σ` and `e : E`,
`diagonalCotangentCoordinates k σ (Finsupp.single i e) = µ(e) • D k A (X_i)`.
