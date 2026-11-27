# A chosen finite lift of a polynomial difference

Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. For each `p : A`, choose a finitely
supported vector `w_p : V` satisfying `F(w_p) = p ⊗ op(1) - 1 ⊗ op(p)`. The function
`diagonalCotangentLift k σ` returns this chosen preimage.
