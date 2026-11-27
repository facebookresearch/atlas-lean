# Cotangent reduction factors through the functional

Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k` and `E = A ⊗[k]
Aᵐᵒᵖ`. Write `µ : E → A` for diagonal multiplication, `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`, `F(w)
= ∑ i, w_i δ_i` on `V = σ →₀ E`, and `Ω = Ω¹(A/k)`. The cotangent coordinate map equals the
composite `C = θ ∘ F`, where `θ(a ⊗ op(b)) = -a db`. In code, `diagonalCotangentCoordinates k
σ = (envelopingCotangentLinear k σ).comp (F.restrictScalars k)`.
