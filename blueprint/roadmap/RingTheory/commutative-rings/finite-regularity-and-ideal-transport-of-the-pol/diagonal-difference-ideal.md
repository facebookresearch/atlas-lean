# The ideal of diagonal differences

Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k`, `E = A ⊗[k] Aᵐᵒᵖ`,
and `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`. The ideal `diagonalDifferenceIdeal k σ` is `Ideal.span
(Set.range (fun i ↦ δ_i))` in `E`.
