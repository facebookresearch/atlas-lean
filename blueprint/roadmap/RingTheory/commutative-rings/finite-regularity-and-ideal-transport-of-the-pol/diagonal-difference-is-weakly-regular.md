# Distinct diagonal differences are weakly regular

Let `k` be a commutative ring and `σ` a type. Put `A = MvPolynomial σ k`, `E = A ⊗[k] Aᵐᵒᵖ`,
and `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)`. For `n : ℕ` and an injective function `f : Fin n → σ`,
the sequence `List.ofFn (fun i ↦ δ_(f i))` is weakly regular in `E`. Multiplication by each
next diagonal difference is injective on the quotient by the earlier differences.
