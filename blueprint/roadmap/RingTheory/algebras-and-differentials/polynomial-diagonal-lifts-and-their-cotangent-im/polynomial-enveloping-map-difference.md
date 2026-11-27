# A diagonal generator maps to the image difference

Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, `F_g(δ_i) = Δ(g(X_i))`, where `δ_i = X_i ⊗ op(1) - 1 ⊗ op(X_i)` and
`Δp = p ⊗ op(1) - 1 ⊗ op(p)` in the appropriate enveloping algebra.
