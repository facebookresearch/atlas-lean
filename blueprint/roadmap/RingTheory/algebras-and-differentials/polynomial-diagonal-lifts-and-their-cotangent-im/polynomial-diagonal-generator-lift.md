# A lift of an image polynomial generator

Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, choose `L_i : τ →₀ E_τ` with `F_τ(L_i) = Δ(g(X_i))`, where `F_τ(w)
= ∑ j, w_j δ_j`. This chosen target diagonal vector is `polynomialDiagonalGeneratorLift k τ g
i`.
