# Semilinear extension of one generator lift

Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, write `L_i = polynomialDiagonalGeneratorLift k τ g i`. This is the
`F_g`-semilinear map `E_σ →ₛₗ[F_g] (τ →₀ E_τ)` given by `e ↦ F_g(e) • L_i`.
