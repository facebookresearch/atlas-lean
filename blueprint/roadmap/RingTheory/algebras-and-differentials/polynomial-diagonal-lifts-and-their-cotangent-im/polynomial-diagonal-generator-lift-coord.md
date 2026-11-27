# The lifted generator has the differential image

Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, cotangent reduction of `polynomialDiagonalGeneratorLift k τ g i` is
`D k (k[τ]) (g(X_i))`. Its coordinate at a target variable `j : τ` is `∂g(X_i)/∂X_j`.
