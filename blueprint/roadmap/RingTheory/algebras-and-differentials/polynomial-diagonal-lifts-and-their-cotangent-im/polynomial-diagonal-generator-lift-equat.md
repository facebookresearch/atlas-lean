# The generator lift covers the enveloping image

Let `k` be a commutative ring, `σ,τ` types, and `g : k[σ] →ₐ[k] k[τ]` a polynomial algebra
homomorphism. Write `E_σ = k[σ] ⊗[k] k[σ]ᵐᵒᵖ`, `E_τ = k[τ] ⊗[k] k[τ]ᵐᵒᵖ`, and `F_g = g ⊗ g.op
: E_σ → E_τ`. For `i : σ`, the target diagonal functional satisfies
`F_τ(polynomialDiagonalGeneratorLift k τ g i) = F_g(δ_i)`. Here `F_τ(w) = ∑ j, w_j δ_j` and
`δ_i` is the source left-minus-right variable difference.
