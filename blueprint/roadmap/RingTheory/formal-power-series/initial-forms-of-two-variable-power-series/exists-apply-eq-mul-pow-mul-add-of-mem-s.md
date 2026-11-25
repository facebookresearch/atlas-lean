# Evaluating a power series through its initial form

Let `W` be a commutative ring, `M` a commutative local ring with maximal
ideal `𝔪`, `Φ : W⟦X₀, X₁⟧ → M` a ring homomorphism, and `ρ : W → M` a ring
homomorphism with `Φ (C w) = ρ w` for all `w`. Suppose `Φ X₀ = v α` and `Φ
X₁ = v β` with `v ∈ 𝔪`, `α - ρ p₀ ∈ 𝔪` and `β - ρ p₁ ∈ 𝔪` for some `p₀, p₁ ∈
W`. If `g` lies in the `d`-th power of the ideal `(X₀, X₁)`, then there is
`r ∈ 𝔪` with `Φ g = v ^ d (ρ (initialForm d g p₀ p₁) + r)`.

Here `W` is a commutative ring and the degree-`d` initial form of a
two-variable power series `g` over `W`, evaluated at `(p₀, p₁)`, is `∑ i ≤
d, coeff (i, d - i) g · p₀ ^ i · p₁ ^ (d - i)`.
