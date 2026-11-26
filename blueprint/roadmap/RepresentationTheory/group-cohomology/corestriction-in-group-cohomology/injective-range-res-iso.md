# Coefficient comparison between an injective domain and range

Let `k` be a commutative ring, `f : H →* G` an injective group homomorphism, and `A : Rep k
G`. Put `e=MonoidHom.ofInjective hf : H ≃* f.range` and `i=f.range.subtype`. The isomorphism
`injectiveRangeResIso f hf A : (e⁻¹)^*(f^*A) ≅ i^*A` has underlying linear map the identity on
`A`, since `f(e⁻¹(g)) = g` for `g ∈ f.range`.
