# Cohomology comparison between an injective domain and range

Let `k` be a commutative ring, `f : H →* G` injective, `A : Rep k G`, and `n : ℕ`. The
isomorphism `injectiveRangeCohomologyIso f hf A n : H^n(H,f^*A) ≅ H^n(f.range,Res A)` is
induced by `e=MonoidHom.ofInjective hf : H ≃* f.range` and the identity linear coefficient
equivalence. Its forward morphism is `map e.symm (injectiveRangeResIso f hf A).hom n`.
