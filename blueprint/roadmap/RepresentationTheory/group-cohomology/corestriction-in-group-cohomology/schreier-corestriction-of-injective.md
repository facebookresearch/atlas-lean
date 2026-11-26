# Corestriction along an injective homomorphism

Let `k` be a commutative ring, `f : H →* G` injective with finite-index range, `A : Rep k G`,
and `n : ℕ`. The morphism `schreierCorestrictionOfInjective f hf A n : H^n(H,f^*A) → H^n(G,A)`
is `map e.symm Γ n ≫ schreierCorestriction f.range A n`, where `e=MonoidHom.ofInjective hf : H
≃* f.range` and `Γ=(injectiveRangeResIso f hf A).hom`.
