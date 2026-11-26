# Normalized weight-zero coefficient tensor functor

For a commutative ring `k : Type u`, `A : CommAlgCat.{max u v} k`, and a simplicial algebra
`P` augmented to constant `A`, `cotangentWeightZeroTensorComplexFunctor k A P` sends `M :
ModuleCat.{t} A` to the normalized Moore complex of the degreewise tensors `M ⊗_A (A ⊗_{P_i}
P_i)`. Its target is `ChainComplex (ModuleCat.{max u v t} A) ℕ`.
