# Homology functor of the weight-zero coefficient tensor complex

For a commutative ring `k : Type u`, `A : CommAlgCat.{max u v} k`, a simplicial algebra `P`
augmented to `A`, and `n : ℕ`, the functor `cotangentWeightZeroTensorHomologyFunctor k A P n :
ModuleCat.{t} A → ModuleCat.{max u v t} A` takes degree-`n` homology of the normalized tensor
complex `M ⊗_A (A ⊗_{P_i} P_i)`.
