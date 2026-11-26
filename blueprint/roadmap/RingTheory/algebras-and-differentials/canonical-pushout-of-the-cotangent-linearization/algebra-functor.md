# Tensor pushout functor on commutative algebras

Let `k : Type u`, `K : Type w` be commutative rings with `Algebra k K`. On algebra carriers of
universe `max u v w`, `algebraFunctor k K` sends `P` to `K ⊗[k] P` and a morphism `f` to `id_K
⊗ f`. It is `CommAlgCat.extendScalarsOfAlgebra k K`.
