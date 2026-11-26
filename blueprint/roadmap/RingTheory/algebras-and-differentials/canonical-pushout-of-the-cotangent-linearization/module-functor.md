# Coefficient extension to the pushed-out algebra

Let `k : Type u`, `K : Type w` be commutative rings with `Algebra k K`, `A : CommAlgCat.{max u
v w} k`, and `B=K ⊗_k A`. The coefficient functor `moduleFunctor k K A : ModuleCat A →
ModuleCat B` at carrier height `max u v w` is extension along `algebraMap A B`, sending `L` to
`B ⊗_A L`.
