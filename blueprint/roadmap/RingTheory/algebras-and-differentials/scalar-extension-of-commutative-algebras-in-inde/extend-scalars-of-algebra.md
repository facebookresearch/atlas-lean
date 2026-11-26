# Tensor scalar extension for a structural algebra

Let `R : Type u` and `S : Type v` be commutative rings with `Algebra R S`. The functor
`CommAlgCat.{max u v w} R → CommAlgCat.{max u v w} S` sends `P` to `S ⊗[R] P` and a morphism
`g` to `Algebra.TensorProduct.map (AlgHom.id S S) g.hom`. The left tensor factor supplies the
`S`-algebra action.
