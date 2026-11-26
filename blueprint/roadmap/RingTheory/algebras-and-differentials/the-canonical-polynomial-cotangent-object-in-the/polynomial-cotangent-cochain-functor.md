# Polynomial cotangent model in integer cochain degrees

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The functor
`polynomialCotangentCochainFunctor k A : Over A → CochainComplex (ModuleCat A) ℤ` extends each
normalized polynomial cotangent chain model along `ComplexShape.embeddingDownNat`, whose index
map is `n ↦ -n`. Positive cochain degrees are zero, and morphisms are the extensions of the
polynomial cotangent chain maps.
