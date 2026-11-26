# Integer cochain model of the cotangent complex

For a commutative ring `k : Type u` and `A : CommAlgCat.{max u v} k`, `cotangentCochainComplex
k A` is the value of `polynomialCotangentCochainFunctor k A` at `Over.mk (𝟙 A)`. It is the
normalized polynomial cotangent chain complex of `A/k` placed in cochain degree `-n` for chain
degree `n`.
