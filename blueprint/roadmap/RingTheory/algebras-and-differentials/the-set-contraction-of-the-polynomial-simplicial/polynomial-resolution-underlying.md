# Underlying augmented simplicial set of the polynomial resolution

For a commutative ring `k : Type u` and `A : CommAlgCat.{max u v} k`,
`polynomialResolutionUnderlying k A` is the augmented simplicial object in `Type(max u v)`
obtained by applying the forgetful functor to `polynomialResolution k A`. Its augmentation
point is the carrier of `A`.
