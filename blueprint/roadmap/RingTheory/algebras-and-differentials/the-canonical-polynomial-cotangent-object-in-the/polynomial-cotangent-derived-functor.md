# Derived polynomial cotangent functor over a fixed algebra

Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and assume
`HasDerivedCategory.{w} (ModuleCat.{max u v} A)`. The functor `Over A → DerivedCategory
(ModuleCat A)` is `polynomialCotangentCochainFunctor k A ⋙ DerivedCategory.Q`. The source
algebra varies over `A`, while the coefficient algebra `A` stays fixed.
