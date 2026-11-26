# Cotangent derived object as a localization image

Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and assume
`HasDerivedCategory.{w} (ModuleCat.{max u v} A)`. Then `cotangentDerived k A =
DerivedCategory.Q.obj (cotangentCochainComplex k A)`: the derived object is the localization
image of the integer cochain representative.
