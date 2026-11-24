# Ho Pre Equivalence Edge Lifting

The equivalence-edge lifting property for precomposition with
`i : A ⟶ B` into `C`: every equivalence edge `e` of `(ihom A).obj C`
whose source is the restriction of a vertex `b` of `(ihom B).obj C`
lifts to an equivalence edge `e'` of `(ihom B).obj C` out of `b` whose
target restricts on the nose to the target of `e` and whose image in
the homotopy category of `(ihom A).obj C` is the morphism represented
by `e`. By `SSet.hoFunctor_pre_isIsofibration_iff`, for `C` a
quasicategory this is equivalent to precomposition with `i` inducing
an isofibration on homotopy categories.
