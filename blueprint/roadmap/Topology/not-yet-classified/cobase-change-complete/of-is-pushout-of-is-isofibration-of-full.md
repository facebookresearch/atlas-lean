# Cobase change of a categorical equivalence along a monomorphism, granted (A) and (B)

**Cobase change of a categorical equivalence along a
monomorphism, granted (A) and (B).** If precomposition with `i`
induces an isofibration on homotopy categories of functor objects
into every quasicategory (TODO(T26-A) for `i`) and precomposition
with the cobase change `f'` is full and faithful on those homotopy
categories (TODO(T26-B) for this square), then `f'` is a
categorical equivalence: essential surjectivity is
`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`. (T30-A)
is now proved (`DwyerKanFinal.lean`); once (T30-B) of the module
header is proved, this theorem with those inputs is the statement
`(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
(MorphismProperty.monomorphisms SSet.{u})` with no further formal
steps.
