# TODO(T26-A) follows from prism strict extension

If
equivalence-edge prisms into a quasicategory `C` extend strictly
along `i ▷ Δ[1]` (`SSet.HoPrePrismStrictExtension i C`), then
precomposition with `i` induces an isofibration on homotopy
categories of functor objects into `C`. This is the prism
restatement of `SSet.hoPreEquivalenceEdgeLifting_of_strict_lift`
combined with `SSet.hoFunctor_pre_isIsofibration_iff`; the
extension property itself for a general monomorphism, formerly
TODO(T30-A) of the module header, is now proved by shuffle-derived
prism extension (see `DwyerKanFinal.lean`).
