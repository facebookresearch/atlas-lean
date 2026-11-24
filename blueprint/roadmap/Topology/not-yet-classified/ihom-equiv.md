# SSet Ihom Zero

Zero-simplex equivalence for simplicial internal hom.

Forward: `s ↦ rightUnitor.inv ≫ uncurry (yonedaEquiv.symm s)`.
Backward: `f ↦ yonedaEquiv (curry (rightUnitor.hom ≫ f))`.
