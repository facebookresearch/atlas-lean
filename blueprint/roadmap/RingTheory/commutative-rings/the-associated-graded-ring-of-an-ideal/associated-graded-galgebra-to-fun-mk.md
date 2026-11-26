# Coefficients enter the degree-zero component

For an ideal `I` in a commutative ring `R` and `r : R`, `(associatedGradedGAlgebra I).toFun
(Ideal.Quotient.mk I r)` is the degree-zero class `[r]_0` in `I.AssociatedGradedPiece 0`.
Equivalently, it is `initialForm I 0 x`, where `x : I^0` has underlying value `r`.
