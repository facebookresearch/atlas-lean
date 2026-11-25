# Relative Chain Complex Functor obj obj

For fixed coefficients `R : C` and a simplicial pair `X`, the value is
definitionally the cokernel of the unnormalized chain map induced by `X.hom`,
i.e. `cokernel ((SSet.chainComplexFunctor C).obj R).map X.hom`.
