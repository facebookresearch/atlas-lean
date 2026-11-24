# Chain Complex Functor map app PInfty

The component at a simplicial set `X` of the natural transformation
`(SSet.chainComplexFunctor C).map f` for a coefficient morphism `f : R ⟶ S`
commutes with the two instances of `P∞`.

For each `X : SSet`, let `F := Limits.sigmaConst ⋙ SimplicialObject.whiskering`
be the coefficient-to-simplicial-object functor, so that
`(SSet.chainComplexFunctor C).map f` at `X` is
`alternatingFaceMapComplex C`-applied to `(F.map f).app X`.
Then naturality of `AlgebraicTopology.DoldKan.natTransPInfty C` at the simplicial
map `(F.map f).app X` gives
`map f ≫ P∞ = P∞ ≫ map f`, where the left `P∞` is on `X.chainComplex S` and the
right `P∞` is on `X.chainComplex R`.
