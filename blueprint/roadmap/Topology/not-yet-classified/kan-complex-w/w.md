# W

Weak equivalences between Kan complexes for the Kan–Quillen model structure.

A morphism `f : X ⟶ Y` lies in `W` when `X` and `Y` are Kan complexes,
the induced functor `SSet.mapFundamentalGroupoid f` is an equivalence of
groupoids, and every based homotopy-group map
`KanComplex.π.map f rfl n : π n X x → π n Y (f.app _ x)` is bijective.
This is the structural predicate used by the identity, composition,
cancellation, and retract results; the precomposition proof uses the
fundamental-groupoid action to transport homotopy-group bijectivity from
image points to arbitrary basepoints.
