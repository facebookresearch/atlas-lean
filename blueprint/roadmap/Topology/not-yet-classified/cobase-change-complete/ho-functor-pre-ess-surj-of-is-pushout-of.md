# Essential surjectivity of precomposition with a cobase change, granted the isofibration property of the left leg

**Essential surjectivity of precomposition with a cobase change,
granted the isofibration property of the left leg.** In a pushout
square `IsPushout i f f' j` with `f` a categorical equivalence, if
precomposition with `i` into a quasicategory `C` induces an
isofibration on homotopy categories (the conclusion of
TODO(T26-A) for this `i` and `C`), then precomposition with `f'`
is essentially surjective on homotopy categories of functor objects
into `C`. At a vertex `b` of `(ihom B).obj C`, essential
surjectivity for `f` supplies a vertex of `(ihom X).obj C` and an
isomorphism over `(ihom A).obj C`; the isofibration property
corrects `b` up to isomorphism so that its restriction to
`(ihom A).obj C` agrees on the nose, and the two classifying maps
then glue along the pushout. This discharges TODO(T26-C)(2) of the
`CobaseChange.lean` header, conditionally on (A).
