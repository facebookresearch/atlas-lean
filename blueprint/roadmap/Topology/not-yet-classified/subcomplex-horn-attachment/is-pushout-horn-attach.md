# The attaching square of a simplex along a horn is a pushout

**The attaching square of a simplex along a horn is a
pushout**, when the classifying map of the simplex is injective
on simplices. The proof is `Types.isPushout_of_isPullback_of_mono'`
pointwise, as in upstream `relativeCellComplexOfMono.isPushout`:
pullback from `Subcomplex.isPullback_hornAttach`, joint
surjectivity from `S ⊔ ofSimplex σ`, and uniqueness from
injectivity.
