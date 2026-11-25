# Normalized Chain Complex Coproduct Iso

The canonical isomorphism from the explicit coproduct of copies of `R`
indexed by `X.nonDegenerate n` to `(X.normalizedChainComplex R).X n`.

It is defined as the canonical isomorphism between the colimit cocone points
supplied by Mathlib's standard coproduct witness `coproductIsCoproduct` and
`X.isColimitCofanNormalizedChainComplex R n`. This construction uses only the
public colimit API and remains stable if the private implementation of
normalized chains is replaced by an isomorphic one.
