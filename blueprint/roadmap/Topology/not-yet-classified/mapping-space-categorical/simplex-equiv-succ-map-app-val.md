# Simplex Equiv Succ map app val

Under the transport `SSet.mappingSpaceRight.simplexEquivSucc`
(an `n`-simplex of the right mapping space read as an
`(n + 1)`-simplex of `X`), the induced map
`SSet.mappingSpaceRight.map X a b F` is postcomposition with `F`.
For `n = 0` this says that the representing `1`-simplex of a
`0`-simplex of the mapping space is sent to its postcomposition
with `F`; identifying that `1`-simplex with an `SSet.Edge` is
`SSet.mappingSpaceRight.zeroSimplexEquivEdge` downstream
(`MappingSpacePi.lean`, formerly
the additional comparison obligation).
