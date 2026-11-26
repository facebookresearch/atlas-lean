# Restriction-transfer and index multiplication induce equal cohomology maps

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, `A
: Rep k G`, and `n : ℕ`. The induced maps on `H^n(G,A)` satisfy
`HomologicalComplex.homologyMap (restrictionCorestrictionCochains A T) n =
HomologicalComplex.homologyMap (H.index • 𝟙 (inhomogeneousCochains A)) n`.
