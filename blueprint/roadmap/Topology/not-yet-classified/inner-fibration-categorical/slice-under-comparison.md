# Slice Under Comparison

Stevenson's slice comparison map `X_{x/} → S_{x/} ×_S X`
(the right vertical map of the transposed square in Step 3; here
the base vertex of the target slice is `x ≫ p`): the map into the
pullback of `SSet.sliceUnder.proj S (x ≫ p)` along `p` induced by
postcomposition (`SSet.sliceUnder.map`) and by the forgetful map
(`SSet.sliceUnder.proj`), which agree after mapping to `S` by
`SSet.sliceUnder.map_proj`. Stevenson proves this map is a left
fibration when `p` is an inner fibration, with fiber over `y` the
mapping-space map `SSet.mappingSpaceLeft.map X x y p`; neither
statement is landed (no left-fibration API for join slices), and
the transposition of boundary lifting problems against `p` to
boundary lifting problems against this map — via the join
decomposition `∂Δⁿ = Δ^{{0}} ⋆ ∂Δ^{{1,…,n}} ∪ Δ^{{1,…,n}}` — is
the geometric heart of the missing core below.
