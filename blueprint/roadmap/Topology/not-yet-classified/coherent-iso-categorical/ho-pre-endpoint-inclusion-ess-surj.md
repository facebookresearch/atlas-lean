# Essential surjectivity of endpoint evaluation, unconditionally

For
every simplicial set `C` (no quasicategory hypothesis), the functor
`h Fun(coherentIso, C) ⟶ h Fun(Δ[0], C)` induced by precomposition with the
endpoint inclusion is essentially surjective. Indeed, precomposition with
the terminal map `coherentIso.toDeltaZero` is a strict section after
`SSet.hoFunctor`, by `endpointInclusion_comp_toDeltaZero`; at the vertex
level this is surjectivity via constant maps.
