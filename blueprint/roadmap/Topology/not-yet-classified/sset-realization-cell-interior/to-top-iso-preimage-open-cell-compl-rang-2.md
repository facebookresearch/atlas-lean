# To Top Iso preimage open Cell compl range zero

The `n = 0` base case: the `toTopIso` preimage of the open cell is the
complement of the realized-boundary range. Since `∂Δ[0] = ⊥`
(`SSet.boundary_zero`), the range is empty: the domain is initial, hence empty
via `TopCat.isInitialPEmpty`. The preimage is everything because the
topological `0`-simplex is a singleton (`Convexity.StdSimplex`
uniqueness).
