# Irrep Multiplicity

The multiplicity of an irreducible representation `σ` in `ρ` (note the order: `σ`
occurs in `ρ`). The `IsIrreducible σ` argument is what makes this a multiplicity rather
than an intertwining-space rank: callers must supply it, so a reducible `σ` cannot be
passed off as an irrep. For a finite group, finite-dimensional representations and
irreducible `σ`, this counts the copies of `σ` in a decomposition of `ρ` into irreducibles
(`irrepMultiplicity_of_isIrreducible`, `irrepMultiplicity_prod`, `irrepMultiplicity_congr`).
