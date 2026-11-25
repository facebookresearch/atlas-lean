# Sigma To Top eq to eqv Gen colimit Type Rel

Bridge from sigma-presentation equality to the tautological-colimit
relation: equal `SSet.sigmaToTop X` values give related points in the realized
tautological diagram. The legs of the realized tautological cocone compute to
`SSet.sigmaToTop` by definition, so the equality transports along
`coconePointUniqueUpToIso` to the chosen colimit and `Limits.Types.colimit_eq`
extracts the relation.
