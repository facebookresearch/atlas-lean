# Exists coherent Iso extension nerve

Nerve gate for extensions: an equivalence edge in the nerve of
a category extends along the endpoint inclusion
`Δ[1] ⟶ SSet.coherentIso`. The extending map is the nerve map
classified by the isomorphism `nerve.homEquiv e`, which exists by
`SSet.Edge.isEquivalence_nerve_iff`. This proves the full
extension characterization for nerves, the one case where a
`coherentIso` extension is formal from inverse data because both
source and target are nerves.
