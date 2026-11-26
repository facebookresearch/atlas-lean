# Resolution-Hom formula for subgroup restriction

Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `A : Rep k G`. Put
`I_H=inhomogeneousResolutionLinearHomCochainIso (Res_H A)` and let `L` be the contravariant
Hom-cochain functor with coefficient `Res_H A`. Then `cochainsMap H.subtype (𝟙 (Res_H A)) ≫
I_H.hom = ambientRestrictedBarCochains H A ≫ L.map (barRestriction H).op`. Thus subgroup
restriction is precomposition by the bar inclusion after the ambient cochain comparison.
