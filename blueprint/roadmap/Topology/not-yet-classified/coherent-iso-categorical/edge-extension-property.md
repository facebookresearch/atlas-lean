# Edge Extension Property

The **edge extension property** for the endpoint evaluation into `C`,
in its deliberately weak, homotopy-category-level form: for every
edge `ε'` of the target functor object `Fun(Δ[0], C)` between
evaluated vertices, there merely *exists* an edge `ε` of
`Fun(coherentIso, C)` between the original vertices whose evaluated
edge has the same `HomotopyCategory.homMk` as `ε'`. This does **not** ask for
a strict prism extension restricting along `{x₀} ⊗ Δ[1]` to the
given edge: through the prism dictionary
(`MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism`) such a
prism would be additional strict data that the definition does not
require. The downstream endpoint proof exploits exactly this
weaker form.
