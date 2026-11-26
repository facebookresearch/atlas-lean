# Restriction of the basis-valued bar cochain

Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `n : ℕ`. Restricting `barBasisCochain
n` along `H.subtype`, with the identity coefficient morphism on `Res_H((Rep.barComplex k G).X
n)`, gives `restrictedBarBasisCochain n`. This is the equality obtained by applying
`(cochainsMap H.subtype (𝟙 _)).f n` to the ambient cochain.
