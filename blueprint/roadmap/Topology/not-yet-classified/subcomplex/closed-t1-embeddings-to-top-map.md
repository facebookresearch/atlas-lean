# Closed T1 Embeddings to Top map ι

Realization of an arbitrary simplicial subcomplex inclusion is a closed
T1-embedding. The proof uses the skeletal filtration `relativeCellComplexOfMono`
as an ℕ-indexed transfinite composition whose steps attach coproducts of
boundary inclusions `∂Δ[n] ↪ Δ[n]`. Each `l d` is a coproduct of boundary
inclusions, hence `toTop.map (l d)` is a colimit of `closedT1` maps, in
`coproducts` and thus `closedT1` by stability. Pushout stability gives `r d`
in `closedT1`. Finally `S.ι` is the transfinite composition of the `r d`,
mapped by `toTop` (left adjoint preserves the ℕ-colimit) to a transfinite
composition of `closedT1` maps, which is `closedT1` by stability under
transfinite composition.
