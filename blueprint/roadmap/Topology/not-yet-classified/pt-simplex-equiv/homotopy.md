# Homotopy

Given `p` and `q` in `X.PtSimplex n x`, this is the type of homotopies between
`p` and `q`. These homotopies are given by morphisms `Δ[n] ⊗ Δ[1] ⟶ X`.
(This contrasts with `RelStruct` or `RelStruct₀` which only involve the more
basic data of a morphism `Δ[n + 1] ⟶ X`. See `SSet.PtSimplex.Homotopy.relStruct₀`
and `SSet.PtSimplex.RelStruct₀.homotopy` for a connection between these
two notions for Kan complexes.)
