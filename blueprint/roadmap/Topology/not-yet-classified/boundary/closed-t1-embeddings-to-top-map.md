# Closed T1 Embeddings to Top map ι

Primary realized-boundary statement: `|∂Δ[n]| → |Δ[n]|` is a closed T1-embedding.

Finite-face gluing via the multicoequalizer `multicoequalizerDiagram n`
is preserved by `SSet.toTop` (`isColimitToTop'`), and each
`|face {i}ᶜ|` includes as the closed coordinate hyperplane `p i = 0` in
`Convexity.StdSimplex ℝ (Fin (n+1))` (isolated through `SimplexCategory.toTopHomeo`).
The topological finite gluing of closed subspaces is the generic
`TopCat.isClosedEmbedding_of_isColimit` descent: with the finite colimit
`isColimitToTop' n` and the face closed embeddings above, the union
`⋃ i, |face {i}ᶜ| = |∂Δ[n]|` includes as a closed embedding; the Hausdorff
`Convexity.StdSimplex ℝ (Fin (n+1))` then strengthens the complement to relative T1.
