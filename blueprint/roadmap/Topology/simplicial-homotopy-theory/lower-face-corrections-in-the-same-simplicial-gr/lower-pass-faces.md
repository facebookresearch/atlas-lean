# Prescribed faces before a lower-pass stage

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌` satisfy `FaceCompatible G i h`, the pairwise simplicial face equations away from `i`. For a stage `r : Fin (n + 3)` with `r ≤ i` and any `k : Fin (n + 3)` with `k < r`,
`(underlying G).δ k (lowerPass G h r) = h k`.
Thus all faces strictly before the stage have their prescribed values.
