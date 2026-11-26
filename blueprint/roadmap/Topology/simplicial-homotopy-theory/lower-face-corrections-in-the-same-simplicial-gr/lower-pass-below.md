# The lower pass fills every face before the missing index

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌` satisfying the pairwise face equations `FaceCompatible G i h` away from `i`, every `k : Fin (n + 3)` with `k < i` satisfies
`(underlying G).δ k (lowerPass G h i) = h k`.
This describes the faces of the `(n + 2)`-simplex at the missing-index stage.
