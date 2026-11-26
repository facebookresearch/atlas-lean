# Every nonmissing face of the group horn filler

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌` satisfying `FaceCompatible G i h`, the pairwise face equations away from `i`, every `k : Fin (n + 3)` with `k ≠ i` satisfies
`(underlying G).δ k (hornFiller G i h) = h k`.
Thus the constructed `(n + 2)`-simplex fills the compatible horn at index `i`.
