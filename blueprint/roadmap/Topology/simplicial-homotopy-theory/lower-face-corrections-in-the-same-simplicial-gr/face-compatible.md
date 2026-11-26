# Compatibility of group-valued horn faces

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, and `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌`. The predicate `FaceCompatible G i h` requires that for every `k : Fin (n + 2)` and `j : Fin (n + 3)` with `Fin.castSucc k < j`, `Fin.castSucc k ≠ i`, and `j ≠ i`,
`(underlying G).δ k (h j) = (underlying G).δ (j.pred _) (h (Fin.castSucc k))`.
The value of the predecessor is `j - 1`; these are the pairwise face equations away from the missing index `i`.
