# First matching face of a degeneracy

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 1)`, and `x ∈ (underlying G) _⦋n⦌`,
`(underlying G).δ (Fin.castSucc i) ((underlying G).σ i x) = x`.
Thus the face at index `i`, viewed in `Fin (n + 2)`, is a left inverse of the degeneracy at `i`.
