# A lower correction attains the prescribed face

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n + 1⦌`, and `h ∈ (underlying G) _⦋n⦌`,
`(underlying G).δ (Fin.castSucc j) (correctLower G j x h) = h`.
Thus the correction prescribes the face at index `j`.
