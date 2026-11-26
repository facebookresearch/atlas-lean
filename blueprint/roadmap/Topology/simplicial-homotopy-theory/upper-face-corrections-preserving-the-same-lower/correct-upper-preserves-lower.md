# An upper correction preserves an earlier prescribed face

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `k, j : Fin (n + 2)`, and `hkj : k < j`. For `x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, suppose `δ (Fin.castSucc k) x = b` and `δ k a = δ j b`. Then
`δ (Fin.castSucc k) (correctUpper G j x a) = b`.
Thus correcting face `j + 1` preserves face `k`; `δ` denotes the face maps of `underlying G`.
