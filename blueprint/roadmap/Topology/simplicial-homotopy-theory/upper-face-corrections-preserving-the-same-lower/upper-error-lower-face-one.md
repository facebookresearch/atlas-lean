# An upper-face error is trivial at an earlier face

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `k, j : Fin (n + 2)`, and `hkj : k < j`. For `x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, suppose `δ (Fin.castSucc k) x = b` and `δ k a = δ j b`. Then
`δ k (upperError G j x a) = 1`,
where `δ` denotes the face maps of `underlying G`.
