# An upper-face error is trivial at a later-face predecessor

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 2)`, `k : Fin (n + 3)`, and `hjk : j.succ < k`. For `x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, suppose `δ k x = b` and `δ (upperTailDeg hjk).succ b = δ (k.pred hjk.ne_zero) a`. Then
`δ (k.pred hjk.ne_zero) (upperError G j x a) = 1`,
where `δ` denotes the face maps of `underlying G` and the predecessor has value `k - 1`.
