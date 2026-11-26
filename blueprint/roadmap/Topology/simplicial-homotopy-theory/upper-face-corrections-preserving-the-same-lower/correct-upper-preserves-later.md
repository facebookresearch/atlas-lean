# An upper correction preserves a later prescribed face

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 2)`, `k : Fin (n + 3)`, and `hjk : j.succ < k`. For `x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, suppose `δ k x = b` and `δ (upperTailDeg hjk).succ b = δ (k.pred hjk.ne_zero) a`. Then
`δ k (correctUpper G j x a) = b`,
where `δ` denotes the face maps of `underlying G`. The compatibility equation ensures that correcting face `j + 1` preserves the later face `k`.
