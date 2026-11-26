# A lower correction preserves an earlier prescribed face

Let `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `k, j : Fin (n + 2)`, and `hkj : k < j`. For `x ∈ (underlying G) _⦋n + 2⦌` and `a, b ∈ (underlying G) _⦋n + 1⦌`, assume `δ (Fin.castSucc k) x = b` and `δ k a = δ (lowerPairPred hkj) b`. Then
`δ (Fin.castSucc k) (correctLower G j x a) = b`,
where `δ` denotes the face maps of `underlying G`. Prescribing face `j` therefore preserves face `k` under this compatibility equation.
