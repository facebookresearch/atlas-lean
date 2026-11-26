# Descending step of the upper-face pass

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 3)`, `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌`, and `j : Fin (n + 2)`,
`upperPass G i h (Fin.castSucc j) = correctUpper G j (upperPass G i h j.succ) (h j.succ)`.
The step prescribes face `j + 1` by the corresponding degeneracy correction.
