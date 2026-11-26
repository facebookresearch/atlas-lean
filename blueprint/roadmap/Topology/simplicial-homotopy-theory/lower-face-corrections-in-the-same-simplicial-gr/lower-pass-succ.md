# Successor step of the lower-face pass

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `h : Fin (n + 3) → (underlying G) _⦋n + 1⦌`, and `j : Fin (n + 2)`,
`lowerPass G h j.succ = correctLower G j (lowerPass G h (Fin.castSucc j)) (h (Fin.castSucc j))`.
The step prescribes face `j` by the corresponding degeneracy correction.
