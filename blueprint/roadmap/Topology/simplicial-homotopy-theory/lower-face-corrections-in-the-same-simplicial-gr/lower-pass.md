# Increasing sequence of lower-face corrections

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, and `h : Fin (n + 3) → (underlying G) _⦋n +
1⦌`, `lowerPass G h r` is an `(n + 2)`-simplex at stage `r : Fin (n + 3)`. It starts at the
group identity at stage zero and, from stage `Fin.castSucc j` to `j.succ`, applies
`correctLower G j` with prescribed face `h (Fin.castSucc j)`.
