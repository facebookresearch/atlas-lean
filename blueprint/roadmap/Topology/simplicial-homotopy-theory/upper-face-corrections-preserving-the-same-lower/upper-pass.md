# Decreasing sequence of upper-face corrections

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, missing index `i : Fin (n + 3)`, and `h : Fin
(n + 3) → (underlying G) _⦋n + 1⦌`, `upperPass G i h r` is an `(n + 2)`-simplex at stage `r :
Fin (n + 3)`. At the last stage it is `lowerPass G h i`. The descending step from `j.succ` to
`Fin.castSucc j` applies `correctUpper G j` with prescribed face `h j.succ`.
