# A correct lower face has identity error

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n +
1⦌`, and `h ∈ (underlying G) _⦋n⦌`, if `(underlying G).δ (Fin.castSucc j) x = h`, then
`lowerError G j x h = 1` in the degree-`n` group.
