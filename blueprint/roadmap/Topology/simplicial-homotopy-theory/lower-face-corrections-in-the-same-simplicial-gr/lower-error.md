# Error in a prescribed lower face

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n + 1⦌`, and `h ∈ (underlying G) _⦋n⦌`,
`lowerError G j x h = ((underlying G).δ (Fin.castSucc j) x)⁻¹ * h`.
The inverse of the current face multiplies the prescribed face on the left.
