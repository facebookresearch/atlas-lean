# Error in a prescribed upper face

For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `j : Fin (n + 1)`, `x ∈ (underlying G) _⦋n + 1⦌`, and `h ∈ (underlying G) _⦋n⦌`,
`upperError G j x h = ((underlying G).δ j.succ x)⁻¹ * h`.
The inverse of the current face at `j + 1` multiplies the prescribed face on the left.
