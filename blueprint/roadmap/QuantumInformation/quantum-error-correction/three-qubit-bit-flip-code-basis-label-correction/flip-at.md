# Flipping one bit of a three-bit label

For a three-bit label `x : Fin 8`, read as bits `(b₂ b₁ b₀)`, and a position
`j : Fin 3`, `flipAt j x` is the label obtained by flipping bit `j`, that
is, the bitwise xor of `x` with `2 ^ j`.
