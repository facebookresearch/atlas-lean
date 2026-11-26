# Winning condition of the CHSH game

Winning condition of the CHSH game for deterministic strategies: Alice and
Bob answer the inputs `x y : Fin 2` with the bits `A x` and `B y`, and
`chshWin A B x y` is true exactly when `A x XOR B y` equals `x AND y`, that
is, the answers differ if and only if `x = y = 1`.
