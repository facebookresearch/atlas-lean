# Buchi Graph edge

Assume that `State` carries a Boolean equality test `==` that agrees with equality and a hash function; that equality on `State` is decidable; that each proposition `na.Tr s x t` is decidable; and that `Symbol` is finite.

Edges of `buchiGraph` are exactly `Buchi.Step` transitions.
