# Buchi Graph reachable

Assume that `State` carries a Boolean equality test `==` that agrees with equality and a hash function; that equality on `State` is decidable; that each proposition `na.Tr s x t` is decidable; and that `Symbol` is finite.

Reachability in `buchiGraph` is exactly `ReflTransGen Buchi.Step`.
