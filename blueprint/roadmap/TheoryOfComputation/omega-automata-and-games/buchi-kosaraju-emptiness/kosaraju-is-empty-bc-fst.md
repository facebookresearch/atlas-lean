# Kosaraju Is Empty BC fst

Assume that `State` carries a Boolean equality test `==` that agrees with equality and a hash function; that equality on `State` is decidable; that membership in `na.start` is decidable; that membership in `na.accept` is decidable; that each proposition `na.Tr s x t` is decidable; and that `Symbol` is finite.

The costed scanner returns the same `Bool` as the uncosted scanner.
