# Kosaraju Is Empty BC cost le

Assume that `State` carries a Boolean equality test `==` that agrees with equality and a hash function; that equality on `State` is decidable; that membership in `na.start` is decidable; that membership in `na.accept` is decidable; that each proposition `na.Tr s x t` is decidable; and that `Symbol` is finite.

The costed scanner's cost: one insertion per start-reachable vertex
plus the per-block budget (one length test plus the block's
adjacency-entry scans plus two tests per block state).
