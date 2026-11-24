# Block Cyclic B

Assume that equality on `V` is decidable.

Boolean cyclic test for a block: `true` iff the block's length is at
least two, or it contains a state with a self-loop in `graph`. Computable
with no edge oracle: a self-loop is adjacency-list membership, tested by
`DirectedAdjacency.hasEdge`. The length test is only a valid test for
two distinct states under `block.Nodup` (carried explicitly in
`blockCyclicB_eq_true`): without it, `[s, s]` would pass the length test
with no self-loop.
