# Any Accept Reach C

Assume that `V` carries a Boolean equality test `==` and a hash function and that `accept` is a decidable predicate.

Costed accept-and-reachable scan: the same `Bool` as
`block.any fun s => decide (accept s) && reachSet.contains s`, plus the
test count. Each examined state charges `1` for the `decide`, plus `1`
more for the `contains` test only when `decide` is true (short-circuit
`&&`); the scan stops at the first `true` state.
