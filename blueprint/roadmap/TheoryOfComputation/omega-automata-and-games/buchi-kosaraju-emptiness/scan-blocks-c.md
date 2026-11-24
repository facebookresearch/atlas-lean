# Scan Blocks C

Assume that `V` carries a Boolean equality test `==` and a hash function; that equality on `V` is decidable; and that `accept` is a decidable predicate.

Costed block scan: the same `Bool` as
`blocks.any fun block => blockCyclicB graph block &&
block.any fun s => decide (accept s) && reachSet.contains s`, plus the
total cost. Per block: the cyclic test's cost, plus the
accept-and-reachable cost only when the block is cyclic (short-circuit
`&&`); the scan stops at the first `true` block.
