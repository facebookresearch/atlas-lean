# Scan Blocks C cost le

Assume that `V` carries a Boolean equality test `==` and a hash function; that equality on `V` is decidable; and that `accept` is a decidable predicate.

The costed block scan's cost is bounded by the per-block budget: one
length test plus the block's adjacency-entry scans plus two tests per
block state.
