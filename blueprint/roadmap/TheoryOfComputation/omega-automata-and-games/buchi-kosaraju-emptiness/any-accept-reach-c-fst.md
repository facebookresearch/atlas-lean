# The costed accept-and-reachable scan gives the right answer

The vertex type has a Boolean equality test and a hash function, used to store finite sets of vertices in hash sets; the Boolean test need not agree with equality. The accept-and-reachable test of a block, for a decidable accepting predicate and a hash set $R$ of vertices, asks whether some vertex of the block is accepting and its lookup in $R$ returns true. The costed scan of a block returns true exactly when some vertex of the block is accepting and its lookup in $R$ returns true.
