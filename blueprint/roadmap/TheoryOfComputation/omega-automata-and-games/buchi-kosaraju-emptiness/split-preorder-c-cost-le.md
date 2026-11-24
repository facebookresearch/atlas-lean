# Split Preorder C cost le

Assume that `V` carries a Boolean equality test `==` and a hash function.

The costed split's cost: one insertion per root plus at most two tests
per preorder vertex plus the final test. In `kosarajuSCCs` the roots are
the second pass's `forestRoots`, so the construction charges
`forestRoots.length` insertions — not `decreasingFinishAll.length`.
