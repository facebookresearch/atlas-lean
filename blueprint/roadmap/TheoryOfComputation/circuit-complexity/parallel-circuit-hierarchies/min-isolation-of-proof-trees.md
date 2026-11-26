# Min-isolation of proof trees in semi-unbounded circuits

Assign integer weights to the wires of a layered semi-unbounded circuit and define the weight of a proof tree as the sum of the weights of its wires (counted with multiplicity). A weight assignment is *min-isolating* if every true gate has a unique proof tree of minimum weight. For circuits of polynomial size and logarithmic depth, weights chosen uniformly from a polynomial range are min-isolating with high probability, and suitable weights can be generated deterministically with small space by scaling weights level by level with the AND-depth.

## Proof sketch

Apply the isolation lemma to the family of proof trees of each gate, whose number of distinct wire multisets is controlled by the logarithmic depth; scaling weights by AND-level keeps proof-tree weights distinct across levels, which allows level-by-level derandomization.

## Depends on

- [Layered semi-unbounded circuits and proof trees](semi-unbounded-circuits-and-proof-trees.md)
- [Isolation lemma](../../../Combinatorics/probabilistic-combinatorics/isolation-lemma.md)

## Proof depends on

- [Isolation lemma](../../../Combinatorics/probabilistic-combinatorics/isolation-lemma.md)

## Sources

- Klaus Reinhardt, Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing, 2000.
- William M. Hoza, "NL = UL", Electronic Colloquium on Computational Complexity, 2026.
