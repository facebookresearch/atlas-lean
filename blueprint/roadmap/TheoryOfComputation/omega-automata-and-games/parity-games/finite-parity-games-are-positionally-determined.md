# Finite parity games are positionally determined

Let $G$ be a parity game with finitely many positions, with the max-parity winning condition; as in the definition of a parity game, every position has at least one move, so every play is infinite. Then every position of $G$ lies in the winning region of exactly one of the two players: from each position, one of the players has a positional strategy that wins every play starting there.

At most one player wins from a position because the two winning regions are disjoint. At least one does by the memoryless determinacy theorem for the lowest-priority condition, transported to the max-parity condition by replacing each priority $p$ with $D - p$ for an even $D$ at least the largest priority of $G$.

## Depends on

- [Winning region of a parity game](winning-region.md)

## Proof depends on

- [The winning regions of the two players are disjoint](disjoint-winning-region.md)
- [Reversing priorities exchanges the min-parity and max-parity conditions](../parity-condition-on-infinite-sequences/reversing-priorities-exchanges-min-parity-and.md)

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *STACS 2000*, LNCS 1770, Springer, 2000, Theorem 1 (memoryless determinacy, credited there to E. A. Emerson and C. S. Jutla, FOCS 1991, and to A. W. Mostowski, 1991)
