# Min-parity and max-parity games have the same winners after reversing priorities

Let $G$ be a parity game with priorities bounded by $d$, and let $D \ge d$ be even. Let $G'$ be the game on the same arena, with the same owners and moves, and with priorities $p'(v) = D - p(v)$.

**Theorem.**
1. A play is won by Even in $G$ under the min-parity condition (the least priority occurring infinitely often is even) if and only if it is won by Even in $G'$ under the max-parity condition (the largest priority occurring infinitely often is even).
2. Consequently the two games have the same winning strategies, positional or not, and the same winning regions for each player.

**Proof.** Part 1 is the [sequence lemma](../parity-condition-on-infinite-sequences/reversing-priorities-exchanges-min-parity-and.md) applied to the priority sequence of the play. Part 2 follows because plays and strategies depend only on the arena, which the two games share.

This transport lets results stated with the min-parity convention be used for max-parity games, and conversely. Jurdziński and Grädel–Walukiewicz state their results with the min-parity convention.

## Proof depends on

- [Reversing priorities exchanges min-parity and max-parity](../parity-condition-on-infinite-sequences/reversing-priorities-exchanges-min-parity-and.md)

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *STACS 2000*, LNCS 1770, Springer, 2000, <https://www.dcs.warwick.ac.uk/people/academic/Marcin.Jurdzinski/Papers/Jur00-STACS.pdf>, Section 2: parity games with the winning condition "$\min \mathrm{Inf}(\pi)$ is even", strategies as functions $\sigma : V_\Diamond \to V$, and Theorem 1 (memoryless determinacy).
- E. Grädel and I. Walukiewicz, "Positional determinacy of games with infinitely many priorities", *Logical Methods in Computer Science* 2(4:6), 2006, <https://arxiv.org/pdf/cs/0610035>, Introduction (parity games and the min-parity condition).
