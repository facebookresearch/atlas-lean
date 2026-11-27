# Finite parity games are positionally determined

Let $G$ be a parity game with finitely many positions, with the max-parity winning condition; as in the definition of a parity game, every position has at least one move, so every play is infinite. Let $d \in \mathbb{N}$ bound every priority of $G$. Then for every position $v$ and every player $p$,

$$v \in W_p \quad \text{or} \quad v \in W_{\bar p},$$

where $W_p$ is the [winning region](winning-region.md) of $p$, the positions from which $p$ has a positional strategy that wins every play starting there, and $\bar p$ is the opponent of $p$. So every position is won positionally by one of the two players. Since the two winning regions are [disjoint](disjoint-winning-region.md), it is won by exactly one.

At least one player wins from each position by the memoryless determinacy theorem for the lowest-priority condition, transported to the max-parity condition by [reversing priorities](../parity-condition-on-infinite-sequences/reversing-priorities-exchanges-min-parity-and.md), replacing each priority $q$ with $D - q$ for an even $D \ge d$; Zielonka's induction on priorities proves it directly.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *STACS 2000*, LNCS 1770, Springer, 2000, Theorem 1 (memoryless determinacy, credited there to E. A. Emerson and C. S. Jutla, FOCS 1991, and to A. W. Mostowski, 1991)
- W. Zielonka, "Infinite games on finitely coloured graphs with applications to automata on infinite trees", *Theoretical Computer Science* 200 (1998), 135-183.
