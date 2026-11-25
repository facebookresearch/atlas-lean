# Positional determinacy of finite parity games (Zielonka)

A parity game on a set of positions consists of an owner (the even or the odd player) for each position, a move relation in which every position has at least one move, and a priority in $\mathbb{N}$ for each position. A play is an infinite sequence of positions following moves; the even player wins it when the largest priority occurring infinitely often is even, and the odd player when it is odd. A positional strategy for a player picks one move at each of that player's positions, and the winning region $W_p$ of player $p$ is the set of positions from which $p$ has a positional strategy winning every play that starts there and follows it.

The following holds. Let $G$ be a parity game on a finite set of positions whose priorities are all at most some $d \in \mathbb{N}$. Then for every position $v$ and every player $p$,

$$v \in W_p \quad \text{or} \quad v \in W_{\bar p},$$

where $\bar p$ is the opponent of $p$. So every position is won positionally by one of the two players.

## Sources

- W. Zielonka, "Infinite games on finitely coloured graphs with applications to automata on infinite trees", *Theoretical Computer Science* 200 (1998), 135-183.
