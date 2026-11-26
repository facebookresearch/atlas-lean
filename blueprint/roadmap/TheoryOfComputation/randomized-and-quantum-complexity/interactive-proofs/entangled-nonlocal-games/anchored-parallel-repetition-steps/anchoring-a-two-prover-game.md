# Anchoring a two-prover game

Let $G = (X, Y, A, B, \mu, V)$ and $\alpha \in [0, 1]$. The *$\alpha$-anchored game* $G_\perp$ has question sets $X \cup \{\perp\}$ and $Y \cup \{\perp\}$: the referee draws $(x, y) \sim \mu$ and independently replaces each player's question by the anchor symbol $\perp$ with probability $\alpha$; the players must answer from $A$ and $B$, and the referee accepts automatically if either question was replaced, and otherwise applies $V$.

## Depends on

- [Two-prover one-round game and its value](../../../../pcp-and-inapproximability/two-prover-games-and-parallel-repetition/two-prover-one-round-game.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2), 2022.
