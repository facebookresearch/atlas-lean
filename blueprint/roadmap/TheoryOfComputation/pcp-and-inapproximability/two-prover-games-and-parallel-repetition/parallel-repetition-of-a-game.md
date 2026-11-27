# Parallel repetition of a two-prover game

The $n$-fold *parallel repetition* $G^{n}$ of a two-prover game $G = (X, Y, A, B, \mu, V)$ is the game with questions $X^n, Y^n$, answers $A^n, B^n$, question distribution $\mu^{\otimes n}$ (independent coordinates) and predicate $V^{n}(\vec x, \vec y, \vec a, \vec b) = \prod_{j=1}^n V(x_j, y_j, a_j, b_j)$. Strategies of $G^n$ are arbitrary maps $X^n \to A^n$ and $Y^n \to B^n$, so a player's answer in one coordinate may depend on all its questions. Playing an optimal strategy of $G$ independently in each coordinate gives $\mathrm{val}(G^n) \ge \mathrm{val}(G)^n$.

## Depends on

- [Two-prover one-round game and its value](two-prover-one-round-game.md)

## Sources

- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing 5, 2009.
- R. Raz, "A Parallel Repetition Theorem", SIAM Journal on Computing 27(3), 1998.
