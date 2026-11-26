# Entangled strategies and the entangled value of a game

Let $G = (X, Y, A, B, \mu, V)$ be a two-prover one-round game. A finite-dimensional *entangled (tensor) strategy* consists of finite-dimensional Hilbert spaces $H_A, H_B$, a unit vector $\psi \in H_A \otimes H_B$, and for every $x \in X$ a POVM $\{P^x_a\}_{a \in A}$ on $H_A$ and for every $y \in Y$ a POVM $\{Q^y_b\}_{b \in B}$ on $H_B$. It produces answers with probability $p(a, b \mid x, y) = \langle \psi, (P^x_a \otimes Q^y_b) \psi \rangle$ and wins with probability $\sum_{x,y} \mu(x,y) \sum_{a,b} V(x,y,a,b)\, p(a,b \mid x,y)$. The *entangled value* $\mathrm{val}^*(G)$ is the supremum of the winning probability over all finite-dimensional entangled strategies. Deterministic strategies are the one-dimensional case, so $\mathrm{val}(G) \le \mathrm{val}^*(G)$.

## Depends on

- [Two-prover one-round game and its value](../../../pcp-and-inapproximability/two-prover-games-and-parallel-repetition/two-prover-one-round-game.md)

## Sources

- R. Cleve, P. Høyer, B. Toner and J. Watrous, "Consequences and Limits of Nonlocal Strategies", IEEE Conference on Computational Complexity, 2004.
- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "MIP* = RE", arXiv:2001.04383, 2020.
