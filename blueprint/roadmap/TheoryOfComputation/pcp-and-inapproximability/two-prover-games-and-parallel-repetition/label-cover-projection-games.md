# Label Cover (projection games)

A *Label Cover* instance consists of a bipartite multigraph with left vertices $U$, right vertices $W$ and edges $E$, finite label sets $\beta$ (left) and $\gamma$ (right), and for each edge $e = (u, w)$ a projection $\pi_e : \beta \to \gamma$. A labelling $\ell : U \to \beta$, $r : W \to \gamma$ satisfies $e$ when $\pi_e(\ell(u)) = r(w)$. The value of the instance is the maximum over labellings of the fraction of satisfied edges. For $0 < s < c \le 1$, $\mathrm{GapLabelCover}_{\beta, \gamma}(c, s)$ is the promise problem of distinguishing value at least $c$ from value at most $s$. Label Cover is the projection case of a two-prover game in which the referee picks a uniform edge.

## Depends on

- [Two-prover one-round game and its value](two-prover-one-round-game.md)
- [2CSP instances](../dinur-s-gap-amplification/cspinstance.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 2001.
