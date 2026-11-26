# Computational depth

For a description method and a time bound $t$, the *computational depth* of $x$ at time $t$ is $\mathrm{depth}^t(x) = K^t(x) - K(x) \ge 0$, how much longer the shortest descriptions become when they must run in time $t$; for $t_1 \le t_2$ the depth between them is $K^{t_1}(x) - K^{t_2}(x)$. Then $\mathrm{depth}^t(x) + K(x) = K^t(x)$, depth is antitone in $t$, it is $0$ iff some shortest description runs within time $t$, and for every $x$ it is $0$ for all sufficiently large $t$.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Sources

- L. Antunes, L. Fortnow, D. van Melkebeek and N. V. Vinodchandran, "Computational Depth: Concept and Applications", Theoretical Computer Science 354(3), 2006.
