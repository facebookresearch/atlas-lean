# Yannakakis: rectangle covers lower-bound nonnegative rank and extension complexity

For every nonnegative matrix $M$, the support matrix $\mathrm{supp}(M)$ has a $1$-cover by $\mathrm{rank}_+(M)$ rectangles, so $C^1(\mathrm{supp}(M)) \le \mathrm{rank}_+(M)$ and $N^1(\mathrm{supp}(M)) \le \lceil \log_2 \max(1, \mathrm{rank}_+(M)) \rceil$ (the zero matrix has empty support, nonnegative rank $0$ and $C^1 = N^1 = 0$). By Yannakakis's factorization theorem the extension complexity of a polytope with nonempty interior in its affine hull equals the nonnegative rank of its slack matrix, up to that theorem's convention for degenerate cases, so the rectangle covering number of the slack matrix's support is a lower bound on extension complexity.

## Proof sketch

If $M = TU$ with $T, U \ge 0$ and inner dimension $r$, then $M_{ij} > 0$ iff some $k$ has $T_{ik} > 0$ and $U_{kj} > 0$, so the $r$ rectangles $\{i : T_{ik} > 0\} \times \{j : U_{kj} > 0\}$ cover the support.

## Depends on

- [Rectangle covers and nondeterministic communication complexity](rectangle-covers-and-nondeterministic-complexity.md)
- [Nonnegative rank of a matrix](../../../ComputerScience/machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)
- [Yannakakis' factorization theorem](../../../ComputerScience/approximation-algorithms/extended-formulations-and-extension-complexity/yannakakis-factorization-theorem.md)

## Sources

- M. Yannakakis, "Expressing Combinatorial Optimization Problems by Linear Programs", Journal of Computer and System Sciences 43(3), 1991.
- S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
