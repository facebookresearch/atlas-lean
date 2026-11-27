# Mean-payoff games and energy games are interreducible

For a finite one-player graph $G$ with integer weights, $G$ satisfies $\mathrm{MeanPayoff}^- \ge 0$ (every infinite path from the given vertex has
$\mathrm{MeanPayoff}^- \ge 0$) if and only if it satisfies $\mathrm{Energy} < \infty$, both being equivalent to every reachable cycle having
non-negative total weight; for a single sequence the two properties are not equivalent. Consequently, for a finite
[mean-payoff game](classical-quantitative-objectives.md) $\mathcal{G}$ and the energy game $\mathcal{G}'$ on the same graph in which the vertices of Max in $\mathcal{G}$ belong to the
player who minimizes the energy (Min of $\mathcal{G}'$) and those of Min to the maximizer, $\mathrm{val}^{\mathcal{G}}(u) \ge 0$ if and only if $\mathrm{val}^{\mathcal{G}'}(u) < \infty$ for every vertex $u$. An algorithm computing energy values in time
$T(n, m, W)$ thus decides $\mathrm{val}^{\mathcal{G}}(u) \ge 0$ for every vertex $u$ in time $T(n, m, W)$, and computes the value of a given vertex in time
$O(\log(n^2 W) \cdot T(n, m, 2nW))$: a binary search over the candidate values $p/q$ with $q \le n$ tests each threshold on the weights $q w - p$, whose absolute values are at most $2nW$.

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)

## Proof depends on

- [Energy, mean-payoff and total-payoff games are positionally determined](positional-determinacy-of-mean-payoff-and-energy-games.md)
- [Mean-payoff values are rationals with small denominators](mean-payoff-values-are-rationals-with-small-denominators.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.2, Lemma 5.3 (relating mean payoff and energy objectives) and Corollary 5.3 with their proofs.
