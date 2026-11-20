# Morrison–Walker lemma on adapting families of maps to an open cover

Let $X$ be a compact
topological space, $T$ a topological space, $P \subseteq \mathbb{R}^k$ a convex linear polyhedron,
$(U_\alpha)_{\alpha \in \iota}$ a family of open subsets of $X$, and $\rho$ a partition of unity on
$X$ indexed by $\iota$ and subordinate to $U$ (the closed support of $\rho_\alpha$ lies in
$U_\alpha$). Then for every continuous map $f : P \times X \to T$ there is a continuous map
$F : [0, 1] \times P \times X \to T$ such that: (i) $F(0, p, x) = f(p, x)$ for all $p \in P$ and
$x \in X$; (ii) there is a polyhedral subdivision $K$ of $P$ such that, for every facet (maximal
face) $D$ of $K$, the family $(p, x) \mapsto F(1, p, x)$ with $p$ in the closed cell of $D$ is
adapted to $U$ with bound $k$; (iii) for every $S \subseteq X$, if $f$ is supported on $S$, then
$F$, as a family with parameter $(t, p) \in [0, 1] \times P$, is supported on $S$; (iv) for every
boundary subpolyhedron $Q$ of $P$ and every $S' \subseteq X$, if the restriction of $f$ to
$Q \times X$ is supported on $S'$, then the restriction of $F$ to $[0, 1] \times Q \times X$, as a
family with parameter $(t, q) \in [0, 1] \times Q$, is supported on $S'$.

## Sources

- S. Morrison and K. Walker, *The Blob Complex*, arXiv:1009.5025, Appendix B, Lemma B.0.1 (pp. 93–96): https://arxiv.org/pdf/1009.5025. Problem `families_of_maps_b01` of the lean-eval benchmark.
