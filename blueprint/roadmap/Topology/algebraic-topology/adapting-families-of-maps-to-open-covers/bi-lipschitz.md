# Morrison–Walker lemma on adapting families of maps, bi-Lipschitz case

Let $X$ be a
compact metric space, $T$ a metric space, $P \subseteq \mathbb{R}^k$ a convex linear polyhedron,
$(U_\alpha)_{\alpha \in \iota}$ a family of open subsets of $X$, and $\rho$ a partition of unity on
$X$ indexed by $\iota$ and subordinate to $U$. Let $f : P \times X \to T$ be continuous and suppose
that for each $p \in P$ the map $x \mapsto f(p, x)$ is a homeomorphism $h_p : X \to T$, and that for
some constant $L \ge 0$ the map $f$ is $L$-Lipschitz on $P \times X$ (for the sup metrics on
$\mathbb{R}^k$ and on $P \times X$) and every inverse $h_p^{-1}$ is $L$-Lipschitz. Then there are a
continuous map $F : [0, 1] \times P \times X \to T$, a constant $L' \ge 0$ and homeomorphisms
$H_{t,p} : X \to T$ for $(t, p) \in [0, 1] \times P$ such that: (i) $F(0, p, x) = f(p, x)$ for all
$p$ and $x$; (ii) $F(t, p, x) = H_{t,p}(x)$ for all $t$, $p$, $x$; (iii) there is a polyhedral
subdivision $K$ of $P$ such that, for every facet (maximal face) $D$ of $K$, the family
$(p, x) \mapsto F(1, p, x)$ with $p$ in the closed cell of $D$ is adapted to $U$ with bound $k$;
(iv) for every $S \subseteq X$, if $f$ is supported on $S$, then $F$, as a family with parameter
$(t, p) \in [0, 1] \times P$, is supported on $S$; (v) for every boundary subpolyhedron $Q$ of $P$
and every $S' \subseteq X$, if the restriction of $f$ to $Q \times X$ is supported on $S'$, then
the restriction of $F$ to $[0, 1] \times Q \times X$, as a family with parameter
$(t, q) \in [0, 1] \times Q$, is supported on $S'$; and (vi) every $H_{t,p}$ and every inverse
$H_{t,p}^{-1}$ is $L'$-Lipschitz.

## Sources

- S. Morrison and K. Walker, *The Blob Complex*, arXiv:1009.5025, Appendix B, Lemma B.0.1 (pp. 93–96): https://arxiv.org/pdf/1009.5025 Via leanprover/lean-eval@38361be, problem `families_of_maps_b01`.
