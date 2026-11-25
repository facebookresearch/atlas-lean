# Switching lemma for multigraph currents

Let $V$ be a finite set and $\iota$ a finite index set with an endpoint map $i \mapsto \mathrm{ends}(i)$ to unordered pairs of $V$ (a multigraph); write $\partial K$ for the set of vertices of odd [degree](deg-k.md) in $K$. Let $m \subseteq \iota$ contain no loop, with $\partial m = A$, let $u \ne v$ be vertices
and $F$ a real function of subsets of $\iota$. Then

$$\sum_{K \subseteq m,\ \partial K = A \triangle \{u, v\}} F(m) = \sum_{K \subseteq m,\ \partial K = A} F(m)\, \mathbf 1_{u \leftrightarrow v \text{ in } m},$$

where $u \leftrightarrow v$ in $m$ means that $u$ and $v$ are [connected](conn-k.md) through $m$ (M. Aizenman, *Geometric analysis of $\varphi^4$ fields and Ising models*, Comm. Math. Phys. 86 (1982) 1–48; H. Duminil-Copin, *Random currents expansion of the Ising model*, arXiv:1607.06933 (2016)).
