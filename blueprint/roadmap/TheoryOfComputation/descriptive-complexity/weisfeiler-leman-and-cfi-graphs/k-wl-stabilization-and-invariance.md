# Stabilization and isomorphism invariance of $k$-WL

For every $k \ge 1$ and finite graph $G$, the $k$-WL partitions of $V^k$ are successively finer, and there is a least $t_\infty < |V|^k$ at which a refinement step no longer changes the partition; the coloring at that round is the stable coloring. Each round's coloring is isomorphism invariant (equivariant): an isomorphism $\pi : G \to H$ satisfies $c^H_t(\pi \bar u) = c^G_t(\bar u)$ for all $t$, including the stable round. Consequently, if $k$-WL distinguishes $(G, \bar u)$ and $(H, \bar v)$, no isomorphism from $G$ to $H$ maps $\bar u$ to $\bar v$, so $k$-WL is a sound non-isomorphism test.

## Proof sketch

Each refinement step refines because the new color contains the old one; a strictly finer partition of a finite set of size $|V|^k$ can occur fewer than $|V|^k$ times. Invariance is an induction on $t$. (Derived.) $(k+1)$-WL is at least as strong as $k$-WL: by induction on the rounds, the $(k+1)$-WL color of $(u_1,\dots,u_k,u_k)$ determines the $k$-WL color of $\bar u$ at the same round.

## Depends on

- [$k$-dimensional Weisfeiler–Leman refinement](k-dimensional-weisfeiler-leman.md)

## Sources

- M. Grohe, "The Logic of Graph Neural Networks", 36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2021); arXiv:2104.14624, Sections II and V ($k$-ary invariants and their equivariance; $k$-WL defines a sequence of $k$-ary invariants; a least $t_\infty < n^k$ at which the coloring is stable).
- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992, Section 5 (at most $n^k$ iterations; Theorem 5.2).
