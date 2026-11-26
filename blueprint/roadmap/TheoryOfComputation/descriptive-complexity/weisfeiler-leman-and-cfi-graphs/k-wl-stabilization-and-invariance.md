# Stabilization and isomorphism invariance of $k$-WL

For every $k \ge 1$ and finite graph $G$, the $k$-WL partitions of $V^k$ are successively finer and become constant after at most $|V|^k$ rounds; the stable partition is a fixed point of one refinement step. Isomorphisms commute with $k$-WL colorings: an isomorphism $\pi : G \to H$ satisfies $c^H_t(\pi \bar u) = c^G_t(\bar u)$ for all $t$. Consequently $k$-WL is a sound non-isomorphism test, and $(k+1)$-WL is at least as strong as $k$-WL.

## Proof sketch

Each refinement step refines because the new color contains the old one; a strictly finer partition of a finite set can occur at most $|V|^k$ times. Invariance is an induction on $t$.

## Depends on

- [$k$-dimensional Weisfeiler–Leman refinement](k-dimensional-weisfeiler-leman.md)

## Sources

- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992.
