# CFI graphs are classified by the parity of the twist

For a connected base graph $B$ (in particular the complete graph $K_m$) and twists $t, t'$, the vertex-colored CFI graphs $X(B,t)$ and $X(B,t')$ are isomorphic (by a color-preserving isomorphism) if and only if $\sum_{e} t(e) = \sum_e t'(e)$ in $\mathbb{F}_2$. Hence the even and odd CFI graphs over $B$ are non-isomorphic, while any two twists of the same parity give isomorphic graphs.

## Proof sketch

Swapping the two vertices $a_{v,e}^0, a_{v,e}^1$ at both ends of an edge, combined with adjusting middle vertices, moves a twist along paths, so only the total parity matters. Conversely the parity is an isomorphism invariant: a color-preserving isomorphism maps each gadget to itself, acts on it by swapping the pairs $a_{v,e}^0, a_{v,e}^1$ for an even set of edges $e$ at $v$, and so changes the twist by a coboundary, whose total is even.

## Depends on

- [Cai–Fürer–Immerman graphs](cai-furer-immerman-graphs.md)

## Sources

- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992.
