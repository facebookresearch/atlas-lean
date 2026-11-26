# Cai–Fürer–Immerman: $k$-WL and $C^{k+1}$ do not capture graph isomorphism

For every $k$ there are finite, non-isomorphic graphs $G_k, H_k$ (the even and odd CFI graphs over $K_{2k+4}$, or over any base graph of treewidth larger than $k$), with gadgets of size $2^{2k+2}+O(k)$ over $K_{2k+4}$ (constant size over a $3$-regular base graph of treewidth larger than $k$), that satisfy the same $C^{k+1}$ sentences, the same $\mathrm{FO}^{k+1}$ sentences, and are not distinguished by $k$-WL. Hence no fixed number of variables in counting logic (equivalently no fixed dimension of Weisfeiler–Leman) decides graph isomorphism, and fixed-point logic with counting does not capture polynomial time.

## Proof sketch

Duplicator survives the bijective $(k+1)$-pebble game by keeping the twist on an edge of the base graph far from all pebbled gadgets; since the base graph remains connected after removing $k+1$ gadgets' worth of vertices (by its connectivity or treewidth), the twist can always be moved away from Spoiler's next move, giving a bijection that is a partial isomorphism on pebbles.

## Depends on

- [Cai–Fürer–Immerman graphs](cai-furer-immerman-graphs.md)
- [Finite-variable counting logics $C^k$ and $C^k_{\infty\omega}$](../finite-variable-logics/finite-variable-counting-logics.md)

## Proof depends on

- [CFI graphs are classified by the parity of the twist](cfi-graphs-twist-parity-classification.md)
- [Cai–Fürer–Immerman: $k$-WL is equivalent to $(k+1)$-variable counting logic](cfi-k-wl-equivalent-to-counting-logic.md)
- [Bijective pebble games characterize counting logic $C^k$](../finite-variable-logics/bijective-games-characterize-counting-logic.md)

## Sources

- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992.
