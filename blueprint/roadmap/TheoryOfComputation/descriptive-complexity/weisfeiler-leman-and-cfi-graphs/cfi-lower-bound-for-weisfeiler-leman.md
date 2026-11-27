# Cai–Fürer–Immerman: $k$-WL and $C^{k+1}$ do not capture graph isomorphism

For every $k$ there are finite, non-isomorphic vertex-colored graphs $G_k, H_k$ (the even and odd CFI graphs over $K_{2k+4}$, or over any connected base graph of minimum degree at least $2$ and treewidth larger than $k$; Cai, Fürer and Immerman also remove the colors with small gadgets), with gadgets of size $2^{2k+2}+O(k)$ over $K_{2k+4}$ (constant size over a $3$-regular base graph of treewidth larger than $k$), that satisfy the same $C^{k+1}$ sentences, the same $\mathrm{FO}^{k+1}$ sentences, and are not distinguished by $k$-WL. Hence no fixed number of variables in counting logic (equivalently no fixed dimension of Weisfeiler–Leman) decides graph isomorphism, and, since the parity of the twist is computable in polynomial time while fixed-point logic with counting embeds into $\bigcup_k C^k_{\infty\omega}$, that logic does not capture polynomial time.

## Proof sketch

Duplicator survives the bijective $(k+1)$-pebble game by keeping the twist on an edge of the base graph away from all pebbled gadgets, moving it along paths that avoid the pebbled gadgets; this is the robber's escape in the cops-and-robber game on $B$ with $k+1$ cops, which exists exactly when $B$ has treewidth at least $k+1$ (CFI use base graphs without small separators). Each bijection she offers is then a partial isomorphism on the pebbles.

## Depends on

- [Cai–Fürer–Immerman graphs](cai-furer-immerman-graphs.md)
- [Finite-variable counting logics $C^k$ and $C^k_{\infty\omega}$](../finite-variable-logics/finite-variable-counting-logics.md)
- [$k$-dimensional Weisfeiler–Leman refinement](k-dimensional-weisfeiler-leman.md)

## Proof depends on

- [CFI graphs are classified by the parity of the twist](cfi-graphs-twist-parity-classification.md)
- [Cai–Fürer–Immerman: $k$-WL is equivalent to $(k+1)$-variable counting logic](cfi-k-wl-equivalent-to-counting-logic.md)
- [Bijective pebble games characterize counting logic $C^k$](../finite-variable-logics/bijective-games-characterize-counting-logic.md)

## Sources

- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992.
- A. Dawar and D. Richerby, "The Power of Counting Logics on Restricted Classes of Finite Structures", Computer Science Logic (CSL 2007), LNCS 4646, 84–98, 2007 (the treewidth form of the base-graph condition, for connected base graphs of minimum degree at least $2$).
