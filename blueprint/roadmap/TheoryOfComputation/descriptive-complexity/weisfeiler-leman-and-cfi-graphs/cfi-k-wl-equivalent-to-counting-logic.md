# Cai–Fürer–Immerman: $k$-WL is equivalent to $(k+1)$-variable counting logic

For every $k \ge 1$, finite simple graphs $G, H$ and $k$-tuples $\bar u, \bar v$: $k$-WL assigns $\bar u$ and $\bar v$ the same stable color iff Duplicator wins the infinite bijective $(k+1)$-pebble game from the position pebbling $\bar u, \bar v$ on the first $k$ pebbles, iff $\bar u, \bar v$ satisfy the same $C^{k+1}$ formulas. In particular $G$ and $H$ are not distinguished by $k$-WL iff they satisfy the same $C^{k+1}$ sentences.

## Proof sketch

A $k$-WL refinement step corresponds to one round of the bijective $(k+1)$-pebble game: Duplicator's bijection $w \mapsto w'$ must preserve the tuple of colors of all $k$ substituted tuples and the atomic type of $\bar u w$, which is exactly equality of the multisets in the refinement step. Induction on rounds and stabilization finish the proof.

## Depends on

- [$k$-dimensional Weisfeiler–Leman refinement](k-dimensional-weisfeiler-leman.md)
- [Finite-variable counting logics $C^k$ and $C^k_{\infty\omega}$](../finite-variable-logics/finite-variable-counting-logics.md)
- [Hella's bijective $k$-pebble game](../finite-variable-logics/bijective-pebble-game.md)

## Proof depends on

- [Bijective pebble games characterize counting logic $C^k$](../finite-variable-logics/bijective-games-characterize-counting-logic.md)
- [Stabilization and isomorphism invariance of $k$-WL](k-wl-stabilization-and-invariance.md)

## Sources

- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992.
