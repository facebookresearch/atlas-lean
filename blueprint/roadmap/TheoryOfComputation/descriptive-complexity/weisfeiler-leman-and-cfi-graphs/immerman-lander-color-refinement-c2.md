# Immerman–Lander: color refinement characterizes two-variable counting logic $C^2$

For finite simple graphs $G, H$ and vertices $v \in V(G)$, $w \in V(H)$: color refinement started from the constant coloring assigns $v$ and $w$ the same stable color (computed jointly on $G \sqcup H$) iff Duplicator wins the infinite bijective 2-pebble game from $(v, w)$ iff $v$ and $w$ satisfy the same $C^2$ formulas. Likewise $G$ and $H$ have the same stable color histogram iff they satisfy the same $C^2$ sentences, iff Duplicator wins the bijective 2-pebble game from the empty position.

## Proof sketch

With one pebble resting on $v \mapsto w$, Duplicator must answer with a bijection carrying $v$ to $w$, neighbours of $v$ to neighbours of $w$ and previous-round colors to equal colors; such a bijection exists exactly when the refinement step gives equal colors. Combine with the bijective game characterization of $C^k$.

## Depends on

- [Color refinement and the stable coloring](color-refinement-stable-coloring.md)
- [Finite-variable counting logics $C^k$ and $C^k_{\infty\omega}$](../finite-variable-logics/finite-variable-counting-logics.md)

## Proof depends on

- [Bijective pebble games characterize counting logic $C^k$](../finite-variable-logics/bijective-games-characterize-counting-logic.md)
- [The stable coloring is the coarsest equitable refinement](stable-coloring-coarsest-equitable-partition.md)

## Sources

- N. Immerman and E. S. Lander, "Describing Graphs: A First-Order Approach to Graph Canonization", in Complexity Theory Retrospective, Springer, 59–81, 1990.
- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992.
- N. Immerman, Descriptive Complexity, Springer, 1999.
