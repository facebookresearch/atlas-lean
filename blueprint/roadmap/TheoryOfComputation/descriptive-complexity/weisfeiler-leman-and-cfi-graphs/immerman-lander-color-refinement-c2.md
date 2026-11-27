# Immerman–Lander: color refinement characterizes two-variable counting logic $C^2$

Let $G, H$ be finite simple graphs, and run color refinement from the constant coloring jointly on $G \sqcup H$. If $G$ and $H$ have the same stable color histogram, then for vertices $v \in V(G)$, $w \in V(H)$: $v$ and $w$ receive the same stable color iff Duplicator wins the infinite bijective 2-pebble game from $(v, w)$ iff $v$ and $w$ satisfy the same $C^2$ formulas in one free variable. (Without equal histograms the pointed claim fails: for $G$ a single vertex and $H$ two isolated vertices all three vertices get the same stable color, yet $\exists^{\ge 2} y\, (y = y)$ separates them and no bijection exists.) For arbitrary $G$ and $H$, they have the same stable color histogram iff they satisfy the same $C^2$ sentences, iff Duplicator wins the bijective 2-pebble game from the empty position.

## Proof sketch

With one pebble resting on $v \mapsto w$, Duplicator must answer with a bijection carrying $v$ to $w$, neighbours of $v$ to neighbours of $w$ and previous-round colors to equal colors; such a bijection exists exactly when the refinement step gives equal colors. Combine with the bijective game characterization of $C^k$.

## Depends on

- [Color refinement and the stable coloring](color-refinement-stable-coloring.md)
- [Finite-variable counting logics $C^k$ and $C^k_{\infty\omega}$](../finite-variable-logics/finite-variable-counting-logics.md)
- [Hella's bijective $k$-pebble game](../finite-variable-logics/bijective-pebble-game.md)

## Proof depends on

- [Bijective pebble games characterize counting logic $C^k$](../finite-variable-logics/bijective-games-characterize-counting-logic.md)
- [The stable coloring is the coarsest equitable refinement](stable-coloring-coarsest-equitable-partition.md)

## Sources

- N. Immerman and E. S. Lander, "Describing Graphs: A First-Order Approach to Graph Canonization", in Complexity Theory Retrospective, Springer, 59–81, 1990.
- J.-Y. Cai, M. Fürer and N. Immerman, "An Optimal Lower Bound on the Number of Variables for Graph Identification", Combinatorica 12(4), 389–410, 1992.
- N. Immerman, Descriptive Complexity, Springer, 1999.
