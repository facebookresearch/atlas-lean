# The stable coloring is the coarsest equitable refinement

For every finite graph and initial coloring, the partition of the stable coloring is equitable and refines the initial partition, and it is the coarsest such partition: every equitable partition refining the initial partition refines the stable partition. Color refinement is isomorphism-invariant: if $\pi$ is an isomorphism from $G$ to $H$ mapping initial colors to initial colors, then $c_t^H(\pi v) = c_t^G(v)$ for all $t$ and $v$, so graphs with different stable color histograms are not isomorphic.

## Proof sketch

At stabilization the multiset of neighbour colors is a function of the color, which is equitability; conversely, by induction on $t$, every equitable partition refining $c_0$ refines $c_t$.

## Depends on

- [Color refinement and the stable coloring](color-refinement-stable-coloring.md)

## Sources

- M. Grohe, K. Kersting, M. Mladenov and E. Selman, "Dimension Reduction via Colour Refinement", Algorithms — ESA 2014, LNCS 8737, 505–516, 2014.
- N. Immerman and E. S. Lander, "Describing Graphs: A First-Order Approach to Graph Canonization", in Complexity Theory Retrospective, Springer, 59–81, 1990.
