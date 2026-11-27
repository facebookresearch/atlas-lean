# Color refinement and the stable coloring

For a finite simple graph $G = (V,E)$ and an initial coloring $c_0 : V \to C$, *color refinement* (1-dimensional Weisfeiler–Leman) computes $c_{t+1}(v) = \big(c_t(v), \{\!\{ c_t(u) : u \in N(v) \}\!\}\big)$. The partitions of $V$ induced by $c_0, c_1, \dots$ are successively finer, so they stabilize after at most $|V|$ rounds; the partition at stabilization is the *stable coloring*. A partition of $V$ is *equitable* if any two vertices in the same class have the same number of neighbours in each class.

## Depends on

- [Message-passing GNNs and 1-WL color refinement](../../../ComputerScience/machine-learning/supervised-learning/message-passing-gnns-and-1-wl-color-refinement.md)

## Sources

- M. Grohe, K. Kersting, M. Mladenov and E. Selman, "Dimension Reduction via Colour Refinement", Algorithms — ESA 2014, LNCS 8737, 505–516, 2014.
- N. Immerman and E. S. Lander, "Describing Graphs: A First-Order Approach to Graph Canonization", in Complexity Theory Retrospective, Springer, 59–81, 1990.
