# The some-but-not-all-colours function of an edge-coloured cubic graph

Let $G=(V,E)$ be a cubic graph with a proper $3$-edge-colouring $c:E\to\{1,2,3\}$. The variables are the vertices: an input $x\in\{0,1\}^V$ selects the vertex set $X=\{v:x_v=1\}$. The function $f_G$ is $1$ iff the subgraph induced by $X$ contains at least one edge and the edges it contains use at most two of the three colours.

## Depends on

- [Negation normal form circuits, DNNF and d-DNNF](nnf-dnnf-and-d-dnnf.md)

## Sources

- Marcelo Arenas, Oliver Broadrick, Vincent Liew, Guy Van den Broeck, "d-DNNF is Not Polynomially Closed Under Negation", STOC 2027 submission 1318, 2026.
