# Spanning-tree layouts give the layout hypothesis with A = 1

For every $\Delta\ge2$, every multigraph of maximum degree at most $\Delta$ has a layout of width at most $\beta_1(G)+O(\Delta\log|V|)$; in particular $\mathrm{LB}(\Delta,1)$ holds in every degree.

## Proof sketch

Order the vertices along a depth-first traversal of a spanning forest arranged so that each prefix cuts few tree edges (a centroid-style ordering cuts $O(\Delta\log|V|)$ tree edges); every cut non-tree edge is one of the $\beta_1$ edges outside the forest.

## Depends on

- [Layouts of multigraphs, cycle rank and the layout hypothesis](layouts-and-the-layout-hypothesis.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
