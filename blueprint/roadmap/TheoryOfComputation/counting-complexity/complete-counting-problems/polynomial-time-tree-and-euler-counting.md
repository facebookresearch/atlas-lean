# Counting spanning trees, arborescences and Eulerian circuits in polynomial time

The following counting functions are computable in polynomial time (counts output in binary): the number of spanning trees of a finite undirected multigraph (Kirchhoff's matrix-tree theorem: any cofactor of the Laplacian); the number of spanning in-arborescences rooted at a vertex of a digraph (Tutte's directed matrix-tree theorem); and the number of Eulerian circuits of a connected balanced multidigraph starting with a given arc, which by the BEST theorem equals $t_w(G)\prod_{v}(\deg^{+}(v)-1)!$ for the number $t_w(G)$ of arborescences rooted at any vertex $w$.

## Proof sketch

Each count is a determinant of an integer matrix of polynomial size times explicit factorials; determinants are computed exactly in polynomial time by fraction-free Gaussian elimination.

## Depends on

- [Kirchhoff's matrix-tree theorem](../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree.md)
- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Polynomial-time rational Gaussian elimination (Bareiss)](../../polynomial-time-problems/exact-algebraic-and-combinatorial-algorithms/bareiss-rational-gaussian-elimination.md)

## Sources

- Gustav Kirchhoff, "Ueber die Auflösung der Gleichungen, auf welche man bei der Untersuchung der linearen Vertheilung galvanischer Ströme geführt wird", Annalen der Physik und Chemie 148(12), 1847.
- T. van Aardenne-Ehrenfest and N. G. de Bruijn, "Circuits and trees in oriented linear graphs", Simon Stevin 28, 1951.
- W. T. Tutte, "The dissection of equilateral triangles into equilateral triangles", Mathematical Proceedings of the Cambridge Philosophical Society 44(4), 1948.
