# Primal graph of a CSP instance

The *primal graph* (Gaifman graph) of a CSP instance $F$ has the variables of $F$ as vertices and an edge between distinct variables whenever they occur together in the scope of some constraint. Every scope is a clique of the primal graph, so for every tree decomposition of the primal graph each scope is contained in some bag. The *treewidth* of $F$ is the treewidth of its primal graph.

## Depends on

- [Finite-domain constraint satisfaction problems](finite-domain-constraint-satisfaction.md)
- [Tree-decomposition](../../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)
- [Gaifman graphs, distance and neighborhoods](../../../descriptive-complexity/hanf-and-gaifman-locality/gaifman-graphs-and-neighborhoods.md)

## Sources

- M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, Parameterized Algorithms, Springer, 2015.
