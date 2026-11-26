# Planar Boolean CSP

The *incidence graph* of a CSP instance is the bipartite graph between its variables and its constraints with an edge for every argument position (a variable occurring twice in a scope gives two parallel edges). An instance is *planar* if its incidence graph has a plane embedding in which, around every constraint vertex, the edges appear in the cyclic order of the constraint's argument positions. $\mathrm{PlanarCSP}(\Gamma)$ is $\mathrm{CSP}(\Gamma)$ restricted to planar instances.

## Depends on

- [Boolean constraint languages and CSP(Γ)](../../boolean-constraint-satisfaction/polymorphisms-of-boolean-relations/boolean-constraint-languages.md)
- [Straight-line planar graph](../../../../GraphTheory/planar-graphs-and-minors/straight-line-planar-drawings/is-planar.md)

## Sources

- Z. Dvořák and M. Kupec, "On Planar Boolean CSP", Automata, Languages, and Programming — ICALP 2015, Part I, LNCS 9134, 432–443, 2015.
- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019.
