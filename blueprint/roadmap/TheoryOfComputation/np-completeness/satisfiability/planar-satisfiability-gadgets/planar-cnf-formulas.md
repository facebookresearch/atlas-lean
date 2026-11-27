# Planar CNF formulas

The *variable–clause incidence graph* of a CNF formula $\varphi$ is the bipartite graph with a vertex for every variable and every clause of $\varphi$, and an edge between $x$ and $C$ whenever $x$ or $\neg x$ occurs in $C$. The formula is *planar* if this graph is planar. Lichtenstein's original definition also adds a cycle through all variable vertices to the graph; planar 3-SAT is NP-complete under both definitions, and the definition here is the one of Hunt, Marathe, Radhakrishnan and Stearns. Planar 3-SAT asks whether a planar CNF formula with clauses of at most three literals is satisfiable.

## Depends on

- [CNF formula](../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)
- [Straight-line planar graph](../../../../GraphTheory/planar-graphs-and-minors/straight-line-planar-drawings/is-planar.md)

## Sources

- D. Lichtenstein, "Planar Formulae and Their Uses", SIAM Journal on Computing 11(2), 329–343, 1982.
- H. B. Hunt III, M. V. Marathe, V. Radhakrishnan and R. E. Stearns, "The Complexity of Planar Counting Problems", SIAM Journal on Computing 27(4), 1142–1167, 1998, Definition 2.8.
