# Incidence reduction from binary CSPs to Label Cover

Given a loopless binary constraint graph $G$ over $\Sigma$, form the Label Cover instance whose left vertices are the edges of $G$ (labelled by satisfying label pairs of that constraint) and whose right vertices are the vertices of $G$ (labelled in $\Sigma$), with an edge from $e = \{u,v\}$ to each endpoint whose projection reads off the corresponding coordinate. This is computable in polynomial time, has no parallel edges, preserves satisfiability, and if $\mathrm{UNSAT}(G) \ge \delta$ then every labelling violates at least a $\delta/2$ fraction of the Label Cover edges.

## Proof sketch

Decode the right labels as a labelling of $G$; each edge of $G$ violated by it has a left label (a satisfying pair) that disagrees with at least one of its two endpoints, so at least one of the two corresponding Label Cover edges is violated.

## Depends on

- [Label Cover (projection games)](label-cover-projection-games.md)
- [2CSP instances](../dinur-s-gap-amplification/cspinstance.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
