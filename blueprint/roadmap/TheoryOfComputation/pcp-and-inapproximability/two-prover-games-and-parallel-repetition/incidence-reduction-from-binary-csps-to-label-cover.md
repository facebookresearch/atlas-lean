# Incidence reduction from binary CSPs to Label Cover

Given a loopless binary constraint graph $G$ over $\Sigma$ in which every constraint has at least one satisfying label pair, fix for each edge $e = (u, v)$ of $G$ (with its endpoints in the order its constraint reads them) a satisfying pair $p^*_e$. Form the Label Cover instance with left label set $\beta = \Sigma \times \Sigma$ and right label set $\gamma = \Sigma$ whose left vertices are the edges of $G$ and whose right vertices are the vertices of $G$, with an edge from $e = (u, v)$ to each of $u$ and $v$. For a left label $p \in \Sigma \times \Sigma$ let $\bar p = p$ if $p$ satisfies the constraint of $e$ and $\bar p = p^*_e$ otherwise; the projection on the edge to $u$ reads off the first coordinate of $\bar p$, and the projection on the edge to $v$ the second. This is computable in polynomial time, has no parallel edges, preserves satisfiability, and if $\mathrm{UNSAT}(G) \ge \delta$ then every labelling violates at least a $\delta/2$ fraction of the Label Cover edges.

## Proof sketch

Decode the right labels as a labelling $\sigma$ of $G$. A left label $p$ of $e$ acts through the satisfying pair $\bar p$, so if $\sigma$ violates the constraint of $e$ then $\bar p \ne (\sigma(u), \sigma(v))$ and at least one of the two Label Cover edges of $e$ is violated; there are $2|E(G)|$ Label Cover edges. A satisfying $\sigma$, with left labels $(\sigma(u), \sigma(v))$, satisfies every Label Cover edge, and a labelling satisfying every Label Cover edge decodes to a satisfying $\sigma$.

## Depends on

- [Label Cover (projection games)](label-cover-projection-games.md)
- [2CSP instances](../dinur-s-gap-amplification/cspinstance.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
