# A closed connected nonorientable n-manifold M has H_n(M; Z) = 0

Let $M$ be a closed connected topological $n$-manifold that is not $\mathbb{Z}$-orientable. Then $H_n(M; \mathbb{Z}) = 0$.

## Proof sketch

Since $M$ is compact, the lemma on the homology of an $n$-manifold relative to the complement of a compact set (with $A = M$) shows that a class $\alpha \in H_n(M; \mathbb{Z})$ is determined by its locally consistent family of restrictions $\alpha_x \in H_n(M \mid x; \mathbb{Z}) \cong \mathbb{Z}$. Local consistency makes the order $k_x \ge 0$ of divisibility of $\alpha_x$ locally constant, so it is constant by connectedness. If $\alpha \neq 0$, then $k \ge 1$. Since $\mathbb{Z}$ is torsion-free, $\alpha_x = k\mu_x$ for a unique generator $\mu_x$, and these $\mu_x$ are locally consistent. This gives a $\mathbb{Z}$-orientation, a contradiction.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: the homology of a manifold relative to the complement of a compact set; singular homology.

## Depends on

- [Closed manifold, not required to be connected](../manifolds-geometric-topology/closed-topological-manifold.md)
- [R-orientation of a topological manifold](homological-orientation.md)
- [Connectedness in the sense of Hausdorff](../../GroupTheory/profinite-and-topological-groups/arcwise-connectedness-of-metric-groups/is-hausdorff-connected.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Theorem 3.26(b).
