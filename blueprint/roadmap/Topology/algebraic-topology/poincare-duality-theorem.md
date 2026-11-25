# Poincaré duality: for a closed R-oriented n-manifold M, α ↦ [M] ⌢ α is an isomorphism H^k(M; R) → H_{n−k}(M; R)

Let $R$ be a commutative ring with identity and $M$ a closed (compact, without boundary) $n$-manifold with an $R$-orientation. Let $[M] \in H_n(M; R)$ be its fundamental class. Then for every $k$, the map $H^k(M; R) \to H_{n-k}(M; R)$, $\alpha \mapsto [M] \frown \alpha$, given by the cap product, is an isomorphism of $R$-modules.

## Proof sketch

Apply Poincaré duality for noncompact manifolds to $M$. Since $M$ is compact, $M$ itself is the largest member of the directed set of compact subsets. So $H^k_c(M; R) = H^k(M, \emptyset; R) = H^k(M; R)$, and the class $\mu_M$ is the fundamental class $[M]$. Hence the duality map there is exactly $\alpha \mapsto [M] \frown \alpha$, which is therefore an isomorphism.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: Singular cohomology with compact supports H^k\_c(X; G); Poincaré duality for manifolds that are not necessarily compact; Singular homology H\_n(X; G) with coefficients in an abelian group G.

## Depends on

- [Commutative ring with identity: a ring whose multiplication is commutative and has an identity element 1](../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Cap product of singular homology with singular cohomology](cap-product.md)
- [Closed manifold, not required to be connected](../manifolds-geometric-topology/closed-topological-manifold.md)
- [Fundamental class of a closed R-oriented manifold](fundamental-class.md)
- [R-orientation of a topological manifold](homological-orientation.md)
- [Singular cohomology with coefficients in an abelian group](singular-cohomology-coefficients.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Theorems 3.30 and 3.35.
