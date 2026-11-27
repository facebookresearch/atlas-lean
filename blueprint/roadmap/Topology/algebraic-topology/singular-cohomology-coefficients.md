# Singular cohomology with coefficients in an abelian group

Let $X$ be a topological space and $G$ an abelian group. Let $(C_\bullet(X), \partial)$ be the singular chain complex of $X$.

- The group of *singular $n$-cochains* is $C^n(X; G) = \operatorname{Hom}(C_n(X), G)$, the abelian group of homomorphisms $C_n(X) \to G$.
- The *coboundary* $\delta\colon C^n(X; G) \to C^{n+1}(X; G)$ is the dual of $\partial_{n+1}$, given by $\delta\varphi = \varphi \circ \partial_{n+1}$. Since $\partial \circ \partial = 0$, also $\delta \circ \delta = 0$.

The *$n$-th singular cohomology group of $X$ with coefficients in $G$* is the quotient abelian group

$$H^n(X; G) = \ker\bigl(\delta\colon C^n(X;G) \to C^{n+1}(X;G)\bigr) \big/ \operatorname{im}\bigl(\delta\colon C^{n-1}(X;G) \to C^n(X;G)\bigr).$$

Here $C^{-1}(X; G) = 0$, so $H^0(X; G)$ is the kernel of $\delta$ on $C^0(X; G)$.

## Expansion

A good expansion of this node links each notion it is built from: images of group homomorphisms; the vanishing of the composite of two singular boundary maps; singular chain groups and their boundary maps.

## Depends on

- [Abelian group](../../GroupTheory/group-basics/abelian-group.md)
- [Topological space](../topological-spaces/topological-space.md)
- [Kernel of a homomorphism from a group](../../GroupTheory/group-basics/group-homomorphism-kernel.md)
- [Abelian group of additive homomorphisms into an abelian group](../../GroupTheory/semigroups-and-monoids/hom-group-abelian.md)
- [Quotient group by a normal subgroup](../../GroupTheory/group-basics/quotient-group.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Section 3.1.
