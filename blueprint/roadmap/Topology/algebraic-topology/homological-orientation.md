# R-orientation of a topological manifold

Let $R$ be a commutative ring with identity and $M$ a topological $n$-manifold without boundary. For $A \subseteq M$, write $H_n(M \mid A; R)$ for the singular homology group $H_n(M, M \setminus A; R)$. For each $x \in M$ the $R$-module $H_n(M \mid x; R)$ is isomorphic to $R$. By a *generator* of it we mean an element that is a basis of it as an $R$-module, that is, an element $g$ for which $r \mapsto rg$ is an isomorphism $R \to H_n(M \mid x; R)$. An *$R$-orientation* of $M$ is a function $x \mapsto \mu_x$ assigning to each $x \in M$ a generator $\mu_x$ of $H_n(M \mid x; R)$, subject to the following local consistency condition. Each $x \in M$ has an open neighborhood $U$ with a homeomorphism $U \cong \mathbb{R}^n$, and an open ball $B \subseteq U$ of finite radius containing $x$ (a ball for the Euclidean metric carried over by this homeomorphism), such that for one element $\mu_B \in H_n(M \mid B; R)$, every $\mu_y$ with $y \in B$ is the image of $\mu_B$ under the map $H_n(M \mid B; R) \to H_n(M \mid y; R)$ induced by the inclusion of pairs. The manifold $M$ is *$R$-orientable* if it admits an $R$-orientation, and *orientable* if it is $\mathbb{Z}$-orientable.

## Expansion

A good expansion of this node links each notion it is built from: the local homology of a manifold at a point; the homomorphisms induced on relative homology by maps of pairs; relative singular homology with coefficients; topological manifolds.

## Depends on

- [Commutative ring with identity: a ring whose multiplication is commutative and has an identity element 1](../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Homeomorphism](../topological-spaces/homeomorphism.md)
- [Free module](../../LinearAlgebra/bases-and-dimension/free-module.md)
- [Open ball in a pseudometric space](../metric-spaces/metric-open-ball.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Section 3.3.
