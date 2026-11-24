# Relative singular homology of a pair of spaces

Let $X$ be a topological space and $A \subseteq X$ a subspace. The chain map induced by the inclusion $A \hookrightarrow X$ identifies the singular chain complex $C_\bullet(A)$ with a subcomplex of $C_\bullet(X)$: each $C_n(A)$ is the subgroup of $C_n(X)$ spanned by the singular simplices with image in $A$, and $\partial$ maps $C_n(A)$ into $C_{n-1}(A)$. Hence $\partial$ induces boundary maps $C_n(X)/C_n(A) \to C_{n-1}(X)/C_{n-1}(A)$, giving the quotient chain complex $C_\bullet(X, A) = C_\bullet(X)/C_\bullet(A)$. The *relative homology groups* $H_n(X, A)$, with integer coefficients, are the homology groups of $C_\bullet(X, A)$.

## Expansion

A good expansion obtains $C_\bullet(X, A)$ as the relative chain complex of the simplicial pair given by the inclusion of singular simplicial sets $\operatorname{Sing}(A) \to \operatorname{Sing}(X)$, the cokernel of the induced chain map $C_\bullet(A) \to C_\bullet(X)$, which is injective in each degree. It identifies the cokernel in degree $n$ with the quotient group $C_n(X)/C_n(A)$, the cokernel projection with the quotient map, and the induced differential with the boundary map induced by $\partial$; the relative homology groups are the homology groups of this cokernel complex. A good expansion also links each notion it is built from: the homology of a chain complex; the maps induced on singular chains and homology by a continuous map; quotient chain complexes; singular chain groups and their boundary maps.

## Depends on

- [Topological space](../../topological-spaces/topological-space.md)
- [Subspace topology](../../topological-spaces/lattice-of-topologies-and-induced-topologies/subspace-topology.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Section 2.1.
