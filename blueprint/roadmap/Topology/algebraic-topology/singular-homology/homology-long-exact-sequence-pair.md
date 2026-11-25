# Long exact sequence of a pair in singular homology

Let $X$ be a topological space and $A \subseteq X$ a subspace, with inclusion $i\colon A \hookrightarrow X$. Singular homology here has integer coefficients and is zero in negative degrees. There is an exact sequence of singular homology groups

$$\cdots \to H_n(A) \xrightarrow{i_*} H_n(X) \xrightarrow{j_*} H_n(X, A) \xrightarrow{\delta} H_{n-1}(A) \xrightarrow{i_*} H_{n-1}(X) \to \cdots \to H_0(X, A) \to 0,$$

where $j_*$ is induced by the quotient chain map $C_\bullet(X) \to C_\bullet(X)/C_\bullet(A)$, and the connecting homomorphism $\delta$ sends the class of a relative cycle represented by $x \in C_n(X)$ to the class of $\partial x \in C_{n-1}(A)$.

## Proof sketch

The chain map induced by the inclusion is injective, and the quotient map is surjective with kernel $C_\bullet(A)$, so $0 \to C_\bullet(A) \to C_\bullet(X) \to C_\bullet(X)/C_\bullet(A) \to 0$ is a short exact sequence of chain complexes. The long exact homology sequence of a short exact sequence of chain complexes gives the stated exact sequence, its connecting homomorphism being described by the same diagram chase as stated. The sequence ends with $H_0(X, A) \to 0$ because all groups in negative degree vanish.

## Expansion

A good expansion identifies $C_\bullet(X)/C_\bullet(A)$ with the cokernel of the chain map induced by the inclusion $\operatorname{Sing}(A) \to \operatorname{Sing}(X)$, as for relative homology, and transports $i_*$, $j_*$ and the connecting homomorphism of the short exact sequence of chain complexes along this identification. It checks that the connecting homomorphism is given by the lift-and-boundary formula of the statement: lift a relative cycle to $x \in C_n(X)$ and take the class of $\partial x \in C_{n-1}(A)$. It then splices the exactness at $H_n(A)$, $H_n(X)$ and $H_n(X, A)$ into the displayed sequence, ending with the surjection $j_*\colon H_0(X) \to H_0(X, A)$. A good expansion also links each prerequisite of its statement and proof: the long exact homology sequence of a short exact sequence of chain complexes; short exact sequences of chain complexes; exact sequences of groups; the maps induced on singular chains and homology by a continuous map.

## Depends on

- [Integral singular homology](../hurewicz-theorem/integral-homology.md)
- [Topological space](../../topological-spaces/topological-space.md)
- [Relative singular homology of a pair of spaces](relative-homology.md)
- [Subspace topology](../../topological-spaces/lattice-of-topologies-and-induced-topologies/subspace-topology.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Section 2.1, Theorem 2.16 and the long exact sequence of a pair that follows it.
