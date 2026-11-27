# The homology of a good pair is the reduced homology of its quotient

Let $(X, A)$ be a good pair: $A$ is a nonempty closed subspace of the topological space $X$ that is a deformation retract of some neighborhood of $A$ in $X$. Let $q\colon X \to X/A$ be the quotient map collapsing $A$ to a point. Singular homology has integer coefficients. Then for every $n$, the homomorphism $q_*\colon H_n(X, A) \to H_n(X/A, A/A)$ induced by $q$ as a map of pairs is an isomorphism, and composing it with the isomorphism $H_n(X/A, A/A) \cong \tilde H_n(X/A)$ from the reduced long exact sequence of the pair $(X/A, A/A)$ gives $H_n(X, A) \cong \tilde H_n(X/A)$.

## Proof sketch

Let $V$ be a neighborhood of $A$ that deformation retracts onto $A$; then $A \subseteq \operatorname{int} V$. The inclusion $A \hookrightarrow V$ is a homotopy equivalence, so homotopy invariance and the long exact sequence of the pair $(V, A)$ give $H_n(V, A) = 0$, and the long exact sequence of the triple $(X, V, A)$ makes the map $H_n(X, A) \to H_n(X, V)$ induced by inclusion an isomorphism. The same holds for the triple $(X/A, V/A, A/A)$: the deformation retraction descends to $V/A$, because $q$ restricted to the saturated set $V$ is a quotient map onto $V/A$ ($A$ being closed) and the product of a quotient map with the identity of $[0,1]$ is a quotient map. Excision of the closed set $A \subseteq \operatorname{int} V$ gives $H_n(X - A, V - A) \cong H_n(X, V)$, and excision of the closed point $A/A \subseteq \operatorname{int}(V/A)$ gives the analogous isomorphism in $X/A$. The restriction of $q$ to the open saturated set $X - A$ is a homeomorphism onto $X/A - A/A$ carrying $V - A$ onto $V/A - A/A$, so it induces an isomorphism $H_n(X - A, V - A) \cong H_n(X/A - A/A, V/A - A/A)$. These isomorphisms fit into the commutative diagram of maps of pairs induced by $q$, so by functoriality of relative homology $q_*\colon H_n(X, A) \to H_n(X/A, A/A)$ is an isomorphism. The reduced long exact sequence of $(X/A, A/A)$, with the reduced homology of the point $A/A$ vanishing, gives the last identification.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: the excision theorem; the homotopy invariance of singular homology; the long exact sequence of a triple; restrictions of quotient maps to open saturated subsets; products of quotient maps with locally compact Hausdorff spaces; the functoriality of the homomorphisms induced on relative homology; good pairs; reduced singular homology; the long exact sequence of reduced homology of a pair; the homomorphisms induced on relative homology by maps of pairs.

## Depends on

- [Relative singular homology of a pair of spaces](relative-homology.md)
- [Coinduced topology and the quotient topology](../../topological-spaces/lattice-of-topologies-and-induced-topologies/quotient-topology.md)

## Proof depends on

- [A contractible space has trivial reduced singular homology](contractible-reduced-homology-vanishes.md)
- [Long exact sequence of a pair in singular homology](homology-long-exact-sequence-pair.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Proposition 2.22.
