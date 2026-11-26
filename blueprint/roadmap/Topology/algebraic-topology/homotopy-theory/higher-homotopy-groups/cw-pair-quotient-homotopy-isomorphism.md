# Homotopy groups of a connected CW pair and of its quotient

Let $(X, A)$ be a CW pair and let $r, s \ge 0$ be integers. Suppose $A$ is $s$-connected: $A$ is nonempty and path-connected, and $\pi_i(A, a) = 0$ for every $a \in A$ and every $1 \le i \le s$. Suppose the pair $(X, A)$ is $r$-connected: every path component of $X$ meets $A$, and for every $x_0 \in A$ and every $1 \le i \le r$ the relative homotopy set $\pi_i(X, A, x_0)$ consists only of its distinguished element.

Fix $x_0 \in A$. Let $q\colon X \to X/A$ be the quotient map onto the CW complex $X/A$, collapsing $A$ to the point $*$. Then $q$ is a map of triples $(X, A, x_0) \to (X/A, *, *)$. Compose the induced map with the canonical identification $\pi_i(X/A, *, *) = \pi_i(X/A, *)$, under which a map of triples $(D^i, S^{i-1}, s_0) \to (X/A, *, *)$, being constant on $S^{i-1}$, is read as a based map of $D^i/S^{i-1} \cong S^i$. This gives

$$q_*\colon \pi_i(X, A, x_0) \to \pi_i(X/A, *).$$

For $1 \le i \le r + s$ this map is a bijection: a bijection of pointed sets for $i = 1$ and a group isomorphism for $i \ge 2$. For $i = r + s + 1$ it is surjective.

## Proof sketch

Form $X \cup CA$ by attaching the cone on $A$. It is a CW complex, and $X$ and $CA$ are subcomplexes meeting in the nonempty path-connected subcomplex $A$. Since $CA$ is contractible, the long exact sequence of the pair $(CA, A)$, read with pointed sets in the lowest degrees, shows that $(CA, A)$ is $(s+1)$-connected. Homotopy excision then makes $\pi_i(X, A) \to \pi_i(X \cup CA, CA)$ a bijection for $1 \le i \le r + s$, of pointed sets for $i = 1$ and of groups for $i \ge 2$, and a surjection for $i = r + s + 1$. The long exact sequence of $(X \cup CA, CA)$, with $CA$ contractible, identifies the target with $\pi_i(X \cup CA)$. Collapsing the contractible subcomplex $CA$ is a homotopy equivalence $X \cup CA \to X/A$, which induces isomorphisms on homotopy groups. These maps compose to $q_*$.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: the contractibility of cones; the fact that collapsing a contractible subcomplex is a homotopy equivalence; the isomorphisms induced on homotopy groups by homotopy equivalences; the homotopy excision theorem; the quotient of a CW complex by a subcomplex; subcomplexes of CW complexes; homotopy groups; n-connected spaces; the maps induced on relative homotopy groups by maps of pairs.

## Depends on

- [n-connected pair of spaces](n-connected-pair.md)
- [Relative homotopy groups of a pair of spaces](relative-homotopy-group.md)

## Proof depends on

- [Long exact sequence of homotopy groups of a pair](homotopy-les-pair.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Proposition 4.28.
