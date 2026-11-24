# Long exact sequence of homotopy groups of a pair

Let $X$ be a topological space, $A \subseteq X$ a subspace and $x_0 \in A$. The following conventions are used.

- For $k \ge 1$, $\pi_k(Y, y_0)$ is the homotopy group of based maps $(S^k, s_0) \to (Y, y_0)$. The relative homotopy set $\pi_k(X, A, x_0)$ is the set of homotopy classes of maps of triples $(D^k, S^{k-1}, s_0) \to (X, A, x_0)$, pointed by the class of the constant map; it is a group when $k \ge 2$, and an abelian group when $k \ge 3$.
- $\pi_0(Y, y_0)$ is the set of path components of $Y$, pointed by the component of $y_0$.
- $i_*$ is induced by the inclusion $A \hookrightarrow X$.
- $j_*[g] = [g \circ c]$, where $c\colon D^n \to S^n$ is a fixed map that sends $S^{n-1}$ to $s_0$ and induces a homeomorphism $D^n/S^{n-1} \cong S^n$. Here $g \circ c$ is regarded as a map of triples $(D^n, S^{n-1}, s_0) \to (X, A, x_0)$.
- $\partial$ sends the class of a map of triples $f\colon (D^n, S^{n-1}, s_0) \to (X, A, x_0)$ to the class of $f|_{S^{n-1}}\colon (S^{n-1}, s_0) \to (A, x_0)$. For $n = 1$, where $S^0 = \{s_0, -s_0\}$, this is the path component of $f(-s_0)$ in $A$.

Then the sequence

$$\cdots \to \pi_n(A, x_0) \xrightarrow{i_*} \pi_n(X, x_0) \xrightarrow{j_*} \pi_n(X, A, x_0) \xrightarrow{\partial} \pi_{n-1}(A, x_0) \to \cdots \to \pi_1(X, A, x_0) \xrightarrow{\partial} \pi_0(A, x_0) \xrightarrow{i_*} \pi_0(X, x_0)$$

is exact at each term that has both an incoming and an outgoing arrow: there, the image of the incoming map equals the preimage of the basepoint under the outgoing map. At and below $\pi_1(X, A, x_0)$ these are maps of pointed sets, and nothing is claimed at the last term $\pi_0(X, x_0)$.

## Proof sketch

All three maps respect homotopies. At $\pi_n(X, x_0)$, $n \ge 1$: $j_* i_*$ is trivial, since a map of triples with image in $A$ represents zero by the compression criterion. Conversely, if $j_*[g] = 0$, the compression criterion homotopes $g \circ c$ rel $S^{n-1}$ to a map into $A$. That map is constant on $S^{n-1}$, so it equals $i \circ h \circ c$ for a based map $h\colon (S^n, s_0) \to (A, x_0)$, and the homotopy, being constant on $S^{n-1}$, descends through $c$ to a based homotopy $i \circ h \simeq_* g$ in $X$. So $i_*[h] = [g]$, and $[g] \in \operatorname{im} i_*$. At $\pi_n(X, A, x_0)$ with $n \ge 2$: $\partial j_*$ is trivial. If $\partial[f] = 0$, the homotopy extension property of $(D^n, S^{n-1})$ extends a based nullhomotopy of $f|_{S^{n-1}}$ in $A$ to a homotopy of triples from $f$ to a map constant on $S^{n-1}$, which factors through $c$. At $\pi_{n-1}(A, x_0)$ with $n \ge 2$: by the extension criterion in degree $n - 1 \ge 1$, $i_*[h] = 0$ if and only if $h$ extends over $D^n$ in $X$, that is, if and only if $[h] \in \operatorname{im} \partial$. The two lowest terms with two arrows, where the maps are only pointed maps, are checked with paths. A map of triples $(D^1, S^0, s_0) \to (X, A, x_0)$ is a path $\gamma$ in $X$ from the point $a = \gamma(-s_0)$ of $A$ to $x_0$, and $\partial[\gamma]$ is the path component of $a$ in $A$. At $\pi_1(X, A, x_0)$: a loop at $x_0$ is such a path with $a = x_0$, so $\partial j_*$ is trivial. Conversely, if $a$ lies in the path component of $x_0$ in $A$, join $x_0$ to $a$ by a path $\delta$ in $A$; sliding the free endpoint back along $\delta$ is a homotopy of triples from $\gamma$ to the loop $\delta \cdot \gamma$ at $x_0$, so $[\gamma] = j_*[\delta \cdot \gamma]$. At $\pi_0(A, x_0)$: $\gamma$ joins $a$ to $x_0$ in $X$, so $i_* \partial$ is trivial. Conversely, if the path component of a point $a \in A$ maps to the path component of $x_0$ in $X$, a path in $X$ from $a$ to $x_0$ is a map of triples whose class $\partial$ sends to the component of $a$. So the path components of $A$ reached by $\partial$ are exactly those whose image in $\pi_0(X, x_0)$ is the component of $x_0$.

## Expansion

A good expansion of this node links each prerequisite of its statement and proof: the homotopy extension property of CW pairs; the compression criterion for relative homotopy classes; the criterion that a based map of a sphere is trivial in homotopy exactly when it extends over the disc; exact sequences of pointed sets; homotopy groups; homotopy groups as based homotopy classes of maps of spheres; the homomorphisms induced on homotopy groups by based maps.

## Depends on

- [Topological space](../../topological-spaces/topological-space.md)
- [Relative homotopy groups of a pair of spaces](relative-homotopy-group.md)
- [Path component of a point](../../general-topology/path-component.md)
- [Quotient map](../../topological-spaces/lattice-of-topologies-and-induced-topologies/quotient-map-topological.md)
- [Subspace topology](../../topological-spaces/lattice-of-topologies-and-induced-topologies/subspace-topology.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Theorem 4.3.
