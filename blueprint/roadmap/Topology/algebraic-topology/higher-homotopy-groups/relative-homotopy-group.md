# Relative homotopy groups of a pair of spaces

Let $X$ be a topological space, $A \subseteq X$ a subspace, $x_0 \in A$ and $n \ge 1$. Let $D^n = \{x \in \mathbb{R}^n : \|x\| \le 1\}$ be the closed unit ball of the Euclidean space $\mathbb{R}^n$ and $S^{n-1} = \{x \in \mathbb{R}^n : \|x\| = 1\}$ its boundary sphere, both with the subspace topology of $\mathbb{R}^n$, and fix a basepoint $s_0 \in S^{n-1}$. The set $\pi_n(X, A, x_0)$ defined below is a pointed set; it is a group when $n \ge 2$, and an abelian group when $n \ge 3$.

A *map of triples* $f\colon (D^n, S^{n-1}, s_0) \to (X, A, x_0)$ is a continuous map $f\colon D^n \to X$ with $f(S^{n-1}) \subseteq A$ and $f(s_0) = x_0$. Two such maps are *homotopic* if some homotopy $F\colon D^n \times [0,1] \to X$ joins them with every $F(\cdot, t)$ a map of triples.

The *relative homotopy group* $\pi_n(X, A, x_0)$ (for $n = 1$, the relative homotopy set) is the set of homotopy classes of such maps, pointed by the class $0$ of the constant map at $x_0$.

For $n \ge 2$ the group operation is defined as follows. Write $I^n = [0,1]^n$ and $J^{n-1}$ for the closure of $\partial I^n \setminus (I^{n-1} \times \{0\})$. Fix a homeomorphism $I^n/J^{n-1} \cong D^n$ that sends the point $J^{n-1}/J^{n-1}$ to $s_0$ and the image of $\partial I^n$ onto $S^{n-1}$, and let $q\colon I^n \to D^n$ be its composite with the quotient map $I^n \to I^n/J^{n-1}$. Then $[f] + [g]$ is the class of the map of triples $h$ determined by

- $h(q(s)) = f(q(2s_1, s_2, \dots, s_n))$ for $s_1 \le 1/2$, and
- $h(q(s)) = g(q(2s_1 - 1, s_2, \dots, s_n))$ for $s_1 \ge 1/2$.

Both formulas give $x_0$ where $s_1 = 1/2$ and on all of $J^{n-1}$, so $h$ is well defined.

## Expansion

A good expansion of this node links each notion it is built from: homotopies of continuous maps.

## Depends on

- [Closed unit ball of $\mathbb{R}^n$](../../../Analysis/function-spaces/radial-sobolev-embedding/closed-unit-ball.md)
- [Group](../../../GroupTheory/group-basics/group.md)
- [Continuous map between topological spaces](../../topological-spaces/continuous-map.md)
- [Topological space](../../topological-spaces/topological-space.md)
- [Quotient map](../../topological-spaces/lattice-of-topologies-and-induced-topologies/quotient-map-topological.md)
- [Subspace topology](../../topological-spaces/lattice-of-topologies-and-induced-topologies/subspace-topology.md)

## Sources

- Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002, Section 4.1.
