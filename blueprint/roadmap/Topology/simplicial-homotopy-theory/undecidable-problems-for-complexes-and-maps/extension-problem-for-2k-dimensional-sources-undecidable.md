# Extendability of maps into (k−1)-connected targets is undecidable when the source has dimension 2k

For each $k \ge 2$, deciding whether a simplicial map from a subcomplex $A \subseteq X$ to a $(k-1)$-connected complex $Y$ extends continuously to $X$ is undecidable when $\dim X = 2k$, even with the target fixed or with the pair $(X, A)$ fixed; it is decidable when $\dim X \le 2k - 1$.

The *extension problem* takes as input finite simplicial complexes $A \subseteq X$ and $Y$ and a simplicial map $f : A \to Y$, and asks whether there is a continuous map $\bar{f} : X \to Y$ with $\bar{f}|_A = f$. A space is $(k-1)$-*connected* if its homotopy groups $\pi_i$ vanish for $i \le k - 1$.

**Theorem (Čadek–Krčál–Matoušek–Vokřínek–Wagner).** Let $k \ge 2$ be fixed.

1. *Fixed target.* There is a fixed $(k-1)$-connected finite simplicial complex $Y = Y_k$ such that no algorithm decides, for given finite simplicial complexes $A \subseteq X$ with $\dim X = 2k$ and a simplicial map $f : A \to Y$, whether $f$ extends to a continuous map $X \to Y$. For $k$ even, $Y_k$ can be taken to be the sphere $S^k$.
2. *Fixed source.* There are fixed finite simplicial complexes $A = A_k \subseteq X = X_k$ with $\dim X = 2k$ such that no algorithm decides, for a given $(k-1)$-connected finite simplicial complex $Y$ and a simplicial map $f : A \to Y$, whether $f$ extends to a continuous map $X \to Y$.

Conventions: by companion results of the same group of authors, for $(k-1)$-connected $Y$ the extension problem is decidable when $\dim X \le 2k - 1$, and in polynomial time for fixed $k$, so the dimension bound $2k$ is sharp.

## Depends on

- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Topological space](../../topological-spaces/topological-space.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof converts a system of quadratic Diophantine equations, whose solvability is undecidable by the negative solution of Hilbert's tenth problem (Matiyasevich, building on Davis, Putnam and Robinson), into an instance of the extension problem. In the simplest case, the fixed-target version with $k$ even and $Y = S^k$, the space $X$ is homotopy equivalent to a wedge of $k$-spheres and $A$ is a wedge of $(2k-1)$-spheres. A map $X \to S^k$ is determined up to homotopy by the degrees $x_1, \dots, x_r$ of its restrictions to the $k$-spheres, and $f$ is specified by integers $b_q$ such that its restriction to the $q$-th sphere of $A$ is $b_q [\iota, \iota]$, where the Whitehead square $[\iota, \iota]$ has infinite order in $\pi_{2k-1}(S^k)$. The pair $(X, A)$ is built so that the extension given by $x$ restricts on the $q$-th sphere of $A$ to $\sum_{i<j} a^{(q)}_{ij} x_i x_j [\iota, \iota]$, so an extension exists exactly when the quadratic system $\sum_{i<j} a^{(q)}_{ij} x_i x_j = b_q$ is solvable. The constructions are carried out with simplicial sets and converted to simplicial complexes by subdivision; the fixed-source version encodes the equations in $f$ and $Y$ instead.

## Sources

- Martin Čadek, Marek Krčál, Jiří Matoušek, Lukáš Vokřínek and Uli Wagner, *Extendability of continuous maps is undecidable*, Discrete Comput. Geom. 51 (2014), no. 1, 24–66, https://doi.org/10.1007/s00454-013-9551-8, read in the copy arXiv:1302.2370v1: the statement is Theorem 1.1 there, the decidable range is recalled in its abstract and introduction, and the outline of the proof follows that theorem in Section 1.
