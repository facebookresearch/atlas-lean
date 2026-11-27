# Recognizing subclasses of higher-dimensional knot groups is algorithmically unsolvable

For the nested classes of groups of $n$-knots for $n \le 3$, of surface knots in $S^4$ and in simply connected $4$-manifolds, and of all finitely presented groups, membership of a finitely presented group from a larger class in a smaller one is undecidable whenever the larger class contains the $3$-knot groups.

Let $\mathcal{K}_n$ be the class of fundamental groups of complements of smooth $n$-spheres in $S^{n+2}$; let $\mathcal{S}$, respectively $\mathcal{M}$, be the class of fundamental groups of complements of closed orientable surfaces smoothly embedded in $S^4$, respectively in a simply connected $4$-manifold; and let $\mathcal{G}$ be the class of all finitely presented groups. Then $\mathcal{K}_0 \subsetneq \mathcal{K}_1 \subsetneq \mathcal{K}_2 \subsetneq \mathcal{K}_3 \subsetneq \mathcal{S} \subsetneq \mathcal{M} \subsetneq \mathcal{G}$, and $\mathcal{K}_0$ consists of the infinite cyclic group only.

**Theorem (González-Acuña–Gordon–Simon).** Let $\mathcal{A}$ and $\mathcal{B}$ be members of $\{\mathcal{K}_0, \mathcal{K}_1, \mathcal{K}_2, \mathcal{K}_3, \mathcal{S}, \mathcal{M}, \mathcal{G}\}$ with $\mathcal{B} \subsetneq \mathcal{A}$ and $\mathcal{A} \supseteq \mathcal{K}_3$. Then there is no algorithm that decides, given a finite presentation of a group $G$ in $\mathcal{A}$, whether $G$ is in $\mathcal{B}$.

Conventions: the input is promised to present a group in $\mathcal{A}$. The case $\mathcal{A} = \mathcal{K}_3$, $\mathcal{B} = \mathcal{K}_0$ says that one cannot decide whether a $3$-knot group is infinite cyclic, so the isomorphism problem for $\mathcal{K}_3$ and the classes containing it is unsolvable. For $\mathcal{A} = \mathcal{K}_1$, $\mathcal{B} = \mathcal{K}_0$ an algorithm exists by Haken's theorem, and the authors conjecture the theorem for $\mathcal{A} = \mathcal{K}_2$. The same paper shows that every finitely presented group embeds in a $3$-knot group, so there are $3$-knot groups with unsolvable word problem.

## Depends on

- [R-orientation of a topological manifold](../../algebraic-topology/homological-orientation.md)

## Proof depends on

None.

## Expansion

The groups in these classes have algebraic characterizations: by Kervaire, $\mathcal{K}_3$ consists of the finitely presented groups $G$ with $H_1(G) \cong \mathbb{Z}$, $H_2(G) = 0$ and an element whose normal closure is $G$ (Theorem 2.1 of the source), and Simon characterized $\mathcal{S}$ similarly, also through Wirtinger presentations (Theorems 2.2 and 2.3). For all pairs except $(\mathcal{A}, \mathcal{B}) = (\mathcal{G}, \mathcal{M})$, Section 3 uses what the authors call $(\mathcal{A}, \mathcal{B}, \mathcal{C})$-constructions to show that an algorithm for the recognition problem would decide triviality of finite presentations, which is undecidable. A key tool is a computable embedding of a finitely presented group $G$ into a perfect finitely presented group $P$ with $P = 1$ when $G = 1$ and with $H_2(P)$ infinite when $G \ne 1$ (Proposition 3.1 and Addendum 3.2). The remaining pair $(\mathcal{G}, \mathcal{M})$ is handled separately in Section 4.

## Sources

- F. González-Acuña, C. McA. Gordon and J. Simon, *Unsolvable problems about higher-dimensional knots and related groups*, Enseign. Math. (2) 56 (2010), no. 1, 143–171, https://doi.org/10.4171/LEM/56-1-5, read in the copy arXiv:0908.4009v1: the statement is Theorem 1.1 there, Kervaire's and Simon's characterizations are Theorems 2.1–2.3, the constructions are Proposition 3.1 and Addendum 3.2 with the proof in Sections 3 and 4, and the remarks on special cases and the embedding into $3$-knot groups are in its introduction.
