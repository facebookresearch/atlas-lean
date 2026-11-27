# Retractability onto a subdivided sphere or wedge of two spheres is undecidable

For every fixed $l \ge 2$ there is no algorithm that decides, for a finite $2l$-dimensional simplicial complex $X$ containing a subdivision of $Y_l$ (the $l$-sphere for even $l$, a wedge of two $l$-spheres for odd $l$), whether the identity of $Y_l$ extends to a PL map $X \to Y_l$.

Let $l \ge 2$. Let $Y_l = S^l$ if $l$ is even and $Y_l = S^l \vee S^l$, the wedge of two $l$-spheres, if $l$ is odd. Here $S^l$ is the boundary of the $(l+1)$-simplex as a simplicial complex. A *PL map* between finite simplicial complexes is a simplicial map between subdivisions of them; for $V^d_m = S^d_1 \vee \dots \vee S^d_m$, the wedge of $m$ copies of $S^d$, maps are given as simplicial maps on subdivisions.

**Theorem (Filakovský–Wagner–Zhechev; proof by Skopenkov).** Let $l > 1$ be a fixed integer. There is no algorithm that decides, for a given finite $2l$-dimensional simplicial complex $X$ containing a subdivision of $Y_l$ as a given subcomplex, whether the identity map of $Y_l$ extends to a PL map $X \to Y_l$.

The source derives this from the extendability version (its Theorem 1.2): for some fixed integer $m$, there is no algorithm that decides, for a given finite $2l$-dimensional simplicial complex $X$ containing a subdivision of $V^{2l-1}_m$ as a given subcomplex and a given simplicial map $V^{2l-1}_m \to Y_l$, whether this map extends to a PL map $X \to Y_l$. This is a concrete form of the fixed-target case of [extendability of maps into $(k-1)$-connected targets](extension-problem-for-2k-dimensional-sources-undecidable.md) of Čadek, Krčál, Matoušek, Vokřínek and Wagner.

Conventions: the dimension $l$ (and in the extendability version the number $m$) is fixed and the complexes and maps are the input. Since $Y_l$ is simply connected for $l > 1$, the undecidability does not come from the fundamental group; for targets that are not simply connected, analogous statements were known by the middle of the twentieth century.

## Depends on

- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Polyhedral subdivisions](../../algebraic-topology/adapting-families-of-maps-to-open-covers/subdivision.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For a map $\varphi : S^{2l-1} \to S^l$ or into a wedge of spheres, the Hopf–Whitehead invariants turn homotopy classes into integers, and composition with maps of degree $x_j$ on the wedge summands acts on these invariants by integer quadratic forms in the $x_j$. Skopenkov uses this to show that, for even $l$, solvability of a system of equations $\sum_{i<j} a^{i,j}_q x_i x_j = b_q$ $(1 \le q \le m)$ in integers is equivalent to the existence of a PL map $V^l_s \to Y_l$ with a prescribed homotopy class after composition with an explicit map $V^{2l-1}_m \to V^l_s$; for odd $l$ an analogous skew-symmetric system is used. This equivalence is Proposition 1.7 of the source. Such systems of quadratic equations are undecidable (Lemma 1.4, deduced from the negative solution of Hilbert's tenth problem by Čadek, Krčál, Matoušek, Vokřínek and Wagner). A mapping-cylinder construction (Proposition 1.8(a)) converts the existence of such a map into extendability of a simplicial map, which is Theorem 1.2, and Proposition 1.8(b) converts that into extendability of an identity map, which gives the theorem. A good expansion links Lemma 1.4, the Hopf–Whitehead computations (Theorems 1.5 and 1.6) and Propositions 1.7 and 1.8, which have no pages here.

## Sources

- A. Skopenkov, *Extendability of simplicial maps is undecidable*, Discrete Comput. Geom. 69 (2023), no. 1, 250–259, https://doi.org/10.1007/s00454-022-00454-0, read in the copy arXiv:2008.00492v2, whose numbering is used here: the theorem is Theorem 1.1 and the extendability version Theorem 1.2, the quadratic Diophantine systems are Lemma 1.4, their equivalence with homotopy left divisibility is Proposition 1.7, and the mapping-cylinder steps are Proposition 1.8(a) and (b); the source states that Theorem 1.1 is implied, as observed by Filakovský, Wagner and Zhechev, by Theorem 1.2 and Proposition 1.8(b).
- Marek Filakovský, Uli Wagner and Stephan Zhechev, *Embeddability of simplicial complexes is undecidable*, in: Proceedings of the 2020 ACM-SIAM Symposium on Discrete Algorithms (SODA), SIAM, 2020, pp. 767–785, https://doi.org/10.1137/1.9781611975994.47, to whom the source credits this form of the theorem, cited beside the copy read above.
- Martin Čadek, Marek Krčál, Jiří Matoušek, Lukáš Vokřínek and Uli Wagner, *Extendability of continuous maps is undecidable*, Discrete Comput. Geom. 51 (2014), no. 1, 24–66, https://doi.org/10.1007/s00454-013-9551-8, the original source of the result, cited beside the copy read above.
