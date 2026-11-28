# The seeded tiling problem on the lamplighter group is undecidable

The lamplighter group, which is not virtually free and contains no plane or hyperbolic plane geometrically, has an undecidable seeded tiling problem: the grid $\mathbb Z^2$ is simulated in its Cayley graph through regular expressions driven by a subshift of finite type.

**Theorem.** Let $G$ be a finitely generated group with a finite symmetric generating set $S$. For a finite set $A$ of colors, a *tileset* is a subset $\Pi \subseteq A \times S \times A$, and a *tiling* of $G$ is a coloring $\varphi : G \to A$ with $(\varphi_g, s, \varphi_{gs}) \in \Pi$ for all $g \in G$ and $s \in S$. The *seeded tiling problem* asks, given $\Pi$ and a seed color $a_0 \in A$, whether there is a tiling with $\varphi_1 = a_0$ at the identity. For the lamplighter group $L = \mathbb Z/2 \wr \mathbb Z = \langle a, b \mid (a^n b^{-n})^2 \text{ for all } n \ge 1 \rangle$, with $S = \{a^{\pm 1}, b^{\pm 1}\}$, the seeded tiling problem is undecidable (Theorem A of the source).

The same holds for the seeded tiling problem of every Diestel–Leader graph $\mathrm{DL}(p, q)$ with $p, q \ge 2$, labeled as in the source (Theorem B and Theorem 7.1). On the trivially labeled $\mathrm{DL}(p, q)$ the seeded problem is decidable for uninteresting reasons (§7); Conjecture 7.2 concerns automorphism-invariant vertex-and-edge subshifts of finite type on the unlabeled graph, of which $\mathrm{DL}(2, 2)$ is essentially the Cayley graph of $L$. Whether the unseeded tiling problem (domino problem) of $L$ is undecidable was left open in this paper (Conjecture 1.1) and was later [settled](the-domino-problem-of-the-lamplighter-group-is.md). Previously all groups known to have an undecidable tiling problem either had an undecidable word problem or contained a plane or hyperbolic plane geometrically; virtually free groups have a decidable tiling problem (see also [Wang tilings of finitely generated groups and the domino problem](wang-tilings-of-finitely-generated-groups-and-th.md)).

## Depends on

- [Group](../../../../GroupTheory/group-basics/group.md)
- [Lamplighter group](../../../../GroupTheory/group-rings/ore-condition-for-group-algebras/lamplighter.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the seeded tiling problem of $\mathbb Z^2$, undecidable by Kahr, Moore and Wang (Theorem 3.7 of the source); it also follows from the undecidability of the unseeded tiling problem, linked above, by trying every seed color. Tiling problems are treated as problems about labeled graphs, and a graph $\mathcal G$ *simulates* a graph $\mathcal H$ when the edges of $\mathcal H$ are realized by regular expressions in the edges of $\mathcal G$, under an auxiliary labeling of $\mathcal G$ by a "pheromone" tileset; if $\mathcal G$ simulates $\mathcal H$ and $\mathcal G$ has a solvable tiling problem, so does $\mathcal H$ (Theorems 3.4 and 3.6). Although $\mathbb Z^2$ does not embed geometrically in $L$, the decorated Cayley graph of $L$ simulates the quadrant or the plane, using a "comb" (Proposition 5.2) or a "sea level" (Proposition 6.10). Combining the pheromone tileset with the instance, and using a seed tile to fix the decoration, gives the undecidability of the seeded tiling problem of $L$.

A complete expansion links pages for the simulation theorems (Theorems 3.4 and 3.6 of the source) and the comb and sea-level simulations (Propositions 5.2 and 6.10), the constructions the proof rests on.

## Sources

- L. Bartholdi and V. Salo, "Simulations and the lamplighter group", *Groups, Geometry, and Dynamics* 16(4):1461–1514, 2022, doi:[10.4171/GGD/692](https://doi.org/10.4171/GGD/692); read as arXiv:2010.14299v2, whose numbering is used here: Section 1 (tilings and the seeded tiling problem), Theorems A and B, Conjecture 1.1, Theorems 3.4, 3.6 and 3.7, and Propositions 5.2 and 6.10, Theorem 7.1 and Conjecture 7.2.
