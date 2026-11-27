# The domino problem of the lamplighter group is undecidable

No algorithm decides whether a given subshift of finite type on the lamplighter group (Z/2) ≀ Z is nonempty; the problem is Π⁰₁-complete. This settles the unseeded case left open after the seeded tiling problem on this group was shown undecidable.

**Setting.** The [lamplighter group](../../../../GroupTheory/group-rings/ore-condition-for-group-algebras/lamplighter.md) $\mathcal L=(\mathbb Z/2)\wr\mathbb Z$ has the presentation $\langle a,b\mid(a^nb^{-n})^2\ (n\ge1)\rangle$. For a finite alphabet $C$, a *subshift of finite type* on $\mathcal L$ is the set of colorings $x:\mathcal L\to C$ in which no translate of a pattern from a given finite list of forbidden patterns occurs. The *domino problem* (tiling problem) of $\mathcal L$ asks, given such a finite list of forbidden patterns, whether the subshift of finite type it defines is nonempty; equivalently, whether a given finite set of tiles admits a [valid tiling](wang-tilings-of-finitely-generated-groups-and-th.md) of $\mathcal L$.

**Theorem (Bartholdi and Salo).** The domino problem on the lamplighter group is undecidable (Theorem 4.9); more precisely, it is $\Pi^0_1$-complete (Corollary 6.5, stated in the introduction as Corollary D).

Previously only the seeded tiling problem of $\mathcal L$, which also prescribes the color of one cell, was known to be undecidable, see [the seeded tiling problem on the lamplighter group](seeded-tiling-problem-on-the-lamplighter-group.md). The same paper constructs a strongly aperiodic tile set on $\mathcal L$ with $1488$ tiles (Theorem 4.8) and shows that the entropies of subshifts of finite type on $\mathcal L$ are exactly the upper semicomputable nonnegative real numbers.

## Depends on

- [Group](../../../../GroupTheory/group-basics/group.md)
- [Lamplighter group](../../../../GroupTheory/group-rings/ore-condition-for-group-algebras/lamplighter.md)
- [Wang tilings of finitely generated groups and the domino problem](wang-tilings-of-finitely-generated-groups-and-th.md)
- [The arithmetical class $\Pi_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

The paper gives two proofs. The first (Theorem 4.9) represents in $\mathcal L$ unions of discrete hyperbolic planes, the 1-skeleton of a tiling of the hyperbolic plane by pentagons, through translates of two subgroups, and then follows Kari's method: tiles store reals as averages along rows and force each row to be an affine image of the previous one, which reduces the mortality problem for rational piecewise affine maps of the plane. The second encodes every Wang tile set of the Euclidean plane into a sofic shift on $\mathcal L$ whose restrictions to cosets of a subgroup are Wang towers, towers of tilings of squares $\{0,\dots,2^n-1\}^2$ each contained in a quadrant of the next; since it is undecidable whether a Wang tile set tiles arbitrarily large squares, the domino problem of $\mathcal L$ is undecidable, and the general simulation theorem of the paper upgrades this to $\Pi^0_1$-completeness. A good expansion links pages for the simulation of Wang towers by sofic shifts on $\mathcal L$ and for the mortality problem of piecewise affine maps; neither has a page yet.

## Sources

- Laurent Bartholdi and Ville Salo, "Shifts on the lamplighter group", *Transactions of the American Mathematical Society*, 2026, doi:[10.1090/tran/9765](https://doi.org/10.1090/tran/9765); read in arXiv:2402.14508v1 ([arXiv](https://arxiv.org/abs/2402.14508v1)), whose numbering is used: the presentation of $\mathcal L$ in Section 2, Theorems 4.8 and 4.9 with the proof of Theorem 4.9, the construction of Wang towers in Section 5 and the remark after it, Corollary 6.5, Corollaries D and E of the introduction, and the abstract for the entropies.
