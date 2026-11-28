# The domino problem is undecidable on Baumslag-Solitar groups

For all positive integers $m$ and $n$, no algorithm decides whether a given finite set of Wang tiles admits a valid tiling of
the Baumslag–Solitar group $BS(m, n)$.

For nonzero integers $m, n$ the *Baumslag–Solitar group* is the two-generator one-relator group

$$
BS(m, n) = \langle a, b \mid a^m b = b a^n \rangle ;
$$

$BS(1, 1) \cong \mathbb{Z}^2$, and $BS(-m, -n) \cong BS(m, n)$.

**Theorem.** For all integers $m, n \ge 1$, the
[domino problem](wang-tilings-of-finitely-generated-groups-and-th.md) on $BS(m, n)$, with Wang tiles on the generators
$\{a, b\}$, is undecidable.

Here $m$ and $n$ are fixed and the input is the tile set. The groups $BS(m, n)$ have decidable word problem, being one-relator
groups, and most of them are not residually finite, hence not virtually free, so neither of the general criteria in the
definition settles their domino problem. The source states that the case $n < 0$ is analogous. The construction also gives tile sets on $BS(m, n)$ that admit
valid tilings but no computable one.

## Depends on

- [Wang tilings of finitely generated groups and the domino problem](wang-tilings-of-finitely-generated-groups-and-th.md)
- [Group](../../../../GroupTheory/group-basics/group.md)
- [One-relator group](../../../../GroupTheory/presentations-and-decision-problems/coherence-of-one-relator-groups/one-relator-group.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the mortality problem of piecewise affine maps, following Kari's proof for the hyperbolic plane. An instance
is a finite family of rational affine maps $f_i(\vec{x}) = M_i \vec{x} + \vec{b}_i$ of $\mathbb{R}^2$ with disjoint closed unit
squares $U_i$ with integer corners as domains; a point is *immortal* if all its forward and backward iterates stay in
$\bigcup_i U_i$, and deciding whether an immortal point exists is undecidable, by reduction from the mortality problem of
Turing machines. In the Cayley graph of $BS(m, n)$ the cosets of $\langle a \rangle$ form levels; tiles on one level encode a
point of $\mathbb{R}^2$ through averages of their labels, and the tiles between adjacent levels compute one of the maps
$f_i$, as in the weakly aperiodic tile set the source constructs. The resulting finite tile set admits a valid tiling of
$BS(m, n)$ exactly when the piecewise affine map has an immortal point.

## Sources

- N. Aubrun and J. Kari, "Tiling problems on Baumslag-Solitar groups", in *Machines, Computations and Universality (MCU 2013)*, Electronic Proceedings in Theoretical Computer Science 128, pp. 35–46, 2013, doi:10.4204/EPTCS.128.12; numbering of the version arXiv:1309.1266v1: Theorem 9 (undecidability) and Theorem 10 (arecursive tile sets) of Section 4, Theorem 8 (weakly aperiodic tile sets) of Section 3, and Section 2 (Baumslag–Solitar groups and their Cayley graphs).
