# Translational monotiling of periodic subsets of ℤ^d is undecidable

No algorithm decides, given $d \ge 3$, a periodic set $E \subseteq \mathbb{Z}^d$ and a finite set $F \subseteq \mathbb{Z}^d$,
whether the single tile $F$ tiles $E$ by translations.

**Theorem.** There is no algorithm which, upon any input of

- an integer $d \ge 3$,
- a periodic set $E \subseteq \mathbb{Z}^d$, given by a finite-index sublattice and a finite set of representatives,
- a finite set $F \subseteq \mathbb{Z}^d$,

decides in finite time whether $F$ tiles $E$, that is, whether $A \oplus F = E$ for some $A \subseteq \mathbb{Z}^d$, in the
sense of [translational tilings](translational-tilings-by-finitely-many-tiles.md).

The dimension $d$ is part of the input. The source also notes that, by blowing tiles up to unions of unit cubes, an analogue
holds for monotilings of $\mathbb{R}^d$ by finite unions of lattice cubes, and that connected monotiles can be obtained in
dimension $d + 2$; neither variant is stated here.

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Translational monotiling of virtually ℤ² spaces is undecidable](translational-monotiling-of-virtually-z2-spaces.md)

## Expansion

The undecidable problem in $\mathbb{Z}^2 \times G_0$ is pulled back to $\mathbb{Z}^d$: a tiling problem in
$\mathbb{Z}^2 \times G_0$ for the region $\mathbb{Z}^2 \times E$ is turned into an equivalent monotiling problem in some
$\mathbb{Z}^d$ for a periodic region and a finite tile. The source cites the pull-back theorem of Meyerovitch, Sanadhya and Solomon (Theorem 1.1 of their note on reduction of tiling problems), or the argument of Section 9 of the earlier Greenfeld–Tao paper on tilings with two tiles.

A good expansion links a page for the pull-back of tiling problems from $\mathbb{Z}^2 \times G_0$ to periodic subsets of $\mathbb{Z}^d$.

## Sources

- R. Greenfeld, T. Tao, "Undecidability of translational monotilings", *Journal of the European Mathematical Society*, published online 2025, doi:[10.4171/JEMS/1673](https://doi.org/10.4171/JEMS/1673). Numbering of the version read, arXiv:2309.09504v2: Corollary 1.5 and the paragraphs after Remark 1.6.
