# Translational monotiling of virtually ℤ² spaces is undecidable

No algorithm decides, given a finite abelian group $G_0$, a set $E \subseteq G_0$ and a finite set
$F \subseteq \mathbb{Z}^2 \times G_0$, whether the single tile $F$ tiles $\mathbb{Z}^2 \times E$ by translations.

**Theorem.** There is no algorithm which, upon any input of

- a finite abelian group $G_0$,
- a set $E \subseteq G_0$,
- a finite set $F \subseteq \mathbb{Z}^2 \times G_0$,

decides in finite time whether $F$ tiles $\mathbb{Z}^2 \times E$, that is, whether some $A \subseteq \mathbb{Z}^2 \times G_0$
satisfies $A \oplus F = \mathbb{Z}^2 \times E$ in the sense of
[translational tilings](translational-tilings-by-finitely-many-tiles.md).

The group $G_0$ is part of the input, not fixed; the source poses as an open question whether some fixed finite abelian
group $G_0$ already gives an undecidable problem. The source remarks that the problem is in fact Turing complete, of Turing
degree $0'$. In $\mathbb{Z}^2$ itself translational monotiling is decidable (Bhattacharya, via the periodic tiling
conjecture for $\mathbb{Z}^2$).

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Abelian group](../../../../GroupTheory/group-basics/abelian-group.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

The proof encodes the Wang tiling problem in three steps. First, a Wang tile set is turned into an instance of a more general
*domino problem* on $\mathbb{N}^2$ (assignments of pips to cells such that horizontally and vertically adjacent pairs lie in
given relations), which is undecidable because the Wang tiling problem is. Second, for sufficiently large distinct primes
$p_1, p_2$, a domino problem is encoded as a *decorated $p_1 \times p_2$-adic Sudoku puzzle*, whose solutions carry
infinitely many $p_1 \times p_2$-adic scales, each decorated by the pip of a simulated cell, in the spirit of the
Aanderaa–Lewis construction. Third, the Sudoku puzzle is expressed in the tiling language developed for the counterexample
to the periodic tiling conjecture, which turns it into a single-tile problem in $\mathbb{Z}^2 \times G_0$ for a finite
abelian group $G_0$ depending on the instance. The domino problem is solvable exactly when the monotiling problem is.

## Sources

- R. Greenfeld, T. Tao, "Undecidability of translational monotilings", *Journal of the European Mathematical Society*, published online 2025, doi:[10.4171/JEMS/1673](https://doi.org/10.4171/JEMS/1673). Numbering of the version read, arXiv:2309.09504v2: Theorem 1.3 (the main theorem), Remark 1.4 (Turing degree), Corollary 2.7 (the domino problem), Theorems 3.2 and 3.3 (the two encodings) and Question 7.1 (fixed $G_0$).
