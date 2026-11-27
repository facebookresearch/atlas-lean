# The domino problem is undecidable on every set of tilings with finite local complexity

For every nonempty set of geometric tilings with finite local complexity, the domino problem on that set is $\Pi^0_1$-hard; and whether the
purely geometric tilings by a given finite set of polygons have finite local complexity is $\Sigma^0_1$-complete.

**Theorem.** For [geometric tilings and the domino problem on a set of tilings](geometric-tilings-and-the-domino-problem-on-a-se.md):

1. for every nonempty set $X$ of geometric tilings with finite local complexity, the domino problem on $X$ is $\Pi^0_1$-hard, and therefore undecidable;
2. the problem of deciding, given a finite shapeset $\mathcal{S}$ of polygons, whether the purely geometric subshift on $\mathcal{S}$ has finite local complexity is $\Sigma^0_1$-complete, and
   therefore undecidable.

Item 1 contains the undecidability of the classical domino problem, the case of the edge-to-edge tilings by a unit square, and an earlier result for subshifts of rhombus
tilings. The theorem assumes only that $X$ is nonempty and has finite local complexity; the source remarks that the domino problem on $X$ need not be $\Pi^0_1$-complete, since the tilings in $X$ can be arbitrarily complex.

## Depends on

- [Geometric tilings and the domino problem on a set of tilings](geometric-tilings-and-the-domino-problem-on-a-se.md)
- [The arithmetical class $\Pi_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [The arithmetical class $\Sigma_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

For item 1, the proof reduces the nearest-neighbor domino problem on $\mathbb{Z}^2$. Using finite local complexity, labels and forbidden patterns on the given shapes carve out a grid-like
structure on any tiling of $X$, a coherent family of paths that behaves, up to quasi-isometry, like the square grid, and the colors of the $\mathbb{Z}^2$ instance are carried along it;
a valid labeled tiling over $X$ exists exactly when the $\mathbb{Z}^2$ instance has a valid configuration. For item 2, a shapeset fails to have finite local complexity exactly when
some tiling has a shear line in the direction of a side of a shape, which places the problem in $\Sigma^0_1$; hardness reduces the halting problem using a purely geometric version of
the Robinson tiles modified by Gurevich and Koryakov, which tile periodically when the encoded machine halts and otherwise admit tilings with a sliding shear line.

## Sources

- B. Hellouin de Menibus, V. H. Lutfalla and P. Vanier, "Decision problems on geometric tilings", *Theoretical Computer Science* 1067, article 115756, 2026, doi:10.1016/j.tcs.2026.115756; read in arXiv:2409.11739v2: Theorem 13 of Section 3 (The domino problem is undecidable on every set of tilings) with its proof, and Theorem 22 of Section 4 (Finite local complexity is undecidable for geometric tilings) with Lemmas 23 and 24, with the numbering of that version.
