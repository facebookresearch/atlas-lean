# Whether a periodic configuration has a periodic preimage under the Game of Life is Σ⁰₁-complete

For the Game of Life, it is $\Sigma^0_1$-complete whether a given doubly periodic configuration has a doubly periodic preimage, and undecidable even for periodic configurations that are promised to have some preimage.

Let $g$ be the global map on $\{0,1\}^{\mathbb{Z}^2}$ of the Game of Life, the two-dimensional [cellular automaton](cellular-automata-on-z-d.md) with the Moore neighborhood in which a live cell survives with two or three live neighbors and a dead cell becomes live with exactly three. A configuration is *periodic* (totally periodic in the source) if it is invariant under translation by $(m, 0)$ and $(0, n)$ for some positive integers $m, n$, as for [periodic configurations](finite-periodic-and-garden-of-eden-configurations.md); a periodic configuration is given by a period block. A *periodic $g$-preimage* of $x$ is a periodic configuration $y$ with $g(y) = x$.

**Theorem (Salo and Törmä).**

1. Given a periodic configuration $x \in \{0,1\}^{\mathbb{Z}^2}$ that has a $g$-preimage, it is undecidable whether $x$ has a periodic $g$-preimage.
2. Given a periodic configuration $x$, it is $\Sigma^0_1$-complete whether $x$ has a periodic $g$-preimage.

The problem is in $\Sigma^0_1$ because a periodic preimage is a finite object that can be checked. The source also exhibits an explicit periodic configuration with periods $6210 \times 37800$ that has a preimage but no periodic one.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)
- [Finite, periodic and Garden-of-Eden configurations](finite-periodic-and-garden-of-eden-configurations.md)
- [The arithmetical class $\Sigma_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The effective semiweak universality theorem used for the companion page computes, from a subshift of finite type $Y$, a periodic configuration $x_Y$ whose preimage set factors onto $Y$ through a block map with a block-map section. A periodic point of $Y$ lifts through the section to a periodic preimage of $x_Y$, and a periodic preimage of $x_Y$ maps to a periodic point of $Y$; so $x_Y$ has a periodic preimage exactly when $Y$ has a periodic point, and $x_Y$ has a preimage when $Y$ is nonempty. Both claims then follow from Jeandel's theorem that, for nonempty two-dimensional subshifts of finite type, having a totally periodic point is $\Sigma^0_1$-hard. A complete expansion links that theorem on periodic points of subshifts of finite type. Weak universality alone would not suffice: the section is what transports periodic points.

## Sources

- V. Salo and I. Törmä, "Structure and computability of preimages in the Game of Life", *Theoretical Computer Science* 1042, 2025, article 115237, doi:10.1016/j.tcs.2025.115237; read in arXiv:2308.10198v2: Theorem 9 of the section "Corollaries" with its proof, and the explicit configuration of Theorem 2 in the section on the Jeandel–Rao tile set.
