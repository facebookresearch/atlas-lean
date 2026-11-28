# Whether a periodic configuration has a preimage under the Game of Life is Π⁰₁-complete

No algorithm decides whether a given doubly periodic configuration of the Game of Life has a preimage, that is, whether it is not a Garden of Eden; the problem is $\Pi^0_1$-complete.

Let $g : \{0,1\}^{\mathbb{Z}^2} \to \{0,1\}^{\mathbb{Z}^2}$ be the global map of the Game of Life, the two-dimensional [cellular automaton](cellular-automata-on-z-d.md) with the Moore neighborhood in which a live cell survives with two or three live neighbors and a dead cell becomes live with exactly three. A configuration $x$ is *periodic* (in the sense of [periodic configurations](finite-periodic-and-garden-of-eden-configurations.md); the source says totally periodic) if there are positive integers $m, n$ with $x_{(i+m, j)} = x_{(i, j+n)} = x_{(i,j)}$ for all $(i, j)$, and it is given by its $m \times n$ period block. A *$g$-preimage* of $x$ is a configuration $y \in \{0,1\}^{\mathbb{Z}^2}$, not necessarily periodic, with $g(y) = x$.

**Theorem (Salo and Törmä).** It is undecidable, and specifically $\Pi^0_1$-complete, whether a given periodic configuration $x \in \{0,1\}^{\mathbb{Z}^2}$ has a $g$-preimage.

Membership in $\Pi^0_1$ is the usual compactness argument: $x$ has a preimage exactly when every finite window of $x$ has a locally consistent preimage pattern, and each window is checked by finite search.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)
- [Finite, periodic and Garden-of-Eden configurations](finite-periodic-and-garden-of-eden-configurations.md)
- [The arithmetical class $\Pi_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The paper builds, from wires and logic gadgets realized by Game of Life patterns, an effective semiweak universality theorem: every two-dimensional subshift of finite type $Y$ can be computed into a periodic configuration $x_Y$ such that the preimage set $g^{-1}(x_Y)$, with the action of the period lattice, factors onto $Y$ through a block map that has a block-map section. In particular $x_Y$ has a $g$-preimage exactly when $Y$ is nonempty. Emptiness of subshifts of finite type, equivalently whether a set of Wang tiles tiles the plane, is undecidable by Berger's theorem, and the reduction is many-one; with the $\Pi^0_1$ upper bound this gives $\Pi^0_1$-completeness.

## Sources

- V. Salo and I. Törmä, "Structure and computability of preimages in the Game of Life", *Theoretical Computer Science* 1042, 2025, article 115237, doi:10.1016/j.tcs.2025.115237; read in arXiv:2308.10198v2: the definitions of the section "Definitions", the effective universality theorem of the section "Universality", and Theorem 8 of the section "Corollaries" with its proof.
