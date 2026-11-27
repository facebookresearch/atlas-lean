# The Game of Life is computationally universal

The *Game of Life* is the two-dimensional [cellular automaton](cellular-automata-on-z-d.md) with states $\{0, 1\}$ (dead and
living), the Moore neighborhood $\{-1, 0, 1\}^2$, and the local rule under which a living cell stays alive exactly when two
or three of its eight neighbors are alive and a dead cell becomes alive exactly when three of them are; $0$ is quiescent.
For every Turing machine $M$ one can effectively construct a [finite configuration](finite-periodic-and-garden-of-eden-configurations.md)
that eventually becomes the all-$0$ configuration if and only if $M$ halts on the blank tape. Hence it is undecidable whether
a given finite configuration of the Game of Life dies.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)
- [Finite, periodic and Garden-of-Eden configurations](finite-periodic-and-garden-of-eden-configurations.md)

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

This page becomes ready once:

- The construction by Berlekamp, Conway and Guy of finite Game of Life configurations (gliders, glider guns and their collisions) that simulate a given Turing machine, with a source whose locator has been checked (proof prerequisite and source check; not yet stated)

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Section 2.6, the definition of the Game of Life and Theorem 1 (Berlekamp et al.).
