# Global halting of periodic-plus-finite sandpiles on ℤ³ is undecidable

No algorithm decides, given a periodic configuration of chips on $\mathbb{Z}^3$ with finitely many chips added, whether the abelian sandpile process makes infinitely many topplings in total.

**Theorem.** The *p+f global halting problem* for [periodic-plus-finite abelian sandpiles on ℤ³](periodic-plus-finite-abelian-sandpiles-on-z3.md), which asks for a given p+f sandpile whether $\sum_{v \in \mathbb{Z}^3} N(v) = \infty$, is undecidable.

## Depends on

- [Periodic-plus-finite abelian sandpiles on ℤ³](periodic-plus-finite-abelian-sandpiles-on-z3.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting of single-tape Turing machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The fuse-circuit simulation used for vertex prediction initializes every square of the tape at once, which already costs infinitely many topplings. The source replaces it by a *lazy automaton*, a one-dimensional automaton that initializes blank squares only one per time step on each side, with two wavefronts moving at speed one. When the simulated Turing machine enters a final state, a *lazy* state appears and spreads at speed two, catches up with both wavefronts and stops them, so the automaton does finitely much work; if the machine never halts, the wavefronts move forever. A periodic fuse circuit simulating the lazy automaton, realized as a p+f sandpile, therefore makes finitely many topplings in total exactly when the Turing machine halts.

## Sources

- H. Cairns, "Some Halting Problems for Abelian Sandpiles Are Undecidable in Dimension Three", *SIAM Journal on Discrete Mathematics* 32(4):2636–2666, 2018, doi:[10.1137/16M1091964](https://doi.org/10.1137/16M1091964); numbering of arXiv:1508.00161v2: Theorem 3 (p+f global halting) with its proof, and the section on the lazy automaton before it.
