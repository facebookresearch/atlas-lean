# Quantum commuting isomorphism of graphs is undecidable

No algorithm decides, given two finite graphs $G$ and $H$, whether they are quantum commuting isomorphic, that is, whether the $(G,H)$-isomorphism game has a perfect commuting-operator strategy.

**Theorem (Atserias, Mančinska, Roberson, Šámal, Severini and Varvitsiotis).** The problem of deciding, for finite undirected loopless simple graphs $G$ and $H$, whether $G \cong_{qc} H$ ([quantum commuting isomorphism](quantum-commuting-isomorphism-of-graphs.md)) is undecidable (Corollary 6.9 of the source).

The same paper shows that there are graphs that are quantum commuting isomorphic but not quantum isomorphic (Corollary 6.8), and that nonsignaling isomorphism coincides with fractional isomorphism (Section 4). Some later literature states this result as the undecidability of quantum isomorphism; the result proved is for the commuting-operator model.

## Depends on

- [Quantum commuting isomorphism of graphs](quantum-commuting-isomorphism-of-graphs.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Existence of a perfect commuting-operator strategy for a linear system game is undecidable](../../tsirelson-problem-and-connes-embedding/perfect-commuting-operator-play-is-undecidable.md)
- [Perfect commuting strategies and the synchronous game algebra](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/perfect-strategies-and-synchronous-game-algebra.md)

## Expansion

To a linear binary constraint system $\mathcal{F}$ over $\mathbb{Z}_2$ with $m$ constraints the source associates two graphs $G_{\mathcal{F}}$ and $G_{\mathcal{F}_0}$, where $\mathcal{F}_0$ is the homogeneous system with the same left-hand sides. Theorem 6.5 of the source shows that the BCS game of $\mathcal{F}$ has a perfect commuting-operator strategy if and only if $G_{\mathcal{F}} \cong_{qc} G_{\mathcal{F}_0}$; the proof works with the tracial-state description of perfect commuting strategies of synchronous games. Since the construction is computable and Slofstra proved that perfect commuting-operator play of linear system games is undecidable, so is quantum commuting isomorphism. A good expansion adds Theorem 6.5, with the construction of $G_{\mathcal{F}}$ and $G_{\mathcal{F}_0}$, as a page and links it.

## Sources

- Albert Atserias, Laura Mančinska, David E. Roberson, Robert Šámal, Simone Severini and Antonios Varvitsiotis, "Quantum and non-signalling graph isomorphisms", *Journal of Combinatorial Theory, Series B* 136:289–328, 2019, doi:[10.1016/j.jctb.2018.11.002](https://doi.org/10.1016/j.jctb.2018.11.002). Numbering of the version read, arXiv:1611.09837v3: Corollary 6.9, Corollary 6.8 and Theorem 6.5.
- William Slofstra, "Tsirelson's problem and an embedding theorem for groups arising from non-local games", *Journal of the American Mathematical Society* 33(1):1–56, 2020, doi:[10.1090/jams/929](https://doi.org/10.1090/jams/929), cited by the source for the undecidability of perfect commuting-operator play of linear system games (statement quoted in Section 6 of the first source).
