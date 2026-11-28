# Convergent cellular automata

A cellular automaton is convergent when every orbit tends to a limit configuration in the product topology, so that every cell eventually stops changing.

**Definition.** Let $F:Q^{\mathbb Z^d}\to Q^{\mathbb Z^d}$ be a [cellular automaton](../cellular-automata-on-z-d.md). $F$ is *convergent* if for every configuration $c$ the sequence $(F^t(c))_{t\in\mathbb N}$ has a limit in the product (Cantor) topology, written $F^\omega(c)$. The *freezing time* $\tau(c,z)$ of a cell $z$ from $c$ is the least $t$ such that $F^{t+t'}(c)_z=F^t(c)_z$ for all $t'\ge0$.

## Depends on

- [Cellular automata on ℤ^d](../cellular-automata-on-z-d.md)

## Proof depends on

None.

## Expansion

Every [bounded-change](bounded-change-cellular-automata.md) automaton is convergent, but not conversely: in the shrinking zone construction a head bounces between the ends of a working zone and shrinks it at each bounce, so every cell freezes after a number of changes that depends on the configuration (Example 7, Fact 2). A convergent automaton that is not nilpotent has at least two distinct fixed points (Proposition 1).

## Sources

- Nicolas Ollinger and Guillaume Theyssier, "Freezing, Bounded-Change and Convergent Cellular Automata", *Discrete Mathematics & Theoretical Computer Science* 24(1), 2022, paper 5734, doi:[10.46298/dmtcs.5734](https://doi.org/10.46298/dmtcs.5734); read in arXiv:1908.06751v4 ([arXiv](https://arxiv.org/abs/1908.06751v4)), whose numbering is used (separate counters for definitions, facts, examples and propositions): Definition 3, Example 7 and Fact 2 in Section 2 (Main Definitions, with Examples), and Proposition 1 in Section 3.
