# Bounded-change cellular automata

A cellular automaton is $k$-change when no cell changes its state more than $k$ times along any orbit, and bounded-change when it is $k$-change for some $k$.

**Definition.** Let $F:Q^{\mathbb Z^d}\to Q^{\mathbb Z^d}$ be a [cellular automaton](../cellular-automata-on-z-d.md). For $k\in\mathbb N$, $F$ is *$k$-change* if for every configuration $c$ and cell $z$ the set $\{t\in\mathbb N: F^{t+1}(c)_z\neq F^t(c)_z\}$ has at most $k$ elements. $F$ is *bounded-change* if it is $k$-change for some $k$.

## Depends on

- [Cellular automata on ℤ^d](../cellular-automata-on-z-d.md)

## Proof depends on

None.

## Expansion

Every [freezing](freezing-cellular-automata.md) automaton with $n$ states is $(n-1)$-change, nilpotent automata (some power $F^t$, $t>0$, is constant) are bounded-change, and every bounded-change automaton is [convergent](convergent-cellular-automata.md); the inclusions freezing, bounded-change, convergent are strict (Fact 2). Prediction of a cell after $t$ steps is in NLOGSPACE for one-dimensional bounded-change automata (Proposition 6).

## Sources

- Nicolas Ollinger and Guillaume Theyssier, "Freezing, Bounded-Change and Convergent Cellular Automata", *Discrete Mathematics & Theoretical Computer Science* 24(1), 2022, paper 5734, doi:[10.46298/dmtcs.5734](https://doi.org/10.46298/dmtcs.5734); read in arXiv:1908.06751v4 ([arXiv](https://arxiv.org/abs/1908.06751v4)), whose numbering is used (separate counters for definitions, facts, examples and propositions): Definition 2 and Fact 2 in Section 2 (Main Definitions, with Examples), and Proposition 6 in Section 4.1.
