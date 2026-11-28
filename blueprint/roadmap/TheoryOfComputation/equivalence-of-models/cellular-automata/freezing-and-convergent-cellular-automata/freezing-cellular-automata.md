# Freezing cellular automata

A cellular automaton is freezing when some partial order on its states is never increased by an update, so that every cell can only move down that order.

**Definition.** Let $F:Q^{\mathbb Z^d}\to Q^{\mathbb Z^d}$ be a [cellular automaton](../cellular-automata-on-z-d.md) with finite state set $Q$, neighborhood $V$ and local rule $f$. $F$ is *freezing* if there is a partial order $\le$ on $Q$ with $F(c)_z\le c_z$ for every configuration $c$ and cell $z$.

## Depends on

- [Cellular automata on ℤ^d](../cellular-automata-on-z-d.md)

## Proof depends on

None.

## Expansion

Equivalently, the relation $q\to_F q'$, meaning that in some context a cell can change from state $q$ to $q'\neq q$ in one step, is acyclic; this gives an algorithm deciding whether an automaton is freezing in time $O(n^{|V|})$ for $n$ states (Fact 1). A freezing automaton with $n$ states changes the state of each cell at most $n-1$ times, so it is [bounded-change](bounded-change-cellular-automata.md). Examples of freezing automata include Ulam's crystal-growth rule, bootstrap percolation, forest-fire models and Life without Death.

## Sources

- Nicolas Ollinger and Guillaume Theyssier, "Freezing, Bounded-Change and Convergent Cellular Automata", *Discrete Mathematics & Theoretical Computer Science* 24(1), 2022, paper 5734, doi:[10.46298/dmtcs.5734](https://doi.org/10.46298/dmtcs.5734); read in arXiv:1908.06751v4 ([arXiv](https://arxiv.org/abs/1908.06751v4)), whose numbering is used (separate counters for definitions, facts, examples and propositions): Definition 1 and Fact 1 in Section 2 (Main Definitions, with Examples), with Examples 1 to 4 (forest-fire models are mentioned in Example 4).
