# Convergence and bounded change of cellular automata are undecidable

In every dimension, nilpotent cellular automata cannot be separated by an algorithm from non-convergent ones, and it is undecidable whether a given convergent cellular automaton is bounded-change.

**Theorem (Ollinger and Theyssier).** In every dimension $d\ge1$, for [freezing, bounded-change and convergent cellular automata](freezing-bounded-change-and-convergent-cellular.md):
1. the set of nilpotent cellular automata and the set of non-convergent cellular automata are recursively inseparable: no decidable set of automata contains every nilpotent one and no non-convergent one; in particular convergence and bounded change are undecidable;
2. it is undecidable, given a convergent cellular automaton, whether it is bounded-change.

By contrast, whether a cellular automaton is freezing is decidable.

## Depends on

- [Freezing, bounded-change and convergent cellular automata](freezing-bounded-change-and-convergent-cellular.md)

## Proof depends on

- [Nilpotency of cellular automata is undecidable](../nilpotency-of-cellular-automata-is-undecidable.md)

## Expansion

Both items reduce the nilpotency problem for one-dimensional automata of radius $1$ with a spreading state $s$ (a state that, once present in a neighbourhood, spreads), which is undecidable (Kari); the constructions extend to higher dimensions. For item 1, $F_1$ runs $F$ while flipping a bit at every step, and collapses to a fixed state once $s$ appears: $F_1$ is nilpotent if $F$ is, and not convergent otherwise. For item 2, $F_2$ simulates $F$ inside *working zones* in which a head bounces between the zone's ends and shrinks the zone at each bounce, so that every cell eventually stops changing and $F_2$ is always convergent; cells turn into an error state when $s$ appears. If $F$ is not nilpotent, some orbit avoids $s$ and cells of $F_2$ change unboundedly often; if $F$ is nilpotent, the number of changes is bounded.

## Sources

- Nicolas Ollinger and Guillaume Theyssier, "Freezing, Bounded-Change and Convergent Cellular Automata", *Discrete Mathematics & Theoretical Computer Science* 24(1), 2022, paper 5734, doi:[10.46298/dmtcs.5734](https://doi.org/10.46298/dmtcs.5734); read in arXiv:1908.06751v4 ([arXiv](https://arxiv.org/abs/1908.06751v4)), whose numbering is used (separate counters for theorems, propositions and corollaries): Theorem 1 and its proof, the shrinking-zone construction of Example 7 and Lemma 1, and Fact 1.
