# Whether a freezing cellular automaton is k-change is undecidable

For some fixed $k$, no algorithm decides whether a given freezing cellular automaton changes the state of each cell at most $k$ times, although a freezing automaton with $n$ states is always $(n-1)$-change.

**Theorem (Ollinger and Theyssier).** There exists $k\in\mathbb N$ such that it is undecidable, given a freezing cellular automaton $F$, whether $F$ is $k$-change (see [freezing, bounded-change and convergent cellular automata](freezing-bounded-change-and-convergent-cellular.md)).

The proof uses one-dimensional automata. The bound $n-1$ for an $n$-state freezing automaton depends on the automaton, so the theorem is not in conflict with it: $k$ is fixed while the automata vary.

## Depends on

- [Freezing, bounded-change and convergent cellular automata](freezing-bounded-change-and-convergent-cellular.md)

## Proof depends on

- [Reachability for one-dimensional freezing cellular automata is undecidable](cylinder-reachability-of-freezing-cellular.md)

## Expansion

The Minsky machine simulation $F_M$ used for cylinder reachability is reused. Its freezing order admits a unique longest chain of state changes, through an initialization sequence $i_0\to\cdots\to i_K$, the initial machine state, three counter-marker states and the halting state $h$, with $K=3k'+3$ for $k'$ counters; every other admissible sequence is shorter. This longest chain can occur at the origin only in a configuration whose evolution simulates a halting computation of $M$ from zero counters, so $F_M$ fails to be $(K+4)$-change iff $M$ halts on the empty input, which is undecidable.

## Sources

- Nicolas Ollinger and Guillaume Theyssier, "Freezing, Bounded-Change and Convergent Cellular Automata", *Discrete Mathematics & Theoretical Computer Science* 24(1), 2022, paper 5734, doi:[10.46298/dmtcs.5734](https://doi.org/10.46298/dmtcs.5734); read in arXiv:1908.06751v4 ([arXiv](https://arxiv.org/abs/1908.06751v4)), whose numbering is used (separate counters for theorems, propositions and corollaries): Theorem 6 and its proof, and Theorem 4 (halting of two-counter machines on the empty input).
