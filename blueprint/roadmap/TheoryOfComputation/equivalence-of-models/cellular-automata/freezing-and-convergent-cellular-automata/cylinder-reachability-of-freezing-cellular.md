# Reachability for one-dimensional freezing cellular automata is undecidable

There is a one-dimensional freezing cellular automaton for which no algorithm decides whether, from some configuration extending a given finite pattern, a given pattern is eventually reached at the origin.

**Theorem (Ollinger and Theyssier).** For a [cellular automaton](../cellular-automata-on-z-d.md) $F$ on $Q^{\mathbb Z^d}$ and a *bounded configuration* $u\in Q^{\mathcal B(n)}$, where $\mathcal B(n)$ is the ball of radius $n$ for the maximum norm, the *cylinder* $[u]$ is the set of configurations agreeing with $u$ on $\mathcal B(n)$. The *cylinder reachability problem* $\mathrm{CYREACH}_F$ asks, given bounded configurations $u,v$, whether $F^t(c)\in[v]$ for some $c\in[u]$ and $t\in\mathbb N$. There exists a one-dimensional [freezing](freezing-cellular-automata.md) cellular automaton $F$ whose cylinder reachability problem is undecidable.

The automaton constructed in the proof has neighborhood $\{-1,0,1\}$. The source also gives a two-dimensional freezing automaton, and a one-dimensional [convergent](convergent-cellular-automata.md) automaton, whose prediction problem is P-complete and whose cylinder reachability problem is undecidable (Propositions 4 and 5).

## Depends on

- [Freezing cellular automata](freezing-cellular-automata.md)
- [Convergent cellular automata](convergent-cellular-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

A $k$-counter Minsky machine is simulated by a one-dimensional freezing automaton $F_M$ in which the machine's configuration at time $x$ is the temporal column of cell $x$: the control is a signal of slope about $2$ carrying the machine state and emptiness flags, counters are encoded in unary along the time axis, incrementing slows the signal down and decrementing speeds it up, and wall states protect the computation zone from wrong halting information. For a two-counter machine $M_u$ with undecidable halting problem on a given input, an input yields a bounded configuration $v$ such that the halting state $h$ is reachable at the origin from $[v]$ iff $M_u$ halts on that input.

## Sources

- Nicolas Ollinger and Guillaume Theyssier, "Freezing, Bounded-Change and Convergent Cellular Automata", *Discrete Mathematics & Theoretical Computer Science* 24(1), 2022, paper 5734, doi:[10.46298/dmtcs.5734](https://doi.org/10.46298/dmtcs.5734); read in arXiv:1908.06751v4 ([arXiv](https://arxiv.org/abs/1908.06751v4)), whose numbering is used (separate counters for theorems, propositions and corollaries): Definition 5 (cylinder reachability) in Section 4.1, Theorem 4 (Minsky's universality, recalled), Definition 6 and the construction of the subsection on Minsky machine simulation with Lemmas 3 and 4, Theorem 5 and its proof, and Propositions 4 and 5.
