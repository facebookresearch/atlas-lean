# Cycle-existence emptiness of parametric timed automata is undecidable

No algorithm decides whether some parameter valuation gives a parametric timed automaton an infinite run, already for
bounded automata with three clocks and one parameter.

**Theorem.** The cycle-existence-emptiness problem is undecidable for PTAs, and for bounded PTAs, with at least $3$ clocks
and $1$ parameter: no algorithm decides, given such an automaton $\mathcal{A}$, whether the set of parameter valuations $v$
such that $v(\mathcal{A})$ has an infinite maximal run is empty. Automata and runs are as in
[parametric timed automata](parametric-timed-automata.md).

For L/U-PTAs the problem is decidable, and PSPACE-complete. Cycle-existence emptiness is equivalent to the universality of
"all maximal runs are finite".

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction uses the boundedness problem of two-counter machines (whether the counters stay bounded along the computation),
which is undecidable. In the one-parameter encoding of the counters, a valuation $a$ simulates the machine as long as the
counter values stay below about $1/a$, and the construction makes the run stop when the encoding overflows; an infinite run
exists for some valuation exactly when the counters stay bounded.

## Sources

- É. André, D. Lime, O. H. Roux, "Reachability and liveness in parametric timed automata", *Logical Methods in Computer Science* 18(1), article 31, 2022, doi:[10.46298/lmcs-18(1:31)2022](https://doi.org/10.46298/lmcs-18(1:31)2022). Numbering of the version read, arXiv:2004.09171v4: Theorem 5.7 (undecidability), Theorem 5.6 (L/U-PTAs) and Section 2.5 (the boundedness problem of two-counter machines).
