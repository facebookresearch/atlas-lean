# EF-emptiness of closed bounded parametric timed automata is undecidable

No algorithm decides whether some parameter valuation lets a parametric timed automaton reach a target location, even when
every parameter ranges over a closed bounded interval.

**Theorem.** The EF-emptiness problem is undecidable for bounded PTAs, and also for closed bounded PTAs: no algorithm
decides, given a (closed) bounded PTA $\mathcal{A}$ and a set of target locations, whether the set of parameter valuations
$v$ in the bounds such that some run of $v(\mathcal{A})$ reaches a target location is empty. Here PTAs, valuations and
EF-emptiness are as in [parametric timed automata](parametric-timed-automata.md), with rational parameter valuations.

The encoding for bounded PTAs uses three clocks and one parameter, which can be bounded by $[0, 1]$. For general (unbounded) PTAs the source recalls
undecidability from Alur, Henzinger and Vardi; the source also shows that EF-emptiness is undecidable for integer-points PTAs, while it
is decidable for bounded integer-points PTAs and for L/U-PTAs.

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Reduce the halting problem of deterministic two-counter machines started with zero counters. Each machine state becomes a
location; the counter values $c_1, c_2$ are encoded by clocks $x, y, z$ and one parameter $a$ so that $y = 1 - a c_1$ and
$z = 1 - a c_2$ whenever $x = 0$, and gadgets implement increment and zero-test with decrement. A valuation of $a$ simulates
the machine faithfully as long as $a$ is small enough for the counter values reached, so the halting location is reachable
for some valuation exactly when the machine halts. For the closed version the two strict inequalities of the encoding (one
forcing $a > 0$, one testing a nonzero counter) are replaced by non-strict constructions whose spurious behavior at the
boundary valuations cannot reach the target.

## Sources

- É. André, D. Lime, O. H. Roux, "Reachability and liveness in parametric timed automata", *Logical Methods in Computer Science* 18(1), article 31, 2022, doi:[10.46298/lmcs-18(1:31)2022](https://doi.org/10.46298/lmcs-18(1:31)2022). Numbering of the version read, arXiv:2004.09171v4: Theorem 4.1 (bounded PTAs), Theorem 4.3 (closed bounded PTAs), Theorem 4.14 (integer-points PTAs), Theorem 4.4 (bounded integer-points PTAs) the summary of Section 6, and Section 1 (the earlier undecidability of EF-emptiness for general PTAs).
