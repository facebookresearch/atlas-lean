# EF-universality of parametric timed automata is undecidable

No algorithm decides whether every parameter valuation lets a parametric timed automaton reach a target location, even
for bounded automata with three parametric clocks and two rational-valued parameters.

**Theorem.** The EF-universality problem is undecidable for bounded PTAs and for PTAs: no algorithm decides, given a PTA
$\mathcal{A}$ (bounded or not) and a set of target locations, whether for every parameter valuation $v$ some run of
$v(\mathcal{A})$ reaches a target location, with PTAs and valuations as in
[parametric timed automata](parametric-timed-automata.md).

The source proves the stronger statement for bounded *integer-points PTAs* (PTAs in which every reachable symbolic state
contains a point with integer clock and parameter values) with at least three parametric clocks and two rational-valued
parameters, a class for which EF-emptiness is decidable. EF-universality is the dual of AG-emptiness.

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from the boundedness problem of two-counter machines (do the counters stay bounded along the computation
from zero counters?), which is undecidable. It reuses the encoding of the counters by clocks and a parameter $a$ from the
EF-emptiness proofs, without the final gadget, and adds an error location that the automaton can enter whenever $a$ is too
large to encode a reached counter value $c$ (that is, $1 - a c < 0$); a second parameter $b$ keeps every reachable symbolic
state integer-points. If a counter grows unbounded, every valuation $a > 0$ eventually overflows and reaches the error
location; if the counters stay below $c$, the valuation $a = 1/(c + 1)$, $b = 1$ never does. So the error location is
reachable for all valuations exactly when the counters are unbounded. A good expansion adds and links a page for the
undecidability of the boundedness problem of two-counter machines.

## Sources

- É. André, D. Lime, O. H. Roux, "Reachability and liveness in parametric timed automata", *Logical Methods in Computer Science* 18(1), article 31, 2022, doi:[10.46298/lmcs-18(1:31)2022](https://doi.org/10.46298/lmcs-18(1:31)2022). Numbering of the version read, arXiv:2004.09171v4: Theorem 4.12 (bounded integer-points PTAs) and Corollary 4.13 (integer-points PTAs, bounded PTAs and PTAs).
