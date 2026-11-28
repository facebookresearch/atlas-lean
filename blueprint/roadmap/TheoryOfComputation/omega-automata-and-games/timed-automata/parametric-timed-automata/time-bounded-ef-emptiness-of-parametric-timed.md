# Time-bounded EF-emptiness of parametric timed automata is undecidable

No algorithm decides whether some parameter valuation lets a parametric timed automaton reach a target location within a
fixed time bound, already with three clocks and two rational-valued parameters.

Let $\mathcal{A}$ be a [parametric timed automaton](parametric-timed-automata.md), with parameter valuations in
$\mathbb{Q}_{\ge 0}$ and dense time. *Time-bounded* EF-emptiness asks, given $\mathcal{A}$, a target location and a rational constant
$T \ge 0$, whether the set of parameter valuations $v$ such that $v(\mathcal{A})$ has a run reaching the target within total
elapsed time at most $T$ is empty.

**Theorem.** The EF-emptiness problem is undecidable over bounded time for PTAs with three clocks and two parameters (Theorem 3.12 of the source); undecidability holds already for the fixed bound $T = 1$, which the reduction uses.

The source attributes an earlier statement of the result to Jovanović and gives a different full proof; it
uses the result to transfer the other undecidability results of the paper to the time-bounded setting.

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction from halting of two-counter machines studies the system over one time unit ($T = 1$). It modifies the
encoding of the robust preservation proof by replacing the constant $1$ by a new parameter $p_1$, so that $x_i = p_1 - p_2
\cdot c_i$ whenever the tick clock is $0$, and counter values up to $p_1 / p_2$ can be represented. Every gadget (increment,
decrement, zero-test) takes at least $p_1$ time units, so within one time unit at most about $1/p_1$ machine steps are
simulated; a halting computation is simulated for a valuation with $p_1$ small enough for its length and $p_2$ small enough
for its counter values.

## Sources

- É. André, D. Lime, N. Markey, "Language preservation problems in parametric timed automata", *Logical Methods in Computer Science* 16(1), article 5, 2020, doi:[10.23638/LMCS-16(1:5)2020](https://doi.org/10.23638/LMCS-16(1:5)2020). Numbering of the version read, arXiv:1807.07091v3: Theorem 3.12 and Section 3.5 (problems over bounded time).
