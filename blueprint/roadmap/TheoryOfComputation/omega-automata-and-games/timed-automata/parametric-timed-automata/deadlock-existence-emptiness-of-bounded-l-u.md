# Deadlock-existence emptiness of bounded L/U parametric timed automata is undecidable

No algorithm decides whether some parameter valuation gives a parametric timed automaton a deadlocked maximal run, already
for closed bounded L/U-PTAs with three clocks and two parameters.

**Theorem.** The deadlock-existence-emptiness problem is undecidable for closed bounded L/U-PTAs with at least $3$ clocks
and $2$ parameters: no algorithm decides, given such an automaton $\mathcal{A}$, whether the set of parameter valuations $v$
in the bounds such that $v(\mathcal{A})$ has a finite maximal run is empty. Automata and deadlocked runs are as in
[parametric timed automata](parametric-timed-automata.md).

The problem is also undecidable, with at least $3$ clocks and $2$ parameters, for open bounded L/U-PTAs, for L/U-PTAs, for
bounded PTAs and for PTAs. Deadlock-existence emptiness is equivalent to the universality of "all maximal runs are
infinite".

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces the halting problem of two-counter machines. It starts from the one-parameter encoding used for
cycle-existence emptiness and turns it into an L/U-PTA by replacing every comparison $x = a$ of a clock with the parameter
by $a^- \le x \le a^+$, with a lower-bound parameter $a^-$ and an upper-bound parameter $a^+$. A new initial gadget first
checks $a^- \le a^+$, and the constraints around the halting location are arranged so that a deadlocked run forces
$a^- = a^+$, that is, a faithful simulation of the machine.

## Sources

- É. André, D. Lime, O. H. Roux, "Reachability and liveness in parametric timed automata", *Logical Methods in Computer Science* 18(1), article 31, 2022, doi:[10.46298/lmcs-18(1:31)2022](https://doi.org/10.46298/lmcs-18(1:31)2022). Numbering of the version read, arXiv:2004.09171v4: Theorem 5.8 and Corollary 5.9.
