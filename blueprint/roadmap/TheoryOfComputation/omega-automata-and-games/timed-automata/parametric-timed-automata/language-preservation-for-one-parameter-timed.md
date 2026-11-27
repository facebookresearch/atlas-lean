# Language preservation for one-parameter timed automata is undecidable

No algorithm decides, given a parametric timed automaton with one parameter and a reference valuation, whether some other
valuation yields the same untimed language.

Let $\mathcal{A}$ be a parametric timed automaton in the syntax of the source (see
[parametric timed automata](parametric-timed-automata.md): atomic constraints $x \bowtie p + c$, $x \bowtie c$ and
$p \bowtie c$ with ${\bowtie} \in \{<, \le, =, \ge, >\}$ and $c \in \mathbb{Z}$; parameter valuations in $\mathbb{Q}_{\ge 0}$).
For a valuation $v$, the *untimed language* $\mathcal{L}(v(\mathcal{A}))$ is the set of (finite or infinite) action
sequences of the maximal runs of $v(\mathcal{A})$, and the set of *untimed traces* $\mathrm{Traces}(v(\mathcal{A}))$ is the
set of their sequences of pairs (location, action).

The *language preservation problem* asks, given $\mathcal{A}$ and a parameter valuation $v$, whether there is a valuation
$v' \neq v$ with $\mathcal{L}(v'(\mathcal{A})) = \mathcal{L}(v(\mathcal{A}))$.

**Theorem.** The language preservation problem for PTAs with one parameter is undecidable, both over discrete and over
continuous time, and both for integer and for rational parameter valuations.

The source also shows that it is undecidable whether some valuation $v' \neq v$ gives a language strictly included in,
included in, containing or strictly containing that of $v$, and the same for the sets of not necessarily maximal finite
untimed words. Language preservation becomes decidable, with an effective synthesis of the preserving valuations, for
deterministic PTAs with one clock.

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

First the halting problem of deterministic two-counter machines is reduced to EF-emptiness: the automaton uses four clocks,
a tick $t$ reset every $p$ time units, clocks $x_1, x_2$ equal to the counter values when $t = 0$, and a clock $z$ counting the
simulated steps, so that the parameter $p$ bounds the length of the simulated computation and the counter values. The halting
location is reachable for some valuation iff the machine halts; otherwise every run deadlocks once $z$ exceeds $p - 1$. For
language preservation, every transition is labeled by one letter $a$; for $p = 0$ the automaton accepts $\{a^\omega\}$ through
a separate loop, while for $p > 0$ it must simulate the machine and continues with $a^\omega$ only after reaching the halting
location. With the reference valuation $p = 0$, some other valuation preserves the language iff the machine halts. The
construction works unchanged over discrete time and for integer parameters.

## Sources

- É. André, D. Lime, N. Markey, "Language preservation problems in parametric timed automata", *Logical Methods in Computer Science* 16(1), article 5, 2020, doi:[10.23638/LMCS-16(1:5)2020](https://doi.org/10.23638/LMCS-16(1:5)2020). Numbering of the version read, arXiv:1807.07091v3: Theorem 3.1 (language preservation), Lemma 3.2 (the reduction to EF-emptiness), Propositions 3.4 and 3.5 (inclusion variants) and Definition 2.7 (the problems).
