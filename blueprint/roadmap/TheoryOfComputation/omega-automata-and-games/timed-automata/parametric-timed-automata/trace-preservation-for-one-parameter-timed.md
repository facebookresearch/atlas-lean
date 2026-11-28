# Trace preservation for one-parameter timed automata is undecidable

No algorithm decides, given a parametric timed automaton with one parameter and a reference valuation, whether some other
valuation yields the same set of untimed traces.

Let $\mathcal{A}$ be a parametric timed automaton in the syntax of the source (see
[parametric timed automata](parametric-timed-automata.md): atomic constraints $x \bowtie p + c$, $x \bowtie c$ and
$p \bowtie c$ with ${\bowtie} \in \{<, \le, =, \ge, >\}$ and $c \in \mathbb{Z}$; parameter valuations in $\mathbb{Q}_{\ge 0}$).
For a valuation $v$, the *untimed language* $\mathcal{L}(v(\mathcal{A}))$ is the set of (finite or infinite) action
sequences of the maximal runs of $v(\mathcal{A})$, and the set of *untimed traces* $\mathrm{Traces}(v(\mathcal{A}))$ is the
set of their sequences of pairs (location, action).

The *trace preservation problem* asks, given $\mathcal{A}$ and a parameter valuation $v$, whether there is a valuation
$v' \neq v$ with $\mathrm{Traces}(v'(\mathcal{A})) = \mathrm{Traces}(v(\mathcal{A}))$.

**Theorem.** The trace preservation problem for PTAs with one parameter is undecidable.

Traces record the visited locations, so the reduction for languages, which uses extra locations, does not apply directly.
The source also proves that it is undecidable whether some valuation gives an automaton without reachable zero-delay
cycles.

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Language preservation for one-parameter timed automata is undecidable](language-preservation-for-one-parameter-timed.md)

## Expansion

The source gives two proofs. The first transforms a (parametric) timed automaton without zero-delay cycles, in which every
run starts with a positive delay and at most $k$ transitions occur in zero delay, into an equivalent automaton with a single
location, using diagonal constraints and $k \times |L| + 2$ additional non-parametric clocks; on a one-location automaton
traces carry the same information as untimed words, so the undecidability of language preservation transfers. The second
proof avoids diagonal constraints and uses eight locations, with unboundedly many transitions and parametric clocks.

## Sources

- É. André, D. Lime, N. Markey, "Language preservation problems in parametric timed automata", *Logical Methods in Computer Science* 16(1), article 5, 2020, doi:[10.23638/LMCS-16(1:5)2020](https://doi.org/10.23638/LMCS-16(1:5)2020). Numbering of the version read, arXiv:1807.07091v3: Theorem 3.6 (trace preservation), Propositions 3.7 and 3.8 (collapsing locations) and Theorem 3.9 (zero-delay cycles).
