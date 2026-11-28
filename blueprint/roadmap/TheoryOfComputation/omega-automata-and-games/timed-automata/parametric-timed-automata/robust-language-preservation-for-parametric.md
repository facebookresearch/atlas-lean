# Robust language preservation for parametric timed automata is undecidable

No algorithm decides, given a one-parameter timed automaton and a reference valuation, whether some other valuation
preserves the untimed language together with every valuation on the segment between the two.

Let $\mathcal{A}$ be a parametric timed automaton in the syntax of the source (see
[parametric timed automata](parametric-timed-automata.md): atomic constraints $x \bowtie p + c$, $x \bowtie c$ and
$p \bowtie c$ with ${\bowtie} \in \{<, \le, =, \ge, >\}$ and $c \in \mathbb{Z}$; parameter valuations in $\mathbb{Q}_{\ge 0}$).
For a valuation $v$, the *untimed language* $\mathcal{L}(v(\mathcal{A}))$ is the set of (finite or infinite) action
sequences of the maximal runs of $v(\mathcal{A})$, and the set of *untimed traces* $\mathrm{Traces}(v(\mathcal{A}))$ is the
set of their sequences of pairs (location, action).

The *robust* (or continuous) *language preservation problem* asks, given $\mathcal{A}$ and a parameter valuation $v$, whether
there is a valuation $v' \neq v$ such that

$$
\mathcal{L}\bigl((\lambda v + (1 - \lambda) v')(\mathcal{A})\bigr) = \mathcal{L}(v(\mathcal{A})) \quad \text{for every } \lambda \in [0, 1].
$$

**Theorem.** The robust language preservation problem for PTAs with one parameter is undecidable, also when the parameter
is bounded.

The same holds for the robust trace preservation problem. Over bounded time (properties that must hold within a given time
$T$), robust language preservation is undecidable for PTAs with two parameters.

## Depends on

- [Parametric timed automata](parametric-timed-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The discrete reductions need only one preserving valuation, so they do not give robustness. This proof uses rational
parameters and dense time and starts from a reduction of two-counter machine halting to EF-emptiness for one-parameter
PTAs: a clock $t$ ticks every time unit and two parametric clocks satisfy $x_i = 1 - p \cdot c_i$ whenever $t = 0$, with
$p \in (0, 1)$, so that a valuation $p$ can represent counter values below $1/p$. Zero-tests check $x_i = 1$ at $t = 0$, and an
increment resets $x_i$ when it reaches $1 + p$ while the other clocks are reset at $1$. This encoding is then adapted to the
language preservation problem as in the trace preservation proof.

## Sources

- É. André, D. Lime, N. Markey, "Language preservation problems in parametric timed automata", *Logical Methods in Computer Science* 16(1), article 5, 2020, doi:[10.23638/LMCS-16(1:5)2020](https://doi.org/10.23638/LMCS-16(1:5)2020). Numbering of the version read, arXiv:1807.07091v3: Theorem 3.10 (robust language preservation), Theorem 3.11 (robust trace preservation), Theorem 3.13 (bounded time) and Definition 2.7 (continuous versions of the problems).
