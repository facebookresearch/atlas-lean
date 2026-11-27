# Weighted automata over a semiring

Let $S$ be a [semiring](semirings-and-formal-power-series.md) and $\Sigma$ a finite alphabet. A *weighted automaton* over $S$ and $\Sigma$ is a
quadruple $\mathcal{A} = (Q, \mathrm{in}, \mathrm{wt}, \mathrm{out})$ of a finite set $Q$ of states, weight functions $\mathrm{in}, \mathrm{out} : Q \to S$
for entering and leaving a state, and a transition weight function $\mathrm{wt} : Q \times \Sigma \times Q \to S$. A path
$P = q_0 a_1 q_1 \cdots a_n q_n$ has label $a_1 \cdots a_n$ and weight
$\mathrm{in}(q_0) \cdot \prod_{0 \le i < n} \mathrm{wt}(q_i, a_{i+1}, q_{i+1}) \cdot \mathrm{out}(q_n)$, the products taken in order. The *behavior* of $\mathcal{A}$
is the series $\|\mathcal{A}\|$ whose value at $w$ is the sum of the weights of the paths labelled $w$. A series is *recognizable* if it is the
behavior of some weighted automaton. Over the Boolean semiring a series is recognizable if and only if its support is a regular
language.

## Depends on

- [Semirings and formal power series on a free monoid](semirings-and-formal-power-series.md)

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Definitions 2.1, 2.3 and 2.4 and the remark after Definition 2.4 on the Boolean semiring.
