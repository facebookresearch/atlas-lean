# Solving discounted-payoff games is in UP ∩ coUP

Deciding, for a finite discounted-payoff game with a binary-encoded rational discount factor and integer weights in binary, a vertex and a binary-encoded rational threshold,
whether the value is at least the threshold is in $\mathrm{UP} \cap \mathrm{coUP}$, where $\mathrm{UP}$ is the class of decision problems decided by a
nondeterministic polynomial-time Turing machine with at most one accepting computation on every input. The machine guesses the
[value vector](discounted-payoff-values-are-the-unique-fixed-point.md), which is unique and has a polynomial-size description (it solves a linear system
fixed by a pair of positional optimal strategies), and checks the fixed-point equation.

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)

## Proof depends on

- [Discounted-payoff values are the unique fixed point of a contraction](discounted-payoff-values-are-the-unique-fixed-point.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.3, Theorem 5.7 with its proof.
