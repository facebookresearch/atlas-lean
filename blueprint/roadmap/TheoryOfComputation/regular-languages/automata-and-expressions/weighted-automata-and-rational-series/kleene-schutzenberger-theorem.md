# Kleene–Schützenberger theorem

For every [semiring](semirings-and-formal-power-series.md) $S$ and finite alphabet $\Sigma$, a series in $S\langle\langle \Sigma^* \rangle\rangle$ is
[recognizable](weighted-automata-over-a-semiring.md) if and only if it is [rational](rational-series.md) (Schützenberger). Recognizable series
contain the monomials and are closed under sum, Cauchy product and the iteration of proper series; conversely, the behavior of a weighted
automaton is a component of the unique solution of a system of linear equations $s_i = \sum_j r_{ij} s_j + r_i$ with proper rational
coefficients $r_{ij}$, solved by eliminating unknowns with $s = r^* r'$. Over the Boolean semiring this is Kleene's theorem.

## Depends on

- [Semirings and formal power series on a free monoid](semirings-and-formal-power-series.md)
- [Weighted automata over a semiring](weighted-automata-over-a-semiring.md)
- [Rational series](rational-series.md)

## Proof depends on

- [Linear representations of recognizable series](linear-representations-of-recognizable-series.md)

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Theorem 4.8 and Lemmas 4.1, 4.2 and 4.5–4.7.
