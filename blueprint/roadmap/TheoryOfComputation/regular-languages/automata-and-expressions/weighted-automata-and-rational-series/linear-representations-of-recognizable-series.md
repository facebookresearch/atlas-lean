# Linear representations of recognizable series

A *linear representation* of dimension $Q$, for a finite set $Q$, is a triple $(\lambda, \mu, \gamma)$ of vectors $\lambda, \gamma \in S^Q$ and a monoid
homomorphism $\mu$ from $(\Sigma^*, \cdot, \varepsilon)$ to the multiplicative monoid of $Q \times Q$ matrices over the
[semiring](semirings-and-formal-power-series.md) $S$; it defines the series with value $\lambda \cdot \mu(w) \cdot \gamma$ at $w$. A series is
[recognizable](weighted-automata-over-a-semiring.md) if and only if it is defined by some linear representation (Schützenberger): a weighted
automaton $(Q, \mathrm{in}, \mathrm{wt}, \mathrm{out})$ corresponds to $\lambda = \mathrm{in}$, $\mu(a)_{p, q} = \mathrm{wt}(p, a, q)$ and $\gamma = \mathrm{out}$.

## Depends on

- [Semirings and formal power series on a free monoid](semirings-and-formal-power-series.md)
- [Weighted automata over a semiring](weighted-automata-over-a-semiring.md)

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Lemma 3.1, Definition 3.1 and Theorem 3.2.
