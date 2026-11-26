# Characteristic series of a language are recognizable exactly when it is regular

Let $S$ be a commutative [semiring](semirings-and-formal-power-series.md) with $0 \ne 1$ and $L \subseteq \Sigma^*$. Then the characteristic series $1_L$ is
[recognizable](weighted-automata-over-a-semiring.md) over $S$ if and only if $L$ is regular (Wang). For an arbitrary semiring, $1_L$ is recognizable
whenever $L$ is regular, by weighting a deterministic automaton for $L$ with $0$ and $1$; the converse uses, for commutative rings, that
recognizable series with finite image have recognizable level sets (Schützenberger; Sontag), and otherwise a semiring homomorphism onto the
Boolean semiring. Without commutativity the converse fails: some semiring makes $1_L$ recognizable for every language $L$; it also fails when $0 = 1$, since then
every series is the zero series.

## Depends on

- [Semirings and formal power series on a free monoid](semirings-and-formal-power-series.md)
- [Weighted automata over a semiring](weighted-automata-over-a-semiring.md)

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Lemma 9.1, Theorem 9.2, Lemma 9.3, Theorem 9.4 and Theorem 9.8.
