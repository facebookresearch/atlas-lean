# Nivat-type decomposition of recognizable series

Let $S$ be a [semiring](semirings-and-formal-power-series.md) and $r \in S\langle\langle \Sigma^* \rangle\rangle$ a series with $(r, \varepsilon) = 0$. Then $r$ is
[recognizable](weighted-automata-over-a-semiring.md) if and only if there are an alphabet $\Gamma$, a homomorphism $h : \Gamma^* \to \Sigma^*$ with
$h(a) \ne \varepsilon$ for every $a \in \Gamma$, a regular language $K \subseteq \Gamma^*$ and a monoid homomorphism $c : (\Gamma^*, \cdot, \varepsilon) \to (S, \cdot, 1)$
such that $(r, w) = \sum_{v \in K,\ h(v) = w} c(v)$ for every word $w$, a sum indexed by the finitely many words $v \in K$ with $h(v) = w$.

## Depends on

- [Semirings and formal power series on a free monoid](semirings-and-formal-power-series.md)
- [Weighted automata over a semiring](weighted-automata-over-a-semiring.md)

## Proof depends on

- [Characteristic series of a language are recognizable exactly when it is regular](characteristic-series-and-regular-languages.md)

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Theorem 6.3 (after Nivat) with Lemmas 6.1 and 6.2; the selection series there is a series over the semiring of finite languages whose support is $K$, regular by Lemma 6.1(1), and the proof writes $c \circ \mathrm{sel} = c \odot 1_K$.
