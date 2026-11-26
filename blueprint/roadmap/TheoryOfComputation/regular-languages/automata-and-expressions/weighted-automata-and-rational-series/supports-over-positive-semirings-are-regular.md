# Supports of recognizable series over positive semirings are regular

Let $S$ be a [semiring](semirings-and-formal-power-series.md) that is zero-sum free and zero-divisor free: $x + y = 0$ or $x \cdot y = 0$ implies
$x = 0$ or $y = 0$. Then the support of every [recognizable series](weighted-automata-over-a-semiring.md) over $S$ is a regular language; deleting
the transitions of weight $0$ and forgetting the other weights gives a finite automaton for it. This applies to $(\mathbb{N}, +, \cdot, 0, 1)$ and to
the max-plus semiring, but not to the ring $\mathbb{Z}$, over which supports of recognizable series need not be regular.

## Depends on

- [Semirings and formal power series on a free monoid](semirings-and-formal-power-series.md)
- [Weighted automata over a semiring](weighted-automata-over-a-semiring.md)

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Proposition 9.5 with its proof and the examples after it, and the remark before it on $\mathbb{Z}$ (Example 7.1).
