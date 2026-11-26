# Recognizable series and finitely generated stable semimodules

For a [semiring](semirings-and-formal-power-series.md) $S$, the series $S\langle\langle \Sigma^* \rangle\rangle$ form a left $S$-semimodule under pointwise
sum and left scalar multiplication. For $u \in \Sigma^*$ let $u^{-1} r$ be the series with $(u^{-1} r, w) = (r, u w)$, and call a subsemimodule
*stable* if it contains $u^{-1} r$ whenever it contains $r$. A series $r$ is [recognizable](weighted-automata-over-a-semiring.md) if and only
if it belongs to some finitely generated stable subsemimodule (Fliess; Jacob). Over the Boolean semiring this says that a language is regular
if and only if it has finitely many left quotients.

## Depends on

- [Semirings and formal power series on a free monoid](semirings-and-formal-power-series.md)
- [Weighted automata over a semiring](weighted-automata-over-a-semiring.md)

## Sources

- M. Droste and D. Kuske, "Weighted automata", in J.-É. Pin (ed.), *Handbook of Automata Theory*, vol. I, EMS Press, 2021, Chapter 4 (authors' version, <https://eiche.theoinf.tu-ilmenau.de/kuske/Publications/DroK21.pdf>): Section 5, the definitions of semimodules and stable subsemimodules, Theorem 5.1 and its proof, and the remark after it on the Boolean semiring.
