# Subexponential-time k-SAT: ETH and SETH fail

For every fixed $k$ and every $\delta>0$, $k$-SAT is decidable by a deterministic multi-tape Turing machine in time $2^{\delta n}\cdot\mathrm{poly}(L)$, with polynomial work space, where $n$ is the number of occurring variables. Equivalently $s_k=0$ for every $k$, so the Exponential Time Hypothesis and the Strong Exponential Time Hypothesis are false; their counting versions $\#\mathrm{ETH},\#\mathrm{SETH}$ fail as well. The same holds on the word RAM with logarithmic word size.

## Proof sketch

A positive model count decides satisfiability, so the subexponential model counter gives time $2^{A s(n)}\mathrm{poly}(L)$ with $s(n)=o(n)$, which is below $2^{\delta n}$ for large $n$; small $n$ are handled by exhaustive search.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Proof depends on

- [Subexponential exact model counting for bounded-width CNF](subexponential-model-counting.md)

## Sources

- OpenAI, "The Exponential Time Hypothesis is False", Manuscript, 2026.
