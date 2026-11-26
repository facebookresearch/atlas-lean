# The Satisfiability Hypothesis (SH) and its counting version

The **Satisfiability Hypothesis** states that for every $p<1$ there is no deterministic algorithm deciding CNF satisfiability in time $2^{O(\mu^{p})}\cdot\mathrm{poly}(L)$, where $\mu$ is the number of occurring variables plus clauses plus literal occurrences; that is, no fixed power saving in the exponent of the instance size. $\#\mathrm{SH}$ is the same statement for computing the number of satisfying assignments. SH is weaker than ETH (it survives subexponential algorithms of the form $2^{n/\mathrm{polylog}\,n}$) yet still implies $\mathsf{P}\ne\mathsf{NP}$.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](k-sat-exponents.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Sources

- MIT Hardness Group et al., "ETH is Dead, Long Live SH", arXiv:2611.02650v2, 2026.
