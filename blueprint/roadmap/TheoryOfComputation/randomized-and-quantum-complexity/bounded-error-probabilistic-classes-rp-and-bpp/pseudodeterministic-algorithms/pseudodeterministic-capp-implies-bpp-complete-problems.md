# Lu–Oliveira–Santhanam: worst-case pseudodeterministic CAPP in polynomial time gives BPP complete problems

Oliveira and Santhanam showed unconditionally that there is a pseudodeterministic algorithm for the Circuit Acceptance Probability Problem (output, canonically, an additive approximation of the acceptance probability of a given circuit) that runs in subexponential time and is correct with high probability over any samplable distribution of circuits on infinitely many input lengths. If instead there is a **worst-case** pseudodeterministic polynomial-time algorithm for CAPP, then $\mathrm{BPP}$ has a complete problem. Improving the running time of the known algorithm, or making it work on every large input length, would imply new time hierarchy theorems for probabilistic time.

## Proof sketch

A pseudodeterministic CAPP algorithm gives each circuit a canonical estimate, which turns the semantic promise defining $\mathrm{BPP}$ into a syntactic one: the language of pairs (machine, input) whose canonical estimate exceeds $1/2$, run with a clock, is in $\mathrm{BPP}$ and every $\mathrm{BPP}$ language reduces to it.

## Depends on

- [Pseudodeterministic algorithms for search problems (Gat–Goldwasser)](pseudodeterministic-algorithm-for-search-problem.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Sources

- Zhenjian Lu, Igor C. Oliveira and Rahul Santhanam, "Pseudodeterministic Algorithms and the Structure of Probabilistic Time", STOC (2021), ECCC TR21-039.
