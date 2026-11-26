# Exponent transfer under the Satisfiability Hypothesis

Assume SH. Let $R$ be a many-one reduction from 3-SAT, running in time $2^{O((s+1)^{q})}\mathrm{poly}$ where $s=n+m$ is the source size, producing instances whose target parameter is $N=O((s+1)^{b+\eta})$ for every $\eta>0$. If $b>0$, $p>0$ and $bp<1$, then the target problem has no deterministic algorithm running in time $2^{O((N+1)^{p})}\mathrm{poly}$ (for $q<1$). In particular, quadratic-size planarization yields: planar 3-SAT with at most three occurrences per variable, and planar positive (exact) 1-in-3-SAT, admit no algorithms in time $2^{O(n^{p})}$ for any $p<1/2$ under SH.

## Proof sketch

Composing the reduction with a fast target algorithm gives a 3-SAT algorithm in time $2^{O(s^{\max(q,\,bp+b\eta)})}$; choosing $\eta$ with $b(p+\eta)<1$ yields a power saving, contradicting SH.

## Depends on

- [The Satisfiability Hypothesis (SH) and its counting version](satisfiability-hypothesis.md)
- [Fine-grained reductions](../fine-grained-hypotheses/fine-grained-reductions.md)

## Proof depends on

- [SH in terms of fixed-width formulas](sh-fixed-width-formulation.md)

## Sources

- MIT Hardness Group et al., "ETH is Dead, Long Live SH", arXiv:2611.02650v2, 2026, Theorem 3.1.
