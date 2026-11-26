# SH in terms of fixed-width formulas

For each fixed $k\ge3$: SH holds iff there is no $p<1$ and deterministic algorithm deciding $k$-SAT in time $2^{O((n+m)^{p})}\cdot\mathrm{poly}(L)$, where $n$ counts occurring variables and $m$ clauses. The same equivalence holds between $\#\mathrm{SH}$ and $\#k$-SAT. Moreover SH implies $\#\mathrm{SH}$, since a positive model count decides satisfiability and the count has polynomially many bits.

## Proof sketch

General CNF reduces to $3$-CNF by splitting long clauses with fresh variables, which keeps $\mu$ linear; for fixed width, literal occurrences are at most $k$ times the number of clauses. Decision from counting tests positivity of the count.

## Depends on

- [The Satisfiability Hypothesis (SH) and its counting version](satisfiability-hypothesis.md)

## Sources

- MIT Hardness Group et al., "ETH is Dead, Long Live SH", arXiv:2611.02650v2, 2026, Lemma 2.1.
