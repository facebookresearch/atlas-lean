# Turing NP-hardness of MCSP implies E is not in P/poly

If MCSP is NP-hard under parametric honest Turing reductions, or under natural Turing reductions, then E has no polynomial-size circuits. Unconditionally, MKtP is not hard for E under parametric honest Turing reductions.

**Theorem (Saks–Santhanam).**

1. If MCSP is NP-hard under parametric honest polynomial-time Turing reductions, then $\mathrm{E}\not\subseteq\mathrm{SIZE}(\mathrm{poly})$.
2. If MCSP is NP-hard under natural polynomial-time Turing reductions, then $\mathrm{E}\not\subseteq\mathrm{SIZE}(\mathrm{poly})$.
3. MKtP is not hard for E under parametric honest polynomial-time Turing reductions.

Every language in P reduces to MCSP under parametric honest Turing reductions, so item 1 must use that the source language is NP-hard. These were the first consequences of NP-hardness of MCSP under Turing reductions of any kind.

## Expansion

For item 3, take a tally language in E but not in P, which exists by diagonalization, and simulate the reduction on $0^n$ answering every query "yes". Each query is produced from $0^n$ in polynomial time, so it has Kt complexity $O(\log n)$, below its parameter $n^{\varepsilon}$; all "yes" answers are therefore correct and the tally language would be in P. For item 1, simulate a parametric honest reduction from SAT answering every query "yes". If this decides SAT, then $\mathrm{P}=\mathrm{NP}$, and $\mathrm{E}\subseteq\mathrm{SIZE}(\mathrm{poly})$ would collapse E into P by the Karp–Lipton theorem for E, contradicting the time hierarchy. Otherwise the Gutfreund–Shaltiel–Ta-Shma refuter produces, from $1^n$ in polynomial time, instances on which the simulation fails; the first wrongly answered query is a truth table needing circuits of size $n^{\varepsilon}$, and the concatenation of all queries is an E-computable truth table on $O(\log n)$ variables that needs exponential-size circuits. Item 2 uses indirect diagonalization with robustly-often simulations.

## Depends on

- [Natural and parametric honest reductions to MCSP](natural-and-parametric-honest-reductions-to-mcsp.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [The minimum Kt problem MKtP](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/the-minimum-kt-problem.md)
- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)
- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Deterministic time hierarchy: quadratic versus linear time](../../../hierarchy-theorems-and-barriers/time-hierarchy-theorem/time-hierarchy.md)

## Sources

- Michael Saks, Rahul Santhanam, "Circuit Lower Bounds from NP-Hardness of MCSP Under Turing Reductions", *Computational Complexity Conference (CCC)*, 2020, https://doi.org/10.4230/LIPIcs.CCC.2020.26 (Theorems 1, 2, 7, 8 and 10, Lemma 9).
