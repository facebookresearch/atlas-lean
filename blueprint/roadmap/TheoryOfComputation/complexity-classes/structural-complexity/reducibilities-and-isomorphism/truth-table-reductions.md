# Polynomial-time truth-table, bounded and Turing reductions

$A\le^{p}_{tt}B$ if there are polynomial-time functions $q$ and $e$ such that $q(x)$ is a list of query strings $y_1,\dots,y_m$ and $x\in A\iff e\bigl(x,[y_1\in B],\dots,[y_m\in B]\bigr)=1$ (non-adaptive queries). Restrictions: **$k$-tt** ($m\le k$), **btt** ($m$ bounded by a constant), **dtt**/**ctt** ($e$ is the disjunction/conjunction of the answers), **ptt** ($e$ monotone). Polynomial-time Turing reductions $A\le^{p}_{T}B$ allow adaptive queries ($A\in\mathsf{P}^{B}$). One has $\le^{p}_{m}\Rightarrow\le^{p}_{1\text{-}tt}\Rightarrow\le^{p}_{btt}\Rightarrow\le^{p}_{tt}\Rightarrow\le^{p}_{T}$, and $\le^{p}_{tt}$ is transitive.

## Depends on

- [Transitivity of polynomial-time many-one reductions](../../../np-completeness/satisfiability/3-satisfiability/poly-many-one-red-trans.md)
- [Polynomial time with an oracle](../../time-and-space-complexity-classes/pwith-oracle.md)

## Sources

- Richard E. Ladner, Nancy A. Lynch and Alan L. Selman, "A comparison of polynomial time reducibilities", Theoretical Computer Science 1(2), 1975.
