# Covering and partitioning branching rules for SAT

A *branching rule* maps a CNF formula $\varphi$ over a declared variable set $X$ to a finite list of child formulas $\varphi_1,\dots,\varphi_r$ over $X$. It *covers* models if for every assignment $\sigma$ of $X$, $\sigma$ satisfies $\varphi$ iff it satisfies some $\varphi_i$; it *partitions* models if moreover every model of $\varphi$ satisfies exactly one child and non-models satisfy none. Splitting on a variable (children $\varphi\restriction_{x=0}$ and $\varphi\restriction_{x=1}$, with $x$ fixed) partitions models; splitting a clause $\ell_1 \vee \dots \vee \ell_k$ into children "$\ell_i$ true" covers models, and into children "$\ell_1,\dots,\ell_{i-1}$ false and $\ell_i$ true" partitions them.

## Depends on

- [Restriction of a CNF formula by a literal](../../../Logic/propositional-logic/conjunctive-normal-form/restrict-2.md)
- [Splitting on a variable](../../../Logic/propositional-logic/conjunctive-normal-form/sat-iff-restrict-true-or-false.md)

## Sources

- F. V. Fomin and D. Kratsch, Exact Exponential Algorithms, Springer, 2010.
