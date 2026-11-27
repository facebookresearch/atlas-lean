# Covering and partitioning branching rules for SAT

A *branching rule* maps a CNF formula $\varphi$ over a declared variable set $X$ to a finite list of child formulas $\varphi_1,\dots,\varphi_r$ over $X$. It *covers* models if for every assignment $\sigma$ of $X$, $\sigma$ satisfies $\varphi$ iff it satisfies some $\varphi_i$; it *partitions* models if moreover every model of $\varphi$ satisfies exactly one child and non-models satisfy none. Splitting on a variable (children $\varphi\wedge\neg x$ and $\varphi\wedge x$, i.e. the restrictions $\varphi\restriction_{x=0}$ and $\varphi\restriction_{x=1}$ together with the unit clause fixing $x$) partitions models; splitting a clause $\ell_1 \vee \dots \vee \ell_k$ of $\varphi$ into the children $\varphi\wedge\ell_i$ covers models, and into the children $\varphi\wedge\neg\ell_1\wedge\dots\wedge\neg\ell_{i-1}\wedge\ell_i$ ($1\le i\le k$) partitions them.

## Depends on

- [Restriction of a CNF formula by a literal](../../../Logic/propositional-logic/conjunctive-normal-form/restrict-2.md)
- [Splitting on a variable](../../../Logic/propositional-logic/conjunctive-normal-form/sat-iff-restrict-true-or-false.md)

## Sources

- F. V. Fomin and D. Kratsch, Exact Exponential Algorithms, Springer, 2010.
