# Every Boolean function has a CNF with at most l·2^l connectives

For every $\ell\ge 0$ and every Boolean function $f:\{0,1\}^\ell\to\{0,1\}$ there is a CNF formula $\varphi$ over the variables $x_1,\dots,x_\ell$ with $\varphi(x)=f(x)$ for all $x$, whose number of binary connectives (each clause of $k$ literals contributing $k-1$ disjunctions and a conjunction of $m$ clauses contributing $m-1$ conjunctions) is at most $\ell\cdot 2^\ell$.

## Proof sketch

Take one clause of $\ell$ literals for each falsifying assignment of $f$, excluding exactly that assignment. There are at most $2^\ell$ clauses, each with $\ell-1$ disjunctions, plus fewer than $2^\ell$ conjunctions.

## Depends on

- [Connective count of a propositional formula](../../../../../Logic/propositional-logic/tseitin-transformation/connective-count.md)
- [Satisfiability of a CNF formula](../../../../../Logic/propositional-logic/conjunctive-normal-form/cnfsat.md)

## Sources

- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
