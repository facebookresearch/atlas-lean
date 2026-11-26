# CNF formulas, graphs and sized graphs as finite structures

A CNF formula is represented as a finite structure over the vocabulary of two binary relations $\mathrm{pos}(c, x)$ and $\mathrm{neg}(c, x)$: every element names both a clause and a variable, and clause $c$ contains $x$ (resp. $\neg x$) when $\mathrm{pos}(c,x)$ (resp. $\mathrm{neg}(c,x)$). The structure is satisfiable when some subset of elements (the true variables) meets every clause positively or misses it negatively. A graph is a structure with one binary relation $E$ (directed, loops allowed for 3COL); a *sized graph* adds a unary relation $\mathrm{size}$ whose cardinality is the target size of an independent set, clique or vertex cover, avoiding numeric predicates.

## Depends on

- [First-order and quantifier-free reductions](first-order-reductions.md)
- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- R. M. Karp, "Reducibility among Combinatorial Problems", in Complexity of Computer Computations, Plenum Press, 85–103, 1972.
