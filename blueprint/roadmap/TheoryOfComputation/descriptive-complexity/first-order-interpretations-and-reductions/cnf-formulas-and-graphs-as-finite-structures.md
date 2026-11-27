# CNF formulas, graphs and sized graphs as finite structures

A CNF formula is represented as a finite structure over the vocabulary of two binary relations $\mathrm{pos}(c, x)$ and $\mathrm{neg}(c, x)$: every element names both a clause and a variable, and clause $c$ contains $x$ (resp. $\neg x$) when $\mathrm{pos}(c,x)$ (resp. $\mathrm{neg}(c,x)$). The structure is satisfiable when there is a set $S$ of elements (the true variables) such that for every element $c$ there is an $x$ with $\mathrm{pos}(c,x) \wedge x \in S$ or $\mathrm{neg}(c,x) \wedge x \notin S$. Every element counts as a clause, so an element with no literals is the empty clause; a formula with more variables than clauses is encoded by repeating a clause. A graph is a structure with one binary relation $E$, arbitrary (directed, loops allowed; a loop makes a graph not 3-colorable); a *sized graph* adds a unary relation $\mathrm{size}$ whose cardinality is the target size of an independent set, clique or vertex cover, avoiding numeric predicates. Independence, cliques and vertex covers refer only to edges between distinct vertices.

## Depends on

- [First-order and quantifier-free reductions](first-order-reductions.md)
- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- R. M. Karp, "Reducibility among Combinatorial Problems", in Complexity of Computer Computations, Plenum Press, 85–103, 1972.
