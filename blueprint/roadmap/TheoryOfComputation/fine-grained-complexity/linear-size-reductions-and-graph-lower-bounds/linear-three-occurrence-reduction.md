# Linear-size parsimonious reduction to three occurrences per variable

There is a polynomial-time map $\varphi\mapsto\varphi'$ from $k$-CNF formulas ($k\ge2$) to $k$-CNF formulas in which every variable occurs at most three times, with the same model count, the number of satisfying assignments of the variables occurring in the formula (parsimonious; in particular satisfiability is preserved), and with the number of variables and clauses of $\varphi'$ linear in the number of literal occurrences of $\varphi$. Consequently ETH implies that 3SAT with at most three occurrences per variable has no $2^{o(n)}$ algorithm.

## Proof sketch

Replace the $d$ occurrences of a variable $x$ by fresh copies $x_1,\dots,x_d$ and add the implication cycle $x_1\to x_2\to\cdots\to x_d\to x_1$ as $d$ two-literal clauses, forcing all copies equal; each copy then occurs three times. Combined with sparsification, linear size in occurrences means linear size in variables.

## Depends on

- [The 3SAT decision problem](../../np-completeness/satisfiability/3-satisfiability/sat3-dec.md)
- [Model count of a CNF formula](../../../Logic/propositional-logic/model-count-preserving-cnf-transformations/model-count.md)
- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Proof depends on

- [ETH holds for sparse 3-SAT iff for general 3-SAT](../sparsification-lemma/eth-for-sparse-3sat.md)
- [Binary implication cycles and chains](../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/cnf-gadgets-and-encodings/binary-implication-cycles.md)

## Sources

- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994, Proposition 9.3.
- Russell Impagliazzo, Ramamohan Paturi and Francis Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 2001.
