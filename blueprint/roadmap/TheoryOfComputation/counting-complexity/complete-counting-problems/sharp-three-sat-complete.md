# #3SAT and #3SAT with three occurrences per variable are #P-complete

Counting satisfying assignments of 3-CNF formulas, even when every variable occurs at most three times, is $\#\mathsf{P}$-complete under parsimonious reductions.

## Proof sketch

The standard clause-splitting reduction from CNF to 3-CNF can be made parsimonious by forcing the fresh variables to equal prefix disjunctions; occurrences are reduced by replacing a variable with a cycle of equivalent copies $x_1\to x_2\to\cdots\to x_1$, which preserves the count.

## Depends on

- [Counting satisfying assignments of a CNF formula](../counting-satisfiability-sat/count-sat-fun.md)
- [$\#P$-complete functions](../../complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)

## Proof depends on

- [The Cook–Levin reduction is parsimonious](parsimonious-cook-levin.md)

## Sources

- Leslie G. Valiant, "The Complexity of Enumeration and Reliability Problems", SIAM Journal on Computing 8(3), 1979, Facts 1 and 2.
- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994, Proposition 9.3 (three occurrences per variable).
- Michael R. Garey and David S. Johnson, "Computers and Intractability: A Guide to the Theory of NP-Completeness", W. H. Freeman, 1979.
