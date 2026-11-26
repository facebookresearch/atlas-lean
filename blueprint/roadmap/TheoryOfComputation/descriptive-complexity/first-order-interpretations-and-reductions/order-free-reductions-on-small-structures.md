# Order-free reductions must special-case tiny structures

On unordered finite structures, an interpretation of positive dimension maps the empty structure to the empty structure and a one-element structure to a structure all of whose tuples are constant. Consequently the order-free first-order reduction from CNF satisfiability to independent set (vertices are literal occurrences, edges join complementary occurrences and occurrences of one clause) is correct on all structures with at least two elements but no order-free first-order reduction from SAT to IndependentSet is correct on all finite structures; reductions *nontrivial* in this sense, required to be correct only on structures with at least two elements, compose with ordinary reductions.

## Proof sketch

A singleton CNF structure may be satisfiable or not depending on its one clause, whereas its interpreted graph structures fall into a class on which independent-set membership is determined; compare the two singleton cases. Karp's occurrence-graph construction handles all larger structures.

## Depends on

- [First-order and quantifier-free reductions](first-order-reductions.md)

## Proof depends on

- [Pullback of formulas along interpretations](pullback-along-interpretations.md)

## Sources

- R. M. Karp, "Reducibility among Combinatorial Problems", in Complexity of Computer Computations, Plenum Press, 85–103, 1972.
- N. Immerman, Descriptive Complexity, Springer, 1999.
