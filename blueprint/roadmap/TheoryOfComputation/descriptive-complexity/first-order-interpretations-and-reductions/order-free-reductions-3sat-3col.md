# Order-free first-order reductions between 3-SAT and 3-colorability

There are order-free first-order (tagged) interpretations reducing 3-SAT to 3-colorability and conversely: (1) from a 3-CNF structure, the palette–variable–clause gadget graph built by an interpretation is 3-colorable iff the formula is satisfiable (also with loopless simple graphs as targets); (2) from a graph, the 3-CNF structure with variables $x(v, c)$, clauses $x(v,0) \vee x(v,1) \vee x(v,2)$ and $\neg x(u,c) \vee \neg x(v,c)$ for edges $uv$, is satisfiable iff the graph is 3-colorable. Hence 3SAT and 3COL are equivalent under order-free first-order reductions.

## Proof sketch

Each gadget is defined by quantifier-free formulas on tagged copies of tuples of the input; correctness is the standard gadget argument for OR-gadgets with a palette triangle.

## Depends on

- [CNF formulas, graphs and sized graphs as finite structures](cnf-formulas-and-graphs-as-finite-structures.md)

## Proof depends on

- [Pullback of formulas along interpretations](pullback-along-interpretations.md)
- [3-COLOR is NP-complete](../../np-completeness/graph-coloring-and-partitioning/graph-3-coloring/part-09/col3-dec-np-complete.md)
- [3SAT is NP-complete](../../np-completeness/satisfiability/3-satisfiability/sat3-dec-np-complete.md)

## Sources

- M. Sipser, Introduction to the Theory of Computation, 3rd ed., Cengage Learning, 2013.
- M. R. Garey and D. S. Johnson, Computers and Intractability: A Guide to the Theory of NP-Completeness, W. H. Freeman, 1979.
- N. Immerman, Descriptive Complexity, Springer, 1999.
