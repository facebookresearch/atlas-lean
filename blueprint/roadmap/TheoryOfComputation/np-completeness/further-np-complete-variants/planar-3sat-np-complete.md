# Lichtenstein: planar 3SAT is NP-complete, also with three occurrences per variable

A CNF formula is **planar** if its variable–clause incidence graph has a planar embedding (here: an orthogonal drawing on the integer grid). Planar 3SAT is $\mathsf{NP}$-complete, and remains so when every variable occurs at most three times. Positive planar exact-one 3SAT (every clause has exactly three distinct positive variables, exactly one of which must be true, each variable occurring at most three times) is also $\mathsf{NP}$-complete; all reductions can be made parsimonious and of quadratic size.

## Proof sketch

Draw the incidence graph of an arbitrary 3-CNF on a grid with crossings, then replace each crossing by a planar crossover gadget of XOR-like clauses that forces the two crossing signals to be carried through unchanged and has exactly one satisfying completion for each pair of signals; finally split high-occurrence variables by cycles of implications.

## Depends on

- [The 3SAT decision problem](../satisfiability/3-satisfiability/sat3-dec.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [3-SAT WITH BOUNDED OCCURRENCES is NP-complete](../satisfiability/3-sat-with-bounded-occurrences/bounded-occurrence-three-sat-np-complete.md)
- [1-IN-3-SAT is NP-complete](../satisfiability/1-in-3-sat/one-in-three-sat-np-complete.md)

## Sources

- David Lichtenstein, "Planar Formulae and Their Uses", SIAM Journal on Computing 11(2), 1982.
- MIT Hardness Group et al., "ETH is Dead, Long Live SH", arXiv:2611.02650v2, 2026.
