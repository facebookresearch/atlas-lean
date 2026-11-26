# van der Zanden: bounded-bandwidth planar AND/OR NCL is PSPACE-complete

There is a constant $b$ such that configuration-to-configuration reachability for planar AND/OR constraint graphs admitting a vertex order of bandwidth at most $b$ (every edge joins vertices at most $b$ apart in the order) is $\mathsf{PSPACE}$-complete.

## Proof sketch

Compile a polynomial-space Turing machine's tape into a long chain of identical constant-size cells, each a planar AND/OR network simulating one tape cell and its neighbours' interactions through boundary wires; laying the cells out row by row gives constant bandwidth.

## Depends on

- [Nondeterministic constraint logic (AND/OR constraint graphs)](nondeterministic-constraint-logic.md)

## Proof depends on

- [Hearn–Demaine: planar AND/OR constraint-logic reachability is PSPACE-complete](planar-and-or-ncl-pspace-complete.md)
- [Wrochna: H-word reconfiguration is PSPACE-hard for a fixed H](h-word-reconfiguration-pspace-hard.md)

## Sources

- Tom C. van der Zanden, "Parameterized Complexity of Graph Constraint Logic", 10th International Symposium on Parameterized and Exact Computation, 2015, Theorem 6.
