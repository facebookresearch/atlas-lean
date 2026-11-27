# van der Zanden: bounded-bandwidth planar AND/OR NCL is PSPACE-complete

There is a constant $c$ such that configuration-to-configuration reachability for planar AND/OR constraint graphs of bandwidth at most $c$ (some vertex order places the endpoints of every edge at most $c$ apart) is $\mathsf{PSPACE}$-complete. The same holds for configuration-to-edge reachability.

## Proof sketch

Reduce from $H$-word reconfiguration for a fixed digraph $H$ for which it is $\mathsf{PSPACE}$-complete (Wrochna). For a word of length $n$, build a matrix of character vertices $X_{i,j}$ ($i\le n$, $j$ a letter) with a universal vertex $U_i$ per position joined to each $X_{i,j}$ by a weight-$2$ edge, so that orientations encode which letter sits at position $i$, and add gadgets between consecutive positions that forbid letter pairs outside $E(H)$; changing one letter becomes a sequence of edge reversals. Replacing the general vertices by AND/OR and crossover gadgets keeps the graph planar, and since $H$ is fixed the bandwidth is bounded by a constant depending only on $H$.

## Depends on

- [Nondeterministic constraint logic (AND/OR constraint graphs)](nondeterministic-constraint-logic.md)

## Proof depends on

- [Hearn–Demaine: planar AND/OR constraint-logic reachability is PSPACE-complete](planar-and-or-ncl-pspace-complete.md)
- [Wrochna: H-word reconfiguration is PSPACE-hard for a fixed H](h-word-reconfiguration-pspace-hard.md)

## Sources

- Tom C. van der Zanden, "Parameterized Complexity of Graph Constraint Logic", 10th International Symposium on Parameterized and Exact Computation (IPEC 2015), Leibniz International Proceedings in Informatics 43, 2015, Theorems 9 and 10.
