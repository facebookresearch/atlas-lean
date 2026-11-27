# A linear-size reduction from 3SAT to Hamiltonian path and cycle

There is a polynomial-time reduction from 3-CNF formulas with $n$ variables and $m$ clauses to directed graphs with $O(n+m)$ vertices and arcs that have a Hamiltonian path (equivalently, after closing the path, a Hamiltonian cycle) iff the formula is satisfiable; an undirected version is obtained by the standard three-vertex splitting with linear blow-up. (Sipser's diamond construction gives each of the $n$ rows a pair of nodes per clause and thus $\Theta(nm)$ size; the sparse version attaches each clause node only to the rows of its three variables.)

## Proof sketch

Each variable gets a diamond-shaped row traversed left-to-right (true) or right-to-left (false); a clause node is attached by a detour to the rows of its literals at private positions, so the number of nodes per row is proportional to the number of occurrences of the variable.

## Depends on

- [The HAMPATH problem](../../np-completeness/paths-cycles-and-subgraphs/hamiltonian-path-in-directed-graphs/part-01/ham-path-dec.md)
- [The 3SAT decision problem](../../np-completeness/satisfiability/3-satisfiability/sat3-dec.md)

## Proof depends on

- [DIRECTED HAMILTONIAN PATH is NP-complete](../../np-completeness/paths-cycles-and-subgraphs/hamiltonian-path-in-directed-graphs/directed-hamiltonian-path-np-complete.md)

## Sources

- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015.
