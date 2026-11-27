# A linear-size reduction from 3SAT to Hamiltonian cycle

There is a linear reduction from 3-SAT to Hamiltonian Cycle: a polynomial-time algorithm that maps a 3-CNF formula with $n$ variables and $m$ clauses to a graph whose size is bounded by $O(n+m)$ and which has a Hamiltonian cycle iff the formula is satisfiable.

## Proof sketch

(Derived.) Each variable gets a diamond-shaped row traversed left-to-right (true) or right-to-left (false); a clause node is attached by a detour to the rows of its literals at private positions, so the number of nodes per row is proportional to the number of occurrences of the variable, and the directed graph has $O(n+m)$ vertices and arcs (Sipser's diamond construction instead gives each of the $n$ rows a pair of nodes per clause and thus $\Theta(nm)$ size). The standard three-vertex splitting turns it into an undirected graph with linear blow-up. Adding a twin $v'$ of a vertex $v$ with the same neighbours and pendant vertices at $v$ and $v'$ turns Hamiltonian cycles into Hamiltonian paths, so the same bound holds for directed and undirected Hamiltonian Path.

## Depends on

- [HAMILTONIAN CYCLE (UNDIRECTED) as a decision problem](../../np-completeness/paths-cycles-and-subgraphs/undirected-hamiltonian-cycle/hamiltonian-cycle-undirected-dec.md)
- [The 3SAT decision problem](../../np-completeness/satisfiability/3-satisfiability/sat3-dec.md)

## Proof depends on

- [DIRECTED HAMILTONIAN PATH is NP-complete](../../np-completeness/paths-cycles-and-subgraphs/hamiltonian-path-in-directed-graphs/directed-hamiltonian-path-np-complete.md)
- [The HAMPATH problem](../../np-completeness/paths-cycles-and-subgraphs/hamiltonian-path-in-directed-graphs/part-01/ham-path-dec.md)

## Sources

- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Section 14.2, Theorem 14.6 and the definition of a linear reduction preceding it (Exercise 14.2(e)).
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
