# Directed Hamiltonian path without prescribed endpoints is NP-complete

Deciding whether a finite directed graph has a Hamiltonian path (between some pair of vertices) is $\mathsf{NP}$-complete; graphs with no vertices are no-instances.

## Proof sketch

Reduce HAMPATH with designated endpoints $s,t$: add a fresh source $s'$ with a single arc $s'\to s$ and a fresh sink $t'$ with a single arc $t\to t'$. Every Hamiltonian path of the new graph must start at $s'$ and end at $t'$, so it exists iff the original graph has a Hamiltonian $s$–$t$ path.

## Depends on

- [The HAMPATH problem](../paths-cycles-and-subgraphs/hamiltonian-path-in-directed-graphs/part-01/ham-path-dec.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [HAMPATH is NP-complete](../paths-cycles-and-subgraphs/hamiltonian-path-in-directed-graphs/part-11/ham-path-dec-np-complete.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Theorem 2.18.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
