# 3SAT, 3-colourability, Independent Set, Clique and Vertex Cover are NP-complete under projections

The ordered-structure versions of 3SAT, 3-colourability (of graphs and of simple graphs), Independent Set, Clique and Vertex Cover are each definable in existential second-order logic, lie in $\mathsf{NP}$ under the standard structure encoding, and are $\mathsf{NP}$-complete under BIT-free quantifier-free projections (and hence under logspace reductions); each is polynomial-time interreducible with its classical string version.

## Proof sketch

ESO sentences guess the witness (assignment, colouring, vertex set). Hardness: compose the projection from any NP query to SAT with the textbook gadget reductions (SAT→3SAT clause splitting, 3SAT→3-colouring, 3SAT→independent set, complements and graph complements for clique and vertex cover), all of which are quantifier-free projections.

## Depends on

- [First-order interpretations, first-order reductions and quantifier-free projections](first-order-reductions.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Immerman: SAT is NP-complete under BIT-free quantifier-free projections](sat-np-complete-under-projections.md)

## Sources

- Richard M. Karp, "Reducibility among Combinatorial Problems", Complexity of Computer Computations, 1972.
- Michael R. Garey and David S. Johnson, "Computers and Intractability: A Guide to the Theory of NP-Completeness", W. H. Freeman, 1979.
- Neil Immerman, "Descriptive Complexity", Springer, 1999.
- Neil Immerman and Susan Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 1995.
