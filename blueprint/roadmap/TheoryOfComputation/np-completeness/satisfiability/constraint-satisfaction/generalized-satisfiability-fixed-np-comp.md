# GENERALIZED SATISFIABILITY over fixed nonempty relations failing Schaefer's alternatives is NP-complete

Let $S$ be a fixed finite sequence of nonempty Boolean relations, each of positive arity $k$ and given by a list of tuples of length $k$, such that none of [Schaefer's six alternatives](schaefer-condition.md) holds for $S$. Then [GENERALIZED SATISFIABILITY over $S$](generalized-satisfiability-fixed-dec.md) belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

The relations must be nonempty. For the sequence of the empty unary relation and the ternary relation $\{FFF, FTT, TFT\}$, none of the six alternatives holds, yet every instance that uses the empty relation is unsatisfiable and every other instance is satisfied by the all-false assignment, so the problem over this sequence is in polynomial time.

## Sources

- T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the Tenth Annual ACM Symposium on Theory of Computing (STOC 1978), 216-226, doi:10.1145/800133.804350, Theorem 2.1 and the nonemptiness condition of Lemma 4.3.
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO6] GENERALIZED SATISFIABILITY (comment: for any fixed sequence of relations the problem is NP-complete unless one of six alternatives holds).
