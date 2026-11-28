# GEOMETRIC TRAVELING SALESMAN is NP-complete

The decision problem GEOMETRIC TRAVELING SALESMAN, the language of encoded instances that have a tour whose sum of [discretized](discrete-dist.md) edge lengths $\lceil \lVert p - q \rVert \rceil$ (each Euclidean edge length rounded up, the return edge included) is at most $B$, belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND23] GEOMETRIC TRAVELING SALESMAN, with the discretized distance. The variant with exact Euclidean edge lengths is NP-hard by the same reductions but is not known to lie in NP, since comparing sums of square roots is not known to be polynomial; it is not the language here.
- C. H. Papadimitriou, "The Euclidean travelling salesman problem is NP-complete", Theoretical Computer Science 4 (1977), 237-244, doi:10.1016/0304-3975(77)90012-3.
- M. R. Garey, R. L. Graham and D. S. Johnson, "Some NP-complete geometric problems", Proc. 8th Annual ACM Symposium on Theory of Computing (1976), 10-22, doi:10.1145/800113.803626.
