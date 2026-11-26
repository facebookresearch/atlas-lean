# INDEPENDENT SET IN UNIT DISK GRAPHS is NP-complete

The INDEPENDENT SET IN UNIT DISK GRAPHS decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a finite set `P` of points in the plane with rational coordinates, given explicitly, and a positive integer `K ≤ |P|`. The unit disk graph of `P` has vertex set `P` and joins two points at (Euclidean) distance at most `1`. Question: is there a set of at least `K` points of `P`, no two at distance at most `1`, that is, an independent set of size at least `K` in the unit disk graph?

## Sources

- B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics 86(1-3) (1990), 165-177, doi:10.1016/0012-365X(90)90358-O.
- A. Tkachenko and H. Wang, "Dominating set, independent set, discrete k-center, dispersion, and related problems for planar points in convex position", arXiv:2501.00207 (2024), Section 1 (definition of the unit-disk graph of a point set; NP-hardness of independent set on unit-disk graphs, credited to Clark, Colbourn and Johnson).
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET.
