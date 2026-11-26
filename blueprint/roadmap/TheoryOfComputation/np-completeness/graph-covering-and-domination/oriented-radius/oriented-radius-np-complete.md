# ORIENTED RADIUS is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph on $\{0, \dots, n - 1\}$, given as an instance of ORIENTED DIAMETER (a vertex count, an edge list and a positive integer $K \le n$), decide whether its edges can be oriented so that some vertex reaches every vertex, and is reached from every vertex, by a directed path of at most $K$ arcs.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT64] ORIENTED DIAMETER, p. 205 (comment: "The variation in which 'diameter' is replaced by 'radius' is also NP-complete.").
- V. Chvátal and C. Thomassen, "Distances in orientations of graphs", Journal of Combinatorial Theory, Series B 24 (1978), 61-75, doi:10.1016/0095-8956(78)90078-3 (also Stanford report STAN-CS-75-517, 1975: deciding whether a graph admits an orientation of radius two is NP-hard).
