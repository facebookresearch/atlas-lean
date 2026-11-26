# NP-completeness of partitioning a graph into at most $k$ cliques

Fix a natural number $k \ge 3$. Given a simple graph on at least $k$ vertices, decide whether its vertices can be partitioned into at most $k$ cliques. The encoded instance must carry the bound $k$; malformed inputs are rejected. For each such fixed $k$, this decision problem belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES, comment: remains NP-complete for all fixed `K ≥ 3`; solvable in polynomial time for `K ≤ 2`.
- R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (CLIQUE COVER, by transformation from GRAPH K-COLORABILITY).
- M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems", Theoretical Computer Science 1 (1976), 237-267, doi:10.1016/0304-3975(76)90059-1 (GRAPH 3-COLORABILITY).
