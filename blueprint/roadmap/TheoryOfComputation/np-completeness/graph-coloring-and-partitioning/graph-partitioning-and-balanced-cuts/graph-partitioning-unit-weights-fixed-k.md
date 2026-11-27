# NP-completeness of unit-weight graph partitioning with a fixed block-size bound

Fix a natural number $K \ge 3$. Given a graph with unit vertex weights and unit edge lengths and a positive cut bound $J$, decide whether its vertices can be partitioned into blocks of at most $K$ vertices with at most $J$ edges joining different blocks. For each such fixed $K$, this decision problem belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND14] GRAPH PARTITIONING, p. 209, comment: "Remains NP-complete for fixed K ≥ 3 even if all vertex and edge weights are 1" (the entry's reference is [Hyafil and Rivest, 1973], transformation from PARTITION INTO TRIANGLES).
- L. Hyafil and R. L. Rivest, "Graph partitioning and constructing optimal decision trees are polynomial complete problems", IRIA-Laboria Rapport 33 (1973).
