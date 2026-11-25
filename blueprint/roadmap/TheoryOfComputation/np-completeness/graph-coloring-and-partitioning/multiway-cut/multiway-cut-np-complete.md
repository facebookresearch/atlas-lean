# MULTIWAY CUT is NP-complete

Let MULTIWAY CUT be the decision problem that accepts exactly
the bitstrings decoding to a well-formed, feasible multiway cut instance: a simple undirected graph
on the vertices $0, \dots, n-1$, a list of distinct terminal vertices and a bound $K$ such that
deleting at most $K$ edges of the graph leaves no two terminals connected. Then MULTIWAY CUT is in
NP, and every decision problem in NP reduces to MULTIWAY CUT by a polynomial-time many-one
reduction.

## Sources

- Michael R. Garey and David S. Johnson, *Computers and Intractability* (1979), MULTIWAY CUT; Elias Dahlhaus, David S. Johnson, Christos H. Papadimitriou, Paul D. Seymour and Mihalis Yannakakis, "The complexity of multiterminal cuts", SIAM Journal on Computing 23 (1994), 864-894.
