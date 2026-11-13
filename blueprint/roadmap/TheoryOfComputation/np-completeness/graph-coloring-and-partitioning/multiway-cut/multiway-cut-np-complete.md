# MULTIWAY CUT is NP-complete

Let MULTIWAY CUT be the decision problem that accepts exactly
the bitstrings decoding to a well-formed, feasible multiway cut instance: a simple undirected graph
on the vertices $0, \dots, n-1$, a list of distinct terminal vertices and a bound $K$ such that
deleting at most $K$ edges of the graph leaves no two terminals connected. Then MULTIWAY CUT is in
NP, and every decision problem in NP reduces to MULTIWAY CUT by a polynomial-time many-one
reduction.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MULTIWAY CUT; E. Dahlhaus et al., "The complexity of multiterminal cuts" (1994).
