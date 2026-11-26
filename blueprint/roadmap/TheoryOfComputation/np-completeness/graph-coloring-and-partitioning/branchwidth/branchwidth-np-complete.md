# BRANCHWIDTH is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph $G$ on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, and a natural number $K$, decide whether $G$ has branchwidth at most $K$: whether $G$ has at most one edge, or there is a tree whose vertices all have degree $1$ or $3$, with the edges of $G$ in bijection with its leaves, such that for every tree edge at most $K$ vertices of $G$ are incident with edges on both sides of it.

## Sources

- P. D. Seymour and R. Thomas, "Call routing and the ratcatcher", Combinatorica 14 (1994), 217-241, doi:10.1007/BF01215352 (branchwidth "is NP-hard for general graphs"; definitions in Section 1, (1.1)).
