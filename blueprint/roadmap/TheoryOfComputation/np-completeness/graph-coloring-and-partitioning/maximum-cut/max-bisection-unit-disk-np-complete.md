# MAXIMUM BISECTION on unit disk graphs is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a list $P$ of distinct points of the plane with rational coordinates (the centers of disks of diameter $1$), the edge list $E$ of the unit disk graph of $P$ on the vertices $0, \dots, |P| - 1$ (two distinct points are adjacent exactly when they are at Euclidean distance at most $1$), and a bound $K > 0$, decide whether the vertices split into two parts of sizes $\lfloor |P| / 2 \rfloor$ and $\lceil |P| / 2 \rceil$ with at least $K$ edges between them.

## Sources

- J. Díaz and M. Kamiński, "MAX-CUT and MAX-BISECTION are NP-hard on unit disk graphs", Theoretical Computer Science 377 (2007), 271-276, doi:10.1016/j.tcs.2007.02.013 (preprint arXiv:cs/0609128), Corollary 11.
- ISGCI, class "unit disk" (gc_389), problem Maximum bisection, NP-complete.
