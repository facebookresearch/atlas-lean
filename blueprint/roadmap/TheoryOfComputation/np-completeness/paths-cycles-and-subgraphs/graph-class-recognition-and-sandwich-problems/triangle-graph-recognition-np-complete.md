# RECOGNITION OF TRIANGLE GRAPHS (PI* GRAPHS) is NP-complete

The RECOGNITION OF TRIANGLE GRAPHS (PI* GRAPHS) decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph $G = (V, E)$. Question: is $G$ a [triangle graph](is-triangle-graph.md) (a PI* graph)? That is, can each vertex $v$ be assigned the convex hull of a closed interval on the line $y = 1$ and a closed interval on the line $y = 0$, at least one of the two a single point (both may be, giving a segment), so that two distinct vertices are adjacent exactly when their regions intersect?

## Sources

- G. B. Mertzios, "The recognition of triangle graphs", Theoretical Computer Science 438 (2012), 34-47, doi:10.1016/j.tcs.2012.02.042.
- conference version in STACS 2011, LIPIcs 9, 591-602, doi:10.4230/LIPIcs.STACS.2011.591.
- ISGCI, class "PI*" (gc_290), problem Recognition.
