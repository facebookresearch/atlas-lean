# MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS with `K = 4` is NP-complete

The decision problem MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS with `K = 4` is NP-complete: it
belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

The language inherits the requirement $K \le |V|$ of the general problem, so graphs with fewer
than four vertices are rejected; padding with isolated vertices relates it to the unrestricted
input size.

Source: Bley and Neto (2010), Theorem 3 and its proof; Tovey (1984); Garey and Johnson (1979),
[ND41], comment (open there).
