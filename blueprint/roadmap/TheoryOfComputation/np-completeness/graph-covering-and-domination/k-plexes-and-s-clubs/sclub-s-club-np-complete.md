# s-CLUB is NP-complete for every fixed s ≥ 2

For every natural number $s \ge 2$, the following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, and a positive integer $K$, decide whether some set of at least $K$ vertices induces a subgraph of diameter at most $s$.

## Sources

- B. Balasundaram, S. Butenko and S. Trukhanov, "Novel approaches for analyzing biological networks", Journal of Combinatorial Optimization 10(1) (2005), 23-39, doi:10.1007/s10878-005-1857-x.
- S. Hartung, C. Komusiewicz and A. Nichterlein, "On structural parameterizations for the 2-club problem", SOFSEM 2013, Lecture Notes in Computer Science 7741 (2013), 233-243, doi:10.1007/978-3-642-35843-2_21 (Section 1: the problem statement, and "For all s ≥ 1, s-Club is NP-complete on graphs of diameter s+1", citing Balasundaram, Butenko and Trukhanov).
