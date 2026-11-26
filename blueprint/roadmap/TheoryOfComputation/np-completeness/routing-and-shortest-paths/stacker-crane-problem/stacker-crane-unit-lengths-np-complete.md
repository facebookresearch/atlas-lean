# STACKER-CRANE with unit lengths is NP-complete

The STACKER-CRANE with unit lengths decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a mixed graph `G = (V, A, E)` (`A` directed edges, `E` undirected edges) in which every edge has length `1`, and a bound `B ∈ ℤ⁺`. Question: is there a cycle in `G` that includes each directed edge in `A` at least once, traversing such edges only in the specified direction, and that has total length no more than `B`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE, comment.
- G. N. Frederickson, M. S. Hecht and C. E. Kim, "Approximation algorithms for some routing problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017.
