# STACKER-CRANE PATH is NP-complete

The STACKER-CRANE PATH decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a mixed graph `G = (V, A, E)` (`A` directed edges, `E` undirected edges), a length `l(e) ∈ ℤ₀⁺` for each `e ∈ A ∪ E`, and a bound `B ∈ ℤ⁺`. Question: is there a path in `G` that includes each directed edge in `A` at least once, traversing such edges only in the specified direction, and that has total length no more than `B`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE, comment (p. 213: "The analogous path problem (with or without specified endpoints) is also NP-complete").
- G. N. Frederickson, M. S. Hecht, and C. E. Kim, "Approximation algorithms for some routing problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017 (the entry's reference for STACKER-CRANE).
