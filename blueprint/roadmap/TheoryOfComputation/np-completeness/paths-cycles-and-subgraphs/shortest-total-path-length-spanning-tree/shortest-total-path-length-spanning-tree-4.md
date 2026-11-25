# SHORTEST TOTAL PATH LENGTH SPANNING TREE is NP-complete

The SHORTEST TOTAL PATH LENGTH SPANNING TREE decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)` and an integer bound `B ∈ ℤ⁺`. Question: is there a spanning tree `T` for `G` such that the sum, over all pairs of vertices `u, v ∈ V`, of the length of the path in `T` from `u` to `v` is no more than `B`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND3] SHORTEST TOTAL PATH LENGTH SPANNING TREE.
- D. S. Johnson, J. K. Lenstra, and A. H. G. Rinnooy Kan, "The complexity of the network design problem", Networks 8 (1978), 279-285, doi:10.1002/net.3230080402.
