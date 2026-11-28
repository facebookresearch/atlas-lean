# SHORTEST PATH WITH FORBIDDEN PAIRS is NP-complete

The SHORTEST PATH WITH FORBIDDEN PAIRS decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)`, a collection `C = {(a₁, b₁), …, (aₘ, bₘ)}` of pairs of vertices from `V`, an initial vertex `s ∈ V`, a final vertex `f ∈ V`, and a positive integer `K`. Question: is there a simple path from `s` to `f` in `G` that contains at most one vertex from each pair in `C` and has at most `K` edges?

## Sources

- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000), entry SHORTEST PATH WITH FORBIDDEN PAIRS in its graph theory section (decision version).
- V. Kann, "Polynomially bounded minimization problems that are hard to approximate", Nordic Journal of Computing 1 (1994), 317-331 (conference version: ICALP 1993, LNCS 700, 52-63, doi:10.1007/3-540-56939-1_61).
- H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of program test paths", IEEE Transactions on Software Engineering SE-2(3) (1976), 227-231, doi:10.1109/TSE.1976.233819.
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS.
