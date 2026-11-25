# SINGLE-SINK EDGE INSTALLATION is NP-complete

The SINGLE-SINK EDGE INSTALLATION decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)`, a length function `l : E → ℕ`, a set of sources `S ⊆ V`, a sink `t ∈ V`, a demand function `d : S → ℤ⁺`, a finite set of cable types, each specified by its capacity and its cost per unit length, and a positive integer `K`. Question: is there a network of cables in the graph, consisting of an integral number of each cable type for each edge of `G`, that routes all the demands at the sources to the sink, the demand of each source following a single path from the source to the sink, whose total cost is at most `K`?

## Sources

- F. S. Salman, J. Cheriyan, R. Ravi and S. Subramanian, "Approximating the single-sink link-installation problem in network design", SIAM Journal on Optimization 11 (2001), 595-610, doi:10.1137/S1052623497321432 (conference version: "Buy-at-bulk network design: approximating the single-sink edge installation problem", SODA 1997, 619-628).
- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000), problem MINIMUM SINGLE-SINK EDGE INSTALLATION (decision version).
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
