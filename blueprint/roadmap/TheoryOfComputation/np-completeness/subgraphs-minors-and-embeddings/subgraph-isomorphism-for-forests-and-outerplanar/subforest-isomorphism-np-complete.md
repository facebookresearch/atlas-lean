# SUBFOREST ISOMORPHISM is NP-complete

The SUBFOREST ISOMORPHISM decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a tree `G = (V₁, E₁)` and a forest `H = (V₂, E₂)`. Question: does `G` contain a subgraph isomorphic to `H`, i.e., is there an injective map from `V₂` to `V₁` sending every edge of `H` to an edge of `G`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), Section 4.2, Theorem 4.6 ("SUBFOREST ISOMORPHISM is NP-complete"), pp. 104-106, and problem [GT48] SUBGRAPH ISOMORPHISM, p. 202 (comment: "remains NP-complete if `G` is a tree and `H` is a forest (see Chapter 4)").
