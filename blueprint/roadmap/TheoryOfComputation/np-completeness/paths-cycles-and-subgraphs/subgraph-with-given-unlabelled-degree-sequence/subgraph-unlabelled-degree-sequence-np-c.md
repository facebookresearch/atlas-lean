# SUBGRAPH WITH GIVEN UNLABELLED DEGREE SEQUENCE is NP-complete

The SUBGRAPH WITH GIVEN UNLABELLED DEGREE SEQUENCE decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)` and a multiset `{d₁, …, dₙ}` of desired degrees, `n = |V|`. Question: does `G` contain a spanning subgraph `G' = (V, E')`, `E' ⊆ E`, whose multiset of vertex degrees is `{d₁, …, dₙ}`, with no constraint on which vertex gets which degree?

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985), 145-159, doi:10.1016/0196-6774(85)90025-2, comment on entry [4] DEGREE CONSTRAINED SUBGRAPH: "If, however, we are given just the desired degrees, and are not constrained as to which vertices get which degrees, the problem once more becomes NP-complete", attributed to Camerini and Maffioli.
- P. M. Camerini and F. Maffioli, "Unlabelled partition systems: optimization and complexity", SIAM Journal on Algebraic and Discrete Methods 5 (1984), 426-441, doi:10.1137/0605041.
