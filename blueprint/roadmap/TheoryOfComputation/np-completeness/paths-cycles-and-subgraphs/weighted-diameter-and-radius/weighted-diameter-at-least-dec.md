# WEIGHTED DIAMETER ($K$ or greater) as a decision problem

The decision problem WEIGHTED DIAMETER with diameter $K$ or greater accepts a bitstring $x$ exactly when the canonical bitstring decoding of $x$ as a quadruple $(n, E, C, K)$ succeeds and returns an instance of WEIGHTED DIAMETER that is well formed and feasible for this variant: some rearrangement of $C$, assigned to the edges in order, leaves a pair of vertices every path between which has length at least $K$. Every bitstring that does not decode is rejected.
