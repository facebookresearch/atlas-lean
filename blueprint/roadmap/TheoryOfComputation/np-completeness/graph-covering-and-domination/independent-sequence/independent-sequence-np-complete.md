# INDEPENDENT SEQUENCE is NP-complete

The decision problem INDEPENDENT SEQUENCE belongs to NP, and every decision problem in NP has a
polynomial-time many-one reduction to it.

A decision reduction from INDEPENDENT SET that preserves the answer: take two disjoint copies of the input graph $G$, apply the construction (added vertices forming a clique, with $v_i$ adjacent to $w_j$ exactly when $i \ge j$), and ask for size $2K$. An independent set of size $K$, listed in both copies in increasing index order, gives an independent sequence of size $2K$, the corresponding added vertex witnessing each next entry. Conversely, an independent sequence uses at most $2\alpha(G)$ original vertices and at most one clique vertex, so a no-instance cannot reach $2K$. This argument differs from the published size claim.

## Sources

- M. M. Halldórsson, "Approximations of weighted independent set and hereditary subset problems", Journal of Graph Algorithms and Applications 4(1) (2000), 1-16, doi:10.7155/jgaa.00020, Section 2.1, problem Max Independent Sequence (introduced by Blundo) and Proposition 2.3 (a reduction from INDEPENDENT SET; its size-preservation claim fails: from a triangle with target two, the construction admits the independent sequence $(w_3, v_1)$).
- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem MAXIMUM INDEPENDENT SEQUENCE.
