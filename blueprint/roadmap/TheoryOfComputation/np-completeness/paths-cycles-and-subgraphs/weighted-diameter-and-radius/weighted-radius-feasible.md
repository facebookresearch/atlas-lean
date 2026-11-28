# Edge-length assignments giving radius at most $K$

A WEIGHTED RADIUS instance $(n, E, C, K)$ is feasible when there are a rearrangement $\ell$ of the list $C$ (a permutation of its entries, with multiplicity), giving the $k$-th listed edge the length $\ell_k$, and a vertex $c$ such that every vertex $v$ is joined to $c$ by a path from $c$ to $v$ of length at most $K$. The length of a path is the sum of the lengths of the edges it traverses, where the edge joining $a$ and $b$ gets the length paired with the first listed edge equal to $(a, b)$ or $(b, a)$, and $0$ if there is none.

This expresses that, with these edge lengths, the graph has radius at most $K$.
