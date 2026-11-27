# Edge-length assignments giving radius at least $K$

An instance $(n, E, C, K)$ is feasible when there is a rearrangement $w$ of the list $C$ (a permutation of its entries, with multiplicity), with edge lengths taken from $w$ by the first-match rule below, such that for every vertex $v$ there is a vertex $u$ for which every path from $v$ to $u$ in the graph of the instance has length at least $K$. Here the length of a path is the sum of the lengths of its edges.

This expresses that, with these edge lengths, the graph has radius at least $K$.

Here an edge $\{a, b\}$ has the length $w_j$ of the first index $j < \min(|E|, |w|)$ with $e_j = (a, b)$ or $e_j = (b, a)$, and $0$ if there is none ([edge length](edge-length.md)); no well-formedness is assumed, so for $n = 2$, $E = ((0, 1))$ and $C$ empty the edge has length $0$.
