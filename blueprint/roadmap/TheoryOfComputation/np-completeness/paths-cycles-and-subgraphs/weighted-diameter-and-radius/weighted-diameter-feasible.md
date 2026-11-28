# Feasibility for WEIGHTED DIAMETER

An instance $(n, E, C, K)$ of WEIGHTED DIAMETER is feasible when there is a rearrangement $\ell$ of the list $C$ (a list with the same entries and multiplicities) such that, with edge lengths taken from $\ell$ by the first-match rule below, every pair of vertices $u, v$ (including $u = v$) is joined by a path in the graph of the instance whose length is at most $K$.

Here an edge $\{a, b\}$ has the length $\ell_j$ of the first index $j < \min(|E|, |\ell|)$ with $e_j = (a, b)$ or $e_j = (b, a)$, and $0$ if there is none ([edge length](edge-length.md)); no well-formedness is assumed, so for $n = 2$, $E = ((0, 1))$ and $C$ empty the edge has length $0$.
