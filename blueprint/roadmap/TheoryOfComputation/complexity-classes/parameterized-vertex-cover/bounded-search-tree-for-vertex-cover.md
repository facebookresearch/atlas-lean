# Bounded search tree for vertex cover

Whether a graph with $n$ vertices and $m$ edges has a vertex cover of size at most $k$ can be decided in $O(2^k (n + m))$ time by the following branching algorithm, which also returns such a cover when one exists: if no edge remains, accept; if $k = 0$, reject; otherwise pick an edge $(u, v)$ and recurse on $(G - u, k - 1)$ and on $(G - v, k - 1)$. Correctness rests on the fact that every vertex cover contains $u$ or $v$; the recursion tree has depth at most $k$ and hence at most $2^k$ leaves.

## Expansion

This page becomes ready once these prerequisites are stated:

- Executable graph representations and size measures (proof prerequisite; not yet stated)
- Algorithm cost model (statement prerequisite; not yet stated)
- The statement must be checked against the cited sources, which have not been opened

## Sources

- R. G. Downey and M. R. Fellows, *Parameterized Complexity*, Springer, 1999
- M. Cygan et al., *Parameterized Algorithms*, Springer, 2015
