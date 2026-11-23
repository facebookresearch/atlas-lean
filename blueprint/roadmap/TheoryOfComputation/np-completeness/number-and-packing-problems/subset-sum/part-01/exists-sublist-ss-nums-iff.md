# Sublists of the reduction's numbers as vertex and pair sets

Let $n, t \in \mathbb{N}$, let
$b$ be a list of booleans, and let $m$ be the length of the list of vertex pairs $(i, j)$,
$i < j < n$. Write $x_v$ for the vertex number of $v$ and $y_q$ for the pair number of $q$ defined
from $n$ and $b$. Some sublist (a subsequence, not necessarily contiguous) of the reduction's
numbers for $n$ and $b$ sums to $t$ if and only if there are finite sets $S$ of vertices $v < n$
and $F$ of pair indices $q < m$ with $\sum_{v \in S} x_v + \sum_{q \in F} y_q = t$.
