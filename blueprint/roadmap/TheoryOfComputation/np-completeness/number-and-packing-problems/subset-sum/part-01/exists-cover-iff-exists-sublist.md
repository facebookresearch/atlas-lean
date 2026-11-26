# Vertex covers of size $k$ match subset sums hitting the target

Let $k, n \in \mathbb{N}$
and let $b$ be a list of booleans with one entry for each pair in the list of vertex pairs
$(i, j)$, $i < j < n$. Let $G$ be the graph on the vertices $0, \dots, n - 1$ encoded by the pair
bits $b$. Then $G$ has a vertex cover with exactly $k$ vertices if and only if some sublist (a
subsequence, not necessarily contiguous) of the reduction's numbers for $n$ and $b$ sums to the
reduction's target for $k$, $n$ and $b$.
