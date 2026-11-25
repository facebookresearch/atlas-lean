# Vertex covers in terms of the pair bits

Let $n \in \mathbb{N}$, let $b$ be a list of
booleans with one entry for each pair in the list of vertex pairs $(i, j)$, $i < j < n$, and let
$G$ be the graph on the vertices $0, \dots, n - 1$ encoded by the pair bits $b$. Let $s$ be a
finite set of vertices of $G$ and $S$ a finite set of natural numbers such that each vertex $i$
lies in $s$ exactly when $i \in S$. Then $s$ is a vertex cover of $G$ if and only if, for every
index $q$ (counting from $0$) of the pair list whose entry in $b$ is true, the $q$-th pair
$(i_q, j_q)$ satisfies $i_q \in S$ or $j_q \in S$.
