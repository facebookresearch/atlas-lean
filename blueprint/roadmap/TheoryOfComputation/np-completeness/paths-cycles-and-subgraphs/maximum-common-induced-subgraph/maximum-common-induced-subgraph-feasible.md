# Feasible instances of MAXIMUM COMMON INDUCED SUBGRAPH

An instance
$(n_1, E_1, n_2, E_2, K)$ of MAXIMUM COMMON INDUCED SUBGRAPH is feasible when, writing $G_1$ and
$G_2$ for its first and second graphs, there are a set $A$ of vertices of $G_1$ and a set $B$ of
vertices of $G_2$ with $|A| \ge K$ and $|B| = |A|$, and a bijection $f : A \to B$ such that for
all $a, b \in A$, the vertices $a$ and $b$ are adjacent in $G_1$ if and only if $f(a)$ and $f(b)$
are adjacent in $G_2$.
