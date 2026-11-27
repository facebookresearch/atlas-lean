# Hamiltonian cycles of the source graph give zero-cost tours

Let $G$ be a simple graph on
the vertex set $\{0, \dots, n-1\}$, let $x$ be a Boolean array of length $n^2$ such that for all
$i, j < n$ the cell of $x$ at index $in + j$ exists and is true exactly when $i$ and $j$ are
adjacent in $G$, and let $y$ be the array output by the Hamiltonian-cycle to TSP converter on $x$,
with a Boolean cell read as $1$ if true and $0$ if false. Let $p$ be a Hamiltonian cycle in $G$
based at a vertex $a$, and let $p'$ be $p$ regarded as a closed walk in the complete graph on
$\{0, \dots, n-1\}$. Then $p'$ is a Hamiltonian cycle, $p'$ visits the same sequence of vertices
as $p$, and for every directed edge $(u, v)$ traversed by $p'$ the cell of $y$ at index $un + v$
exists, and the sum of these cells over the directed edges of $p'$ is $0$.
