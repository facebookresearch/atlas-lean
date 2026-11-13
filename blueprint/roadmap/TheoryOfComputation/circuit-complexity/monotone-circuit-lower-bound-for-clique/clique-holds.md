# The clique function on adjacency-matrix bits

For a natural number $n$ and a bitstring
$x$, read $x$ as an $n \times n$ adjacency matrix in row-major order: the entry for a pair
$(a, b)$ is the bit of $x$ at position $an + b$, where a position beyond the end of $x$ reads as
false. The clique predicate holds for $n$ and $x$ when there is a set $S$ of exactly
$\lfloor n/3 \rfloor$ vertices among $0, \dots, n - 1$ such that the entry for $(a, b)$ is true
for all distinct $a, b \in S$.
