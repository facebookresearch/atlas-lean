# Outer-product matrix circuit

For a type $F$ of scalars and $m, n \in \mathbb{N}$, the
outer-product matrix circuit is the matrix arithmetic circuit for an $m \times 1$ matrix times a
$1 \times n$ matrix with exactly $mn$ gates: for $i < m$ and $j < n$, the gate for $(i, j)$
multiplies the input at entry $(i, 0)$ of the first matrix by the input at entry $(0, j)$ of
the second, and the output at $(i, j)$ is that gate.
