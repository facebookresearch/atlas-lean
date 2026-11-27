# Bit encoding of a graph code

The bit encoding of a graph code with $n$ vertices and
adjacency matrix $A$ is the prefix-free encoding of $n$ followed by the $n^2$ entries of $A$, as
bits, in row-major order: $A_{0,0}, A_{0,1}, \dots, A_{0,n-1}, A_{1,0}, \dots, A_{n-1,n-1}$.
