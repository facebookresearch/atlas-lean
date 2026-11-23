# Bits pushed for a list of edges

For a list of edges $e_1, \dots, e_k$ (pairs of
natural numbers), the output is the concatenation $b(e_k) \cdots b(e_1)$, where $b(u, v)$ is
$u$ ones, a zero, $v$ ones and a zero.

This is what the output stack gains, read top-first, when the edges are pushed in the order
$e_1, \dots, e_k$.
