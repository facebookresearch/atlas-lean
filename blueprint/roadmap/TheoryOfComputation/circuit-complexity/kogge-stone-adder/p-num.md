# Propagate gate of a bit in the Kogge–Stone adder

For natural numbers $n$, $k$ and $i$,
$p_n(k, i)$ is the index of the gate holding the propagate signal of bit $i$ after level $k$ of
the $n$-bit carry-lookahead adder: $p_n(0, i) = 2i + 1$, and $p_n(k + 1, i) = 2n + 3nk + 3i + 2$,
where $2n + 3nk$ is the number of gates in levels $0, \dots, k$.
