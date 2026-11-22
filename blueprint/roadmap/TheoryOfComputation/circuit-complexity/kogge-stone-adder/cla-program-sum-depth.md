# Depth of the sum gates

For all natural numbers $n$, $K$ and $i < n$, in the gate program
of the $n$-bit adder with $K$ Kogge–Stone levels, the sum gate of bit $i$ in the final level
(gate $3i + 2$ of that level) has depth $2$ if $i = 0$ and depth $\max(2K + 1, K + 2) + 2$
otherwise, where inputs have depth $0$ and each gate is one deeper than its deepest argument.
