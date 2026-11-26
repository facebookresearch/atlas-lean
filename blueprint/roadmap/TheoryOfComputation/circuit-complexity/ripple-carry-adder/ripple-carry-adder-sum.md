# Sum bits of the ripple-carry adder

Let $x, y$ be $n$-bit vectors, $c$ a bit and $i < n$,
and evaluate the $n$-bit ripple-carry adder, with its gates read as Boolean XOR, AND and OR, on the
input whose entry $j$ is bit $j$ of $x$ and entry $n + j$ is bit $j$ of $y$ for $j < n$ (bit $0$
being the least significant), and whose entry $2n$ is $c$. Its output number $i$ (outputs being
numbered from $0$) is bit $i$ of the $n$-bit sum $(x + y + c) \bmod 2^n$, reading $x$ and $y$ as
natural numbers below $2^n$.
