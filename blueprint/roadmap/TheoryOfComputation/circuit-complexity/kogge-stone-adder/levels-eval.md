# Each Kogge-Stone level is correct

Let $x$ and $y$ be $n$-bit vectors and $c$ a carry bit,
and evaluate level $0$ and the first $k$ Kogge-Stone levels of the adder on the bits of $x$, the
bits of $y$ and $c$. For every bit $i < n$, the gate holding the generate signal of bit $i$
carries the generate signal, and the gate holding its propagate signal carries the propagate
signal, of the block of the at most $2^k$ bits ending at $i$, that is, of the bits
$\max(0, i + 1 - 2^k), \dots, i$.
