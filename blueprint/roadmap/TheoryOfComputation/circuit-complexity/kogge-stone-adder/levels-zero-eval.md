# Level 0 computes generate and propagate

Let $x$ and $y$ be $n$-bit vectors and $c$ a carry
bit, and evaluate level $0$ of the adder on the bits of $x$, the bits of $y$ and $c$. For every
bit $i < n$, the gate holding the generate signal of bit $i$ carries the generate signal, and the
gate holding its propagate signal carries the propagate signal, of the block consisting of bit $i$
alone, namely $x_i \wedge y_i$ and $x_i \oplus y_i$.
