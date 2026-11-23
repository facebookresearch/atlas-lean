# Gates of level 0

Gate $j < 2n$ of level $0$ of the $n$-bit adder of $x$ and $y$ reads the
inputs $\lfloor j/2 \rfloor$ and $n + \lfloor j/2 \rfloor$, which carry bit $\lfloor j/2 \rfloor$
of $x$ and of $y$. For even $j$ it is an AND gate, the generate signal of that bit; for odd $j$ it
is an XOR gate, its propagate signal.
