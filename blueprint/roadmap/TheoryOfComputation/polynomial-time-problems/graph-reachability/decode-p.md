# Decoding a PATH instance

Writing $1$ for true and $0$ for false, a bit string $x$ is parsed
by reading a unary number $s$ (a run of ones ended by a zero), then a unary number $t$ from the
rest, then a graph from what remains: a unary number $n$ followed by pairs $(u, v)$ of unary
numbers until the input ends. The result is $(s, t, n, E)$, with $E$ the list of these pairs in
order; there is no result unless the input ends right after $n$ or right after a complete pair.
