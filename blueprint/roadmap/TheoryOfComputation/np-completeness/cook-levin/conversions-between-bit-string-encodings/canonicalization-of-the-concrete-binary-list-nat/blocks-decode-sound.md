# Successful block parsing reconstructs the input

The framed form of a bit string $p = p_1 \cdots p_m$ is $1 p_1 \cdots 1 p_m 0$. For every natural number $F$ and
every bit string $x$, if the parser of at most $F$ framed blocks succeeds on $x$ with payloads
$(p^1, \ldots, p^k)$, then $x$ is the concatenation of the framed forms of $p^1, \ldots, p^k$.
