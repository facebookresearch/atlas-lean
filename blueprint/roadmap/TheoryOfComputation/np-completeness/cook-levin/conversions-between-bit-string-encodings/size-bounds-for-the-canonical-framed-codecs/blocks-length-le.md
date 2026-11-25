# Decoded block count is at most the input length

The framed form of a bit string $p = p_1 \cdots p_m$ is $1 p_1 \cdots 1 p_m 0$. For a natural number $F$, the
parser of at most $F$ framed blocks succeeds on a bit string $x$ with result $(p^1, \ldots, p^k)$ exactly when
$x$ is the concatenation of the framed forms of $p^1, \ldots, p^k$ and $k \le F$.

For every $F$ and every bit string $x$, if this parser succeeds on $x$ with result $(p^1, \ldots, p^k)$, then
$k \le |x|$.

Each framed block contains at least its final $0$.
