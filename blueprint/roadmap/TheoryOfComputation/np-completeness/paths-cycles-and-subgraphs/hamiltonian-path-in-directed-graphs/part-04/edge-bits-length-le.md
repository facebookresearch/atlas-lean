# Length bound for the bit encoding of an edge list

Let $B$ be a natural number and $E$ a
list of pairs of natural numbers such that every pair $(u, v)$ in $E$ has $u \le B$ and
$v \le B$. Then the bit encoding of $E$, which writes each pair $(u, v)$ as $u$ ones, a zero,
$v$ ones and a zero, has length at most $|E| \cdot (2B + 2)$, where $|E|$ is the length of $E$.
