# Completeness of the tail of a chain

Let $v$ and $v'$ be assignments with $v'(2n) = v(n)$
for every $n$, let $C$ be a nonempty clause with $m + 1$ literals and let $z$ be a natural
number. Suppose that for every $j \le m$, $v'$ gives the fresh variable $\mathrm{fresh}(z - j)$
the value true exactly when $v$ satisfies some literal of the clause obtained from $C$ by
dropping its first $j$ literals, where $z - j$ is truncated subtraction ($0$ when $j > z$). Then
$v'$ satisfies every clause of $\mathrm{chainTail}(C, z)$.
