# The size invariant survives a new literal occurrence

Let $s$ and $s'$ be states of
the 3-COLOR construction with next free vertices $n$ and $n'$, and let $l = (x, p)$ be a
literal. Suppose that $s$ satisfies the size invariant after $\tau$ tokens, that the earlier
occurrences of $s'$ are those of $s$ preceded by the occurrence of $l$ with literal vertex $n$
and negation vertex $n + 1$, and that $n \le n' \le n + 5$. Then $s'$ satisfies the size
invariant after $\tau + t$ tokens, where $t$ is the number of tokens of $l$ on the token
stack.
