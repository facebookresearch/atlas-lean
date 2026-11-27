# The verifier as a row-by-row check

Let $m$ be a mode and $x$, $w$ bit lists.
Suppose that $x$ decodes to $(k, n, \mathit{bits})$, that $w$ has at least $n$ bits, and that
exactly $k$ of the first $n$ bits of $w$ are set. Then the verifier for mode $m$ on input $x$
and witness $w$ returns the same value as the row-by-row check for mode $m$ of the first $n$
bits of $w$ against the pair bits $\mathit{bits}$.
