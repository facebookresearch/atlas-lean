# The unary reader rejects an unterminated number

Let $c \ne X$ be a stack and $s$, $t$
labels such that the verifier runs, at $s$, the unary reader from $X$ onto the counter $c$ that
loops at $s$ and exits to $t$. If $X$ holds a bit list $l$ on which reading a unary number
fails, that is, $l$ consists of ones only, then from label $s$, in any internal state and with
any other stacks, the verifier reaches the rejecting label within at most $|l| + 1$ steps.
