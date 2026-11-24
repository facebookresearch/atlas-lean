# Reading an unterminated unary number rejects

Let $m$ be a mode, $c$ a stack other
than the input stack $X$, and $\lambda$, $\mu$ labels such that the verifier for $m$ runs at
$\lambda$ the unary reader onto $c$ that loops at $\lambda$ and exits to $\mu$. Let $l$ be a
list of Booleans from which no unary length can be read (it contains no false). Then for every
machine variable $v$ and all stack contents in which $X$ holds exactly the bits of $l$, the
verifier for $m$ goes from label $\lambda$ to the rejecting label no in at most $|l| + 1$
steps.
