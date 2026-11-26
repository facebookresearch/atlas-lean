# The unary reader on a terminated number

Let $c \ne X$ be a stack and $s$, $t$ labels
such that the verifier runs, at $s$, the unary reader from $X$ onto the counter $c$ that loops at
$s$ and exits to $t$. Let $k, j$ be natural numbers and $r$ a list of bits. If $X$ holds $k$ ones,
then a zero, then $r$, and $c$ holds exactly $j$ units, then from label $s$, in any internal
state, the verifier reaches label $t$ in exactly $k + 1$ steps, with $X$ holding $r$, $c$ holding
exactly $k + j$ units, and every other stack as at the start.
