# Running a program on a binary string

For a code $c$ of a partial recursive function on
the natural numbers and a binary string $w$, running $c$ on $w$ evaluates $c$ at the number
encoding $w$; if this halts with output $m$, the result is the binary string encoded by $m$. The
result is undefined when the evaluation does not halt or $m$ encodes no binary string.
