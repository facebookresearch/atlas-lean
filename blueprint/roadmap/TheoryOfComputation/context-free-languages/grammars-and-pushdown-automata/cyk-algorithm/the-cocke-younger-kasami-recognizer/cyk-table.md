# The CYK table

The CYK table of a word $w$ up to length $l$ is a list of pairs of a word
and a cell, defined by recursion on $l$. Up to length $0$ it is empty. The table up to length
$l + 1$ is the table $t$ up to length $l$ followed by one entry for each position $i$ (counted
from $0$) with $i + l + 1 \le |w|$, in increasing order of $i$: the factor $u$ of $w$ of length
$l + 1$ starting at position $i$, together with the CYK cell of $u$ built from the cells recorded
in $t$.
