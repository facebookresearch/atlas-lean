# Correctness of the CYK table

Let $g$ be a context-free grammar in Chomsky normal form and
$w$ a word. For every $l$, the CYK table of $w$ up to length $l$ is correct, and for all $j$ and
$m$ with $0 < m \le l$ and $j + m \le |w|$, some entry of the table has as its word the factor of
$w$ of length $m$ starting at position $j$ (positions counted from $0$).
