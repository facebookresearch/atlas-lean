# Well-formed encoded circuits

A list $C = (g_0, \dots, g_{m-1})$ of encoded gates is
well-formed when every NOT, AND or OR gate references only strictly earlier gates: for every
$j < m$ such that $g_j = (k, r)$ has kind $k \in \{2, 3, 4\}$, every entry $a$ of $r$ satisfies
$a < j$.
