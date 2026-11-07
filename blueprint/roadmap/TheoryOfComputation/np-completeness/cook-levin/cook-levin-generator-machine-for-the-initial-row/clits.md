# Literals of a clause kind

Given natural numbers $i_c$ and $g'$, a list $y$ of natural
numbers, a base position $B$ and a clause kind $c$, the literal list of $c$ at base $B$ is the
list of the pairs $(B + \mathrm{off}(c, l), \mathrm{sg}(c, l))$ for $l = 0, 1, \dots,
\mathrm{nl}(c) - 1$ in order, where $\mathrm{nl}(c)$ is the number of literals of $c$,
$\mathrm{off}(c, l)$ is the offset of literal $l$ (computed from $i_c$, $g'$ and $y$) and
$\mathrm{sg}(c, l)$ is its sign.
