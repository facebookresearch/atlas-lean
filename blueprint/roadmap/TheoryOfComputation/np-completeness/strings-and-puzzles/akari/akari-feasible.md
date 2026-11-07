# Feasible Akari boards

Let $B$ be an Akari board with $m$ rows, let $n$ be the length of its
first row ($n = 0$ when there are no rows), and write $B_{r,c}$ for the entry in row $r$ and column
$c$, read as $1$ when there is no such entry. The board $B$ is feasible when there is a finite set
$S$ of pairs of natural numbers (the bulbs) such that every bulb $(r, c) \in S$ has $r < m$,
$c < n$ and $B_{r,c} = 0$; every cell $(r, c)$ with $r < m$, $c < n$ and $B_{r,c} = 0$ is
illuminated by some bulb in $S$; no bulb in $S$ illuminates a different bulb in $S$; and for every
$(r, c)$ with $r < m$, $c < n$ and $B_{r,c} \ge 2$, the number of bulbs $(r', c') \in S$ with
$|r - r'| + |c - c'| = 1$ equals $B_{r,c} - 2$.
