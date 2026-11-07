# Well-formed situation tables for the transition clauses

Given a layout with label/state
block size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, a current-code table $\ell$, a
next-code table $\nu$ and a window table $w$, the tables are well formed for situation $i$ at
height $H$ when $\ell(i) < A$, $\nu(i) < A$, $w(i, k, j) < g$ for all $k < K$ and $j < d$, and
$d \le H$.
