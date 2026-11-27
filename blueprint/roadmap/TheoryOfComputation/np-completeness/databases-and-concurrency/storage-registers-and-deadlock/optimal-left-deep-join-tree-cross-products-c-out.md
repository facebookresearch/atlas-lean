# Cost of a left-deep join order

The cost $C_{\mathrm{out}}$ of the left-deep tree joining the relations in the order $π$: the sum of the output cardinalities of its joins, $\sum _{k \ge 1} |s_1, \dots, s_{k+1}|$. The selectivity $f_{a,b}$ is $p / q$, computed in the rationals (so $0$ when $q = 0$), for the first entry $(i, j, p, q)$ with $i = \min(a, b)$ and $j = \max(a, b)$. It is $1$ when there is no such entry (a cross product), and an entry with $i \ge j$ is never read.
