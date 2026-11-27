# Feasible instances of OPTIMAL LEFT-DEEP JOIN TREE WITH CROSS PRODUCTS

An instance of OPTIMAL LEFT-DEEP JOIN TREE WITH CROSS PRODUCTS is feasible when some left-deep tree (an order $π$ of the relations, cross products allowed) has $C_{\mathrm{out}} \le K$. The selectivity $f_{a,b}$ is $p / q$, computed in the rationals (so $0$ when $q = 0$), for the first entry $(i, j, p, q)$ with $i = \min(a, b)$ and $j = \max(a, b)$. It is $1$ when there is no such entry (a cross product), and an entry with $i \ge j$ is never read.
