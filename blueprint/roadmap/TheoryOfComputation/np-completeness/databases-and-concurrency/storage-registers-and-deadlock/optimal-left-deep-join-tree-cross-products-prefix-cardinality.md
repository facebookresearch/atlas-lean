# Output cardinality of a join prefix

The output cardinality $|s_1, \dots, s_{k+1}|$ of joining the relations at positions $0, \dots, k$ of the order $π$: $\prod _{a \le k} |R_{π a}| \cdot \prod _{a < b \le k} f_{π a, π b}$. The selectivity $f_{a,b}$ is $p / q$, computed in the rationals (so $0$ when $q = 0$), for the first entry $(i, j, p, q)$ with $i = \min(a, b)$ and $j = \max(a, b)$. It is $1$ when there is no such entry (a cross product), and an entry with $i \ge j$ is never read.
