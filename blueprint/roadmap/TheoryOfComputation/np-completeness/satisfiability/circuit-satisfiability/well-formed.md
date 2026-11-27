# Well-formed circuit-satisfiability instances

An instance $(n, G)$ with gates
$G = (g_0, \dots, g_{m-1})$ is well formed when every gate $g_j = (o, a, b)$ satisfies
$o \le 5$, and moreover: if $o = 0$ or $o = 1$ then $a < n + j$ and $b < n + j$; if $o = 2$ then
$a < n + j$; and if $o = 3$ then $a < n$.
