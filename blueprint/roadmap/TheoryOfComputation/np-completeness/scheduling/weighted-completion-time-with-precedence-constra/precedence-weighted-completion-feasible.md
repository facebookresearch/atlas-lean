# Feasible weighted completion instances

Let $(J, P, K)$ be an instance whose job list $J$
consists of $n$ jobs $(p_0, w_0), \dots, (p_{n-1}, w_{n-1})$ (processing time, weight). It is
feasible when there is an ordering $j_1, \dots, j_n$ of the indices $0, \dots, n-1$, each listed
exactly once, such that for every pair $(a, b)$ in $P$ the position of $a$ in the ordering is
smaller than the position of $b$, where an index that does not occur gets position $n + 1$, and
$\sum_{k=1}^{n} w_{j_k} (p_{j_1} + \dots + p_{j_k}) \le K$.
