# Feasible RCPSP instances

Let $(J, P, C, D)$ be an RCPSP instance with $n$ jobs, where
job $j < n$ has duration $p_j$ and resource demand $r_j$, and set $p_j = 0$ for $j \ge n$. The
instance is feasible when there are start times $s_0, \dots, s_{n-1} \in \mathbb{N}$, with
$s_j = 0$ for $j \ge n$, such that every job finishes by the deadline ($s_j + p_j \le D$ for all
$j < n$), every precedence pair $(a, b) \in P$ satisfies $s_a + p_a \le s_b$, and at every time
$t < D$ the total demand of the jobs active at $t$ (the jobs $j < n$ with
$s_j \le t < s_j + p_j$) is at most $C$.
