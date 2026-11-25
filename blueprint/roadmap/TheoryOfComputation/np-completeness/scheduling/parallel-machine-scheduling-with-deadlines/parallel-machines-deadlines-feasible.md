# Feasible schedules on parallel machines with deadlines

An instance consisting of jobs
$(p_1, d_1), \dots, (p_k, d_k)$, where job $j$ has processing time $p_j$ and deadline $d_j$, and
a number $m$ of machines is feasible when there are start times $s_1, \dots, s_k \in \mathbb{N}$
and machines $\mu_1, \dots, \mu_k \in \{0, \dots, m - 1\}$ such that $s_j + p_j \le d_j$ for
every $j$, and for all $a \ne b$ with $\mu_a = \mu_b$, either $s_a + p_a \le s_b$ or
$s_b + p_b \le s_a$.
