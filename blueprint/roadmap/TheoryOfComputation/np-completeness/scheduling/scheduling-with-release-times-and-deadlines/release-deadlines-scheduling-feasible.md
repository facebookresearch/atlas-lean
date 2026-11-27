# Feasible single-machine schedules with release times and deadlines

A release-deadlines
instance with jobs $(p_j, r_j, d_j)$ for $j < n$ is feasible when there are start times
$s_0, \dots, s_{n-1} \in \mathbb{N}$ such that $r_j \le s_j$ and $s_j + p_j \le d_j$ for every
$j < n$, and for all $a < b < n$ either $s_a + p_a \le s_b$ or $s_b + p_b \le s_a$.
