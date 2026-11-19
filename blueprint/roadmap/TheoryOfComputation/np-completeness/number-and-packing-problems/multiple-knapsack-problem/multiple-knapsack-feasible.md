# Feasible multiple-knapsack instances

Let a multiple-knapsack instance have items
$(w_0, v_0), \dots, (w_{k-1}, v_{k-1})$ (weight, value), knapsack capacities
$c_0, \dots, c_{m-1}$ and target $V$. The instance is feasible when there are
$a_0, \dots, a_{k-1} \in \{0, \dots, m\}$, where $a_j = b < m$ puts item $j$ in knapsack $b$
and $a_j = m$ leaves item $j$ out, such that for every $b < m$ the total weight
$\sum_{j : a_j = b} w_j$ is at most $c_b$, and the total value $\sum_{j : a_j < m} v_j$ is at
least $V$.
