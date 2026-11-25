# Total tardiness of a job order

Let $J = ((p_0, d_0), \dots, (p_{n-1}, d_{n-1}))$ be a
list of jobs with processing times $p_i \in \mathbb{N}$ and due dates $d_i \in \mathbb{N}$, and
set $(p_i, d_i) = (0, 0)$ for $i \ge n$. For a list $(j_1, \dots, j_m)$ of natural numbers (job
indices), let $C_k = p_{j_1} + \dots + p_{j_k}$ be the completion time of the $k$-th job when the
jobs are run in this order. The total tardiness of the order is
$\sum_{k=1}^{m} \max(C_k - d_{j_k}, 0)$.
