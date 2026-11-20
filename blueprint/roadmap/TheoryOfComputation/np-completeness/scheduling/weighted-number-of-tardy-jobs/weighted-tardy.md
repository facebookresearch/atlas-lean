# Weighted number of tardy jobs of an ordering

Let $J$ be a list of jobs, each a triple of
natural numbers (processing time, due date, weight), and write $(p_i, d_i, w_i)$ for the job at
position $i$ of $J$, counting from $0$, with $(p_i, d_i, w_i) = (0, 0, 0)$ when $J$ has no
position $i$. For a list $(j_1, \dots, j_m)$ of natural numbers, the weighted number of tardy
jobs of this order is the sum of $w_{j_k}$ over all $k$ with $d_{j_k} < C_k$, where
$C_k = p_{j_1} + \dots + p_{j_k}$ is the completion time of the $k$-th job.
