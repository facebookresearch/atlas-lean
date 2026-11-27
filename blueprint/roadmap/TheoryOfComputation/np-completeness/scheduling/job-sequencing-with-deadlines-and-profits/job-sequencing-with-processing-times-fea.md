# Feasible job-sequencing instances

Let $(J, K)$ be a job-sequencing instance with jobs
$J = (p_0, d_0, w_0), \dots, (p_{n-1}, d_{n-1}, w_{n-1})$. The instance is feasible when there
are distinct indices $j_1, \dots, j_m < n$, for some $m \ge 0$, such that
$w_{j_1} + \dots + w_{j_m} \ge K$ and, for every $t$ with $1 \le t \le m$,
$p_{j_1} + \dots + p_{j_t} \le d_{j_t}$: the selected jobs, run one after another in this order
from time $0$, each finish by their deadlines, and their total profit is at least $K$.
