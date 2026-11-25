# Feasible job shops, weighted tardiness

An instance is feasible when some schedule, start times $\sigma$ with job completion times $C$ as in the schedule predicate, has $\sum_j w_j (C_j - d_j) \le K$ using truncated subtraction. There a job with no operations has a $C_j$ bounded only by the start times of the operations of the jobs it precedes, so $C_j = 0$ is allowed for it. A job with no listed triple $(r_j, d_j, w_j)$ has $r_j = d_j = w_j = 0$.
