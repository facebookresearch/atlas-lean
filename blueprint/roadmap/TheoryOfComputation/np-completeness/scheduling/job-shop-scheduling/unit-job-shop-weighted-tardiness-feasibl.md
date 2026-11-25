# Feasible instances of TWO-PROCESSOR UNIT-TIME JOB SHOP, WEIGHTED TARDINESS

An instance is feasible when there are job-shop start times one-to-one on the tasks of each processor, a later task on a processor starting no earlier than an earlier one ends, and the tasks of each job in order, with $\sum_j w_j (C_j - d_j) \le K$ using truncated subtraction, $C_j$ the end of job $j$'s last task when $j$ has tasks (pairs missing from the list read as $(0, 0)$). A job with no tasks has no last task, so its $C_j$ is unconstrained and can be taken to be $0$.
