# Feasible instances of TWO-MACHINE UNIT-TIME MULTI-PURPOSE JOB SHOP, WEIGHTED TARDINESS

With $D$ listing pairs $(d_j, w_j)$, an instance is feasible when there is a multi-purpose machine job-shop schedule (each operation on an eligible machine, operations of a job in order, no overlap on a machine) with $\sum_j w_j (C_j - d_j) \le K$, $C_j$ the completion of the last operation of each job $j$ with operations, using truncated subtraction (pairs missing from the list read as $(0, 0)$). A job with no operations has no last operation, so its $C_j$ is unconstrained and can be taken to be $0$.
