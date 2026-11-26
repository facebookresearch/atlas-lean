# Feasible instances of NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax

An instance $(m, J, A, K)$ of NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax, with $n$ listed jobs, job $j$ carrying the integer due date $d_j$, is feasible when some natural-number start times $\sigma_k(j)$ form a [unit-time open-shop schedule](is-unit-open-shop-schedule.md) of the $m \cdot n$ unit operations for the arcs $A$ in which each job's operations fill $m$ consecutive unit slots (for each job $j$ some $s$ has $s \le \sigma_k(j) < s + m$ for every machine $k$), and every operation meets the lateness bound:

$$
\sigma_k(j) + 1 - d_j \le K \quad \text{for every machine } k < m \text{ and every job } j < n.
$$

The schedule always has exactly one unit operation per machine and job; the processing times stored with the jobs are not read, and that every job has $m$ processing times, all equal to $1$, is part of [well-formedness](../unit-time-flow-shop-scheduling/well-formed-2.md). With at least one job and $m \ge 1$, the bound says that the maximum lateness $\max_j (C_j - d_j)$ is at most $K$, where $C_j$ is the completion time of job $j$'s last operation; with no jobs (or no machines) it holds for every bound $K$, negative ones included. Feasibility does not include well-formedness; the decision problem requires both.
