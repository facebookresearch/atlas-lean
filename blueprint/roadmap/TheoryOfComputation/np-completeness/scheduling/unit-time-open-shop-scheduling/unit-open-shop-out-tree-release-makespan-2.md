# Feasible instances of OPEN SHOP O|p_ij=1;outtree;r_i|Cmax

An instance $(m, J, A, K)$ of OPEN SHOP O|p_ij=1;outtree;r_i|Cmax, with $n$ listed jobs, job $j$ carrying the release date $r_j$, is feasible when some natural-number start times $\sigma_k(j)$ form a [unit-time open-shop schedule](is-unit-open-shop-schedule.md) of the $m \cdot n$ unit operations for the arcs $A$ such that, for every machine $k < m$ and every job $j < n$,

$$
r_j \le \sigma_k(j) \quad \text{and} \quad \sigma_k(j) + 1 \le K.
$$

The schedule always has exactly one unit operation per machine and job; the processing times stored with the jobs are not read, and that every job has $m$ processing times, all equal to $1$, is part of [well-formedness](well-formed.md). With at least one job and $m \ge 1$, the second condition says that the makespan $\max_j C_j$ is at most $K$; with no jobs (or no machines) it holds for every $K$. Feasibility does not include well-formedness; the decision problem requires both, and well-formedness rejects an empty job list.
