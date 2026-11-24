# Feasible instances of TWO-PROCESSOR OPEN-SHOP MEAN FLOW TIME

An instance $(m, J, K)$ is feasible when there is an open-shop schedule meeting the bound: start times $\sigma_p(j)$ of job $j$'s task on processor $p$, pairwise different on each processor, such that a task starting after another task $k$ on the same processor starts no earlier than $k$ finishes, the tasks of each job occupy pairwise disjoint time intervals, and every task finishes by $K$ whose completion times $C_j = \max_p (\sigma_p(j) + l(t_p[j]))$ sum to at most $K$.
