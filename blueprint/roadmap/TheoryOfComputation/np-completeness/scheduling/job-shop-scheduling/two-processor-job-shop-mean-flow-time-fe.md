# Feasible instances of TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME

An instance $(m, J, K)$ is feasible for TWO-PROCESSOR JOB-SHOP MEAN FLOW TIME when there are start times $\sigma(t) \in \mathbb{N}$ for the tasks such that two tasks on the same processor never start at the same time, a task starting after another task $t'$ on the same processor starts no earlier than $\sigma(t') + l(t')$, each task of a job starts no earlier than the previous task of that job finishes, and the completion times $C_j$ (the finishing time of the last task of job $j$) satisfy $\sum_j C_j \le K$.
