# Feasible instances of JOB-SHOP SCHEDULING

An instance $(m, J, D)$ is feasible when there are start times $\sigma(t) \in \mathbb{N}$ for the tasks such that two tasks on the same processor never start at the same time, a task starting after another task $t'$ on the same processor starts no earlier than $\sigma(t') + l(t')$, each task of a job starts no earlier than the previous task of that job finishes, and the last task of every job finishes by $D$.
