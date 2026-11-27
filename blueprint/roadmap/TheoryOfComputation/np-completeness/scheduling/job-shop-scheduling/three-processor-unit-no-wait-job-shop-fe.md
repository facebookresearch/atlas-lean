# Feasible instances of THREE-PROCESSOR UNIT-LENGTH NO-WAIT JOB-SHOP SCHEDULING

An instance $(m, J, D)$ is feasible for no-wait job-shop scheduling with deadline $D$ when there are start times $\sigma(t) \in \mathbb{N}$ for the tasks such that two tasks on the same processor never start at the same time, a task starting after another task $t'$ on the same processor starts no earlier than $\sigma(t') + l(t')$, each task of a job after the first starts exactly when the previous task of that job finishes (no wait), and the last task of every job finishes by $D$.
