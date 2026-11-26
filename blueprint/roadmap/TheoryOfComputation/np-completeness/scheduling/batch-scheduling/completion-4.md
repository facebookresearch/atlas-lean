# Completion time of a job in SERIAL BATCHING, WEIGHTED COMPLETION TIME

Let $(s, L, K)$ be an instance of SERIAL BATCHING, WEIGHTED COMPLETION TIME, $b$ an assignment of the jobs to batch indices in $\mathbb{N}$, and $S : \mathbb{N} \to \mathbb{N}$ the setup start times of the batches. The completion time $C_j$ of job $j$ is the completion time of its batch, $C_j = S(b(j)) + s + \sum_{i : b(i) = b(j)} p_i$, so all jobs of a batch complete together.
