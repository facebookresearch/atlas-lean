# Completion time of a batch in SERIAL BATCHING, WEIGHTED COMPLETION TIME

Let $(s, L, K)$ be an instance of SERIAL BATCHING, WEIGHTED COMPLETION TIME, let $b$ assign to each job $j$ a batch index $b(j) \in \mathbb{N}$, and let $S : \mathbb{N} \to \mathbb{N}$ give the time at which the setup of each batch starts. The completion time of batch $k \in \mathbb{N}$ is $S(k) + s + \sum_{j : b(j) = k} p_j$: the setup, followed by the jobs of the batch one after another. For an index $k$ that no job is assigned to, the sum is empty and the value is $S(k) + s$.
