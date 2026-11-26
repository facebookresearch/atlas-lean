# Serial batch schedules for SERIAL BATCHING, TOTAL TARDINESS

Let $(s, L, K)$ be an instance of SERIAL BATCHING, TOTAL TARDINESS, $b$ an assignment of the jobs to batch indices in $\mathbb{N}$, and $S : \mathbb{N} \to \mathbb{N}$ the setup start times of the batches. The pair $(b, S)$ processes the batches one after another in index order when, for all jobs $j$ and $j^\prime$ with $b(j) < b(j^\prime)$, the completion time of batch $b(j)$, namely $S(b(j)) + s + \sum_{i : b(i) = b(j)} p_i$, is at most $S(b(j^\prime))$. Only batch indices that contain a job are constrained.
