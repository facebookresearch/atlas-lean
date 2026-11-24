# Parallel batches processed in index order

Batch start times $S$ process the batches in index order when, whenever $B(j) < B(j')$, batch $B(j')$ starts no earlier than batch $B(j)$ completes ($S(B(j))$ plus its length).
