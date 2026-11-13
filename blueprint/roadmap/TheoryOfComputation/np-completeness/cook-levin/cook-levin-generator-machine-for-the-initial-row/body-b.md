# Step bound for one loop iteration (initial-row generator)

For natural numbers
$m, g, N, V$,

$$\mathrm{bodyB}(m,g,N,V) = 2V + 2 + (N(2g+3) + N + 2) + g + 1 + \mathrm{clauseB}(m,V) + V + 1,$$

where $\mathrm{clauseB}(m, V)$ is the step bound for one clause with at most $m$ literals.

It bounds one iteration of any phase loop, and one I3 iteration including its read.
