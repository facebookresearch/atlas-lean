# Step bound for one clause (initial-row generator)

For natural numbers $m$ and $V$,

$$\mathrm{clauseB}(m, V) = V(3V + 6) + m \cdot \mathrm{litE}(V) + 3V + 4,$$

where $\mathrm{litE}(V) = 6V + 9$ is the per-literal cost apart from the gap loop.

It bounds the steps the generator takes to emit one clause with at most $m$ literals over $V$
variables.
