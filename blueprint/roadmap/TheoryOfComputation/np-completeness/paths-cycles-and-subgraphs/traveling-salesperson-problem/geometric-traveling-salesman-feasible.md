# Feasible instances of GEOMETRIC TRAVELING SALESMAN

An instance is feasible when some tour of the points has length at most $B$, where the length of a tour is the sum, over its edges including the return edge to the first point, of the [discretized Euclidean distance](discrete-dist.md) $\lceil \sqrt{(x_1 - x_2)^2 + (y_1 - y_2)^2} \rceil$ of each edge; each edge is rounded up separately, not the total. For the points $(0,0), (1,1), (2,0)$ the exact tour length is $2 + 2\sqrt2 < 5$, but the tour has length $2 + 2 + 2 = 6$.
