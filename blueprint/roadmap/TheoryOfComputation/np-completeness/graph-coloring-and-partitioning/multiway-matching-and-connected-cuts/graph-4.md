# Directed graph of a max directed cut instance

For a MAX DIRECTED CUT instance with $n$ vertices $0, \dots, n-1$ and an arc list, the directed graph $G = (V, A)$ on these vertices has an arc $u \to v$, for in-range vertices $u, v < n$, exactly when the ordered pair $(u, v)$ is in the arc list. Pairs with an endpoint at least $n$ produce no arc, and a listed pair $(u, u)$ produces a loop; for $n = 1$ the pair $(0, 1)$ gives nothing and $(0, 0)$ gives a loop at $0$. Well-formedness of the instance rules out loops and out-of-range endpoints.
