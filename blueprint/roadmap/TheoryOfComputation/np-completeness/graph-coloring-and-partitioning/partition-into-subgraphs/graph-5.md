# Directed graph of a partition into Hamiltonian subgraphs instance

In PARTITION INTO HAMILTONIAN SUBGRAPHS, for an instance with $n$ vertices $0, \dots, n-1$ and an arc list, the directed graph on these vertices has an arc $u \to v$, for in-range vertices $u, v < n$, exactly when the ordered pair $(u, v)$ is in the arc list. Pairs with an endpoint at least $n$ produce no arc, and a listed pair $(u, u)$ produces a loop; for $n = 1$ the pair $(0, 1)$ gives nothing and $(0, 0)$ gives a loop at $0$. Well-formedness of the instance rules out loops and out-of-range endpoints.
