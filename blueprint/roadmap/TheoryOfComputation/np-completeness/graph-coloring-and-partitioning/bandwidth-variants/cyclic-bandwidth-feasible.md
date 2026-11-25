# Feasible instances of CYCLIC BANDWIDTH

An instance $(n, E, K)$ is feasible for CYCLIC BANDWIDTH when there is an ordering of the numbers $0, \dots, n-1$ such that the cyclic distance on $n$ positions between $p(u)$ and $p(v)$ is at most $K$ for every pair $(u, v)$ in $E$, where $p(m)$ is the position of $m$ in the ordering, counting from $0$, and $p(m) = n$ when $m$ is not among $0, \dots, n-1$. Thus a pair whose endpoints both lie outside $0, \dots, n-1$ has cyclic distance $0$ and never blocks feasibility: with $n = 1$ and $K = 0$, the list $E = [(1, 1)]$ is feasible.
