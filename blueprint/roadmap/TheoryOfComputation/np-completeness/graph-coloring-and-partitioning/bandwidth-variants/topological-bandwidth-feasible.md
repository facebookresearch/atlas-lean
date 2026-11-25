# Feasible instances of TOPOLOGICAL BANDWIDTH

An instance $(n, E, K)$ is feasible for TOPOLOGICAL BANDWIDTH when for some list $s$ with one entry per edge, the subdivided instance $(n + \sum s, E', K)$ is feasible for BANDWIDTH: some ordering of $0, \dots, N-1$, with $N = n + \sum s$, has $|p(u) - p(v)| \le K$ for every pair $(u, v)$ in $E'$, where $p(m)$ is the position of $m$ in the ordering, counting from $0$, and $p(m) = N$ when $m$ is not among $0, \dots, N-1$.
