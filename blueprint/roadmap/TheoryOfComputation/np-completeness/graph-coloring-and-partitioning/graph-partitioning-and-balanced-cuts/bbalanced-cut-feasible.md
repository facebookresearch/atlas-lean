# Feasible instances of b-BALANCED CUT

An instance $(n, w, E, (p, q), K)$ is feasible for b-BALANCED CUT when some set $C \subseteq \{0, \dots, n-1\}$ satisfies $p \cdot w(V) \le q \cdot \min(w(C), w(V \setminus C))$ with $V = \{0, \dots, n-1\}$, that is $\min(w(C), w(V \setminus C)) \ge b \cdot w(V)$ for $b = p/q$, and the total cost of the edges with exactly one end in $C$ is at most $K$.
