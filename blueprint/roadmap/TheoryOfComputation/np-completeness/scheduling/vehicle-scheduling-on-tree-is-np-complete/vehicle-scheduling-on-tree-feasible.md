# Feasibility for VEHICLE SCHEDULING ON TREE

Let $(P, R, K)$ be an instance of VEHICLE SCHEDULING ON TREE with vertices $V = \{0, \dots, m\}$. For vertices $u, v$, say that $d$ bounds the trip from $u$ to $v$ when some path (a walk without repeated vertices) from $u$ to $v$ in the [graph of the parent list](graph.md) has travel time at most $d$; no well-formedness is assumed here, and under the parent condition this graph is the rooted tree of the instance. The instance is feasible when there are a bijection $\pi : V \to V$ (the order of processing, $\pi(k)$ being the $k$-th vertex) and start times $S : V \to \mathbb{N}$ such that

- $r(v) \le S(v)$ for every vertex $v$;
- $S(\pi(0))$ bounds the trip from the root $0$ to $\pi(0)$;
- for every $k < m$, there is a path from $\pi(k)$ to $\pi(k+1)$ with travel time $t$ satisfying $S(\pi(k)) + h(\pi(k)) + t \le S(\pi(k+1))$;
- there is a path from $\pi(m)$ to $0$ with travel time $t$ satisfying $S(\pi(m)) + h(\pi(m)) + t \le K$.
