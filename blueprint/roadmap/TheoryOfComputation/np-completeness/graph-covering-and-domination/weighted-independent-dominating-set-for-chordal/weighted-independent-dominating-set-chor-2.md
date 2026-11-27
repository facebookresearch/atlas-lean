# Instances with a light independent dominating set (chordal)

A weighted independent dominating set instance $(n, E, w, B)$ is feasible when its graph $G$ has an independent dominating set $D \subseteq \{0, \dots, n-1\}$ of total weight at most $B$: no two vertices of $D$ are adjacent in $G$, every vertex lies in $D$ or is adjacent to a vertex of $D$, and

$$\sum_{v \in D} w(v) \le B,$$

where $w(v)$ is the $v$-th entry of the weight list, taken to be $0$ when the list has fewer than $v + 1$ entries.
