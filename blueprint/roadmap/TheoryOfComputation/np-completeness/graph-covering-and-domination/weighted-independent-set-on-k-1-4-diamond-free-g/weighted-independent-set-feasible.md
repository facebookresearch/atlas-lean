# Instances with a heavy independent set

A weighted independent set instance $(n, E, w, k)$ is feasible when its graph has an independent set $S \subseteq \{0, \dots, n-1\}$ (no two vertices of $S$ adjacent) of total weight at least $k$:

$$k \le \sum_{v \in S} w(v),$$

where $w(v)$ is the $v$-th entry of the weight list, and $0$ when the list has fewer than $v + 1$ entries.
