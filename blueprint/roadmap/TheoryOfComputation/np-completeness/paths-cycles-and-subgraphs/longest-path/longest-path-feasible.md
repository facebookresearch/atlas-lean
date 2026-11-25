# Feasibility of a longest-path instance

A longest-path instance $(n, E, K, s, t)$ is
feasible when the graph of $E$ on $n$ vertices has a simple path from $s$ to $t$ with at least
$K$ edges, that is, a list $v_0, \dots, v_m$ of pairwise distinct vertices with $m \ge K$,
$v_0 = s$ and $v_m = t$, in which $v_j$ and $v_{j+1}$ are adjacent for every $j < m$.
