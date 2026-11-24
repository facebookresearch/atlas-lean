# Unit-time three-machine flow-shop schedules with chains

For jobs $0, \dots, n-1$ and chain arcs $A$, start times $S_i(k)$ for job $i$ on machine $k \in \{0, 1, 2\}$ (all operations of length $1$) form a schedule when each job runs on machines $0, 1, 2$ in order ($S_i(0) + 1 \le S_i(1)$ and $S_i(1) + 1 \le S_i(2)$), two different jobs never overlap on a machine, and for every arc $(i, j)$ job $j$ starts on machine $0$ only after $i$ completes on machine $2$ ($S_i(2) + 1 \le S_j(0)$).
