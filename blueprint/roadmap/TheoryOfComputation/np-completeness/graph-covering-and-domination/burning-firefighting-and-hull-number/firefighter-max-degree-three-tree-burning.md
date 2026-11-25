# Burning vertices under a defence sequence

For a graph $G$, a root $r$ and a defence list $d$, this defines when a vertex $v$ is on fire at time $t$. At time $0$ only $r$ burns; at time $t + 1$ the firefighter has defended $d[0], \dots, d[t]$, and the fire spreads from every vertex burning at time $t$ to each neighbour not defended.
