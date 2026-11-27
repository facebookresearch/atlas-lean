# Feasible instances of QUOTIENT CUT

An instance $(n,w,E,K)$ is feasible when some $C\subseteq V=\{0,\ldots,n-1\}$ has $m=\min\{w(C),w(V\setminus C)\}>0$ and cut cost at most $K m$. Each side's weight is the sum of its vertex weights; an absent entry in $w$ contributes zero. The cut cost is the sum of the costs of the listed edges with exactly one endpoint in $C$. Since $m>0$, the ratio of this cost to $m$ is at most $K$.
