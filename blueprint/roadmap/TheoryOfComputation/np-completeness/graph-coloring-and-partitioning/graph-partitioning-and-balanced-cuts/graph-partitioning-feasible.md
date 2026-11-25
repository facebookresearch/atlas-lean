# Feasible instances of GRAPH PARTITIONING

An instance $(n,w,E,K,J)$ is feasible if some labelling $c:\mathbb N\to\mathbb N$ gives every block total vertex weight at most $K$, and the listed edge lengths between different blocks sum to at most $J$. A block sum runs over vertices $v<n$ with the given label. If $v$ has no entry in the weight list $w$, its weight is zero. Each edge record $(u,v,l)$ contributes its length $l$ exactly when $c(u)\ne c(v)$.
