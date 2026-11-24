# Feasible instances of VERTEX K-CUT

For $(n,E,P,w,K)$ let $V=\{0,\ldots,n-1\}$. The instance is feasible if some $C\subseteq V$ contains no endpoint of any listed pair in $P$, has total weight at most $K$, and separates the pairs. A vertex in $C$ contributes zero if its weight is missing from $w$.

For a pair $(s,t)$ with both endpoints in $V$, separation means that $t$ is not reachable from $s$ in the graph induced on $V\setminus C$. Distinct vertices $u,v$ are adjacent before deletion when $(u,v)$ or $(v,u)$ is in $E$. Hence a pair $(s,s)$ with $s\in V$ cannot be separated. A pair with an endpoint outside $V$ imposes no reachability test, but its in-range endpoint, if any, is still excluded from $C$.
