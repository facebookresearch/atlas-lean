# Feasible instances of ACYCLIC PARTITION

Let $(n,w,A,B,K)$ consist of a vertex count, a list of vertex weights, an arc list with costs, and two bounds. It is feasible if there is a block labelling $p:\mathbb N\to\mathbb N$ satisfying three conditions. The quotient digraph has no directed cycle: no block label reaches itself by a nonempty sequence of quotient arcs. For each label $b$, the weights of vertices $v<n$ with $p(v)=b$ sum to at most $B$. Finally, the costs of the listed arcs $(u,v,c)$ with $p(u)\ne p(v)$ sum to at most $K$.

A missing vertex weight contributes zero to its block; weights at indices $v\ge n$ do not enter any block sum.
