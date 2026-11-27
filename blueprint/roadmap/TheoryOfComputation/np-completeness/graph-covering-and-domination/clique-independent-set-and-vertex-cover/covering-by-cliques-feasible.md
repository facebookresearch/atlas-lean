# Feasible COVERING BY CLIQUES instances

An instance $(n, E, K)$ of COVERING BY CLIQUES is feasible when the edges of its graph can be covered by at most $K$ cliques: for some $k \le K$ there are cliques $S_1, \dots, S_k$ of the graph such that every edge has both endpoints in some $S_j$.

Equivalently, as in [GT59] INTERSECTION GRAPH BASIS, the graph is the intersection graph of subsets $S(v)$ of a set of at most $K$ elements: distinct vertices are adjacent exactly when their subsets intersect. From label sets $S(v) \subseteq \{0, \dots, k-1\}$ take the cliques $S_j = \{v : j \in S(v)\}$; conversely give each vertex the labels of the cliques containing it. On the same encoded triple both descriptions define the same set of instances.
