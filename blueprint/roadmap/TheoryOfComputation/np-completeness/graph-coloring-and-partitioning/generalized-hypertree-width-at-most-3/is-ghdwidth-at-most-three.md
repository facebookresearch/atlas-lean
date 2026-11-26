# Generalized hypertree decompositions of width at most 3

Let $H$ be a hypergraph with vertices $0, \dots, n-1$ and hyperedges $e_1, \dots, e_m$, each a set of vertices. A triple $\langle T, B, \Lambda \rangle$, with $T$ a graph on finitely many nodes, a bag $B_u$ of vertices for every node $u$ and a set $\Lambda_u$ of hyperedges for every node $u$, is a generalized hypertree decomposition of $H$ of width at most $3$ when:

1. $T$ is a tree;
2. every hyperedge is contained in some bag: for each $e$ there is a node $u$ with $e \subseteq B_u$;
3. for every vertex $v$, the nodes whose bags contain $v$ induce a connected subgraph of $T$ (the empty set counts as connected);
4. every bag is covered by its hyperedges: $B_u \subseteq \bigcup_{e \in \Lambda_u} e$ for every node $u$;
5. $|\Lambda_u| \le 3$ for every node $u$.
