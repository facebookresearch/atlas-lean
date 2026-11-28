# Generalized hypertree decompositions of width at most 3

Let $H$ be a hypergraph with vertices $0, \dots, n-1$ and a list of hyperedge entries indexed by $j$, and write $E_j$ for the [vertex set](edge-set.md) of entry $j$ (the listed vertices below $n$). A triple $\langle T, B, \Lambda \rangle$, with $T$ a graph on finitely many nodes, a bag $B_u$ of vertices for every node $u$ and a set $\Lambda_u$ of hyperedge **indices** for every node $u$, is a generalized hypertree decomposition of $H$ of width at most $3$ when:

1. $T$ is a tree;
2. every hyperedge is contained in some bag: for each index $j$ there is a node $u$ with $E_j \subseteq B_u$;
3. for every vertex $v$, the nodes whose bags contain $v$ induce a connected subgraph of $T$ (the empty set counts as connected);
4. every bag is covered by its selected hyperedges: $B_u \subseteq \bigcup_{j \in \Lambda_u} E_j$ for every node $u$;
5. $|\Lambda_u| \le 3$ for every node $u$, counting selected indices.

Indices, not vertex sets, are counted: with four entries equal to $[0]$, selecting all four has width four although they have the same vertex set.
