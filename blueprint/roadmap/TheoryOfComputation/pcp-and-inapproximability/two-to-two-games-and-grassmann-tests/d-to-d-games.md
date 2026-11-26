# d-to-d games and 2-to-2 constraints

A **label-cover game** $\mathcal{G} = (U, V, E, [L], [R], \{\Phi_e\}_{e \in E})$ consists of a bipartite graph $(U \cup V, E)$, label sets $[L]$ for $U$ and $[R]$ for $V$, and for each edge $e = (u, v)$ a relation $\Phi_e \subseteq [L] \times [R]$. Its **value** is the maximum, over labelings $\ell : U \to [L]$ and $r : V \to [R]$, of the fraction of edges with $(\ell(u), r(v)) \in \Phi_e$.

The game is **$d$-to-$d$** if $L = R$ and every $\Phi_e$ has all left and right degrees at most $d$. A **$2$-to-$2$ constraint** on $[2m] \times [2m]$ is a relation obtained from a perfect matching between a partition of the left labels into pairs and a partition of the right labels into pairs, connecting each left pair completely to its matched right pair (a disjoint union of $m$ copies of $K_{2,2}$). **Unique games** are the $1$-to-$1$ case in which every $\Phi_e$ is a permutation.

## Depends on

- [The Unique Games Conjecture](../pcp-constructions/the-unique-games-conjecture.md)

## Sources

- S. Khot, "On the power of unique 2-prover 1-round games", STOC (2002).
- S. Khot, D. Minzer, M. Safra, "On independent sets, 2-to-2 games, and Grassmann graphs", STOC (2017), ECCC TR16-124.
