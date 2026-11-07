# Pair condition of the clique verifier

For a mode $m$, the adjacency bit $b$ of a vertex
pair $\{i, j\}$, and flags $s_i$, $s_j$ saying whether $i$ and $j$ are chosen, the pair
condition $\mathrm{ok}_m(b, s_i, s_j)$ is $\lnot(s_i \land s_j) \lor b$ for clique,
$\lnot(s_i \land s_j) \lor \lnot b$ for independent set, and $\lnot b \lor s_i \lor s_j$ for
vertex cover.
