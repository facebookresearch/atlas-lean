# Proved cost shape: three DFS passes

Assume that `V` carries a Boolean equality test `==` that agrees with equality and a hash function; that equality on `V` is decidable; and that `start` is a decidable predicate.

The SCC decomposition's two
passes (`kosaraju_dfs_counts`) plus the start-reachability pass each have
exactly the `Internal.Step` transition counts given by the proved DFS cost
lemmas. The third pass counts its start-vertex roots, its preorder length,
and one transition per adjacency entry scanned from a reached vertex.
