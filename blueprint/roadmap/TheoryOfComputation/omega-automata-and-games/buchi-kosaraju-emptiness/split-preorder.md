# Split Preorder

Assume that `V` carries a Boolean equality test `==` that agrees with equality.

The second-pass DFS trees of a traversal: split its preorder at its forest
roots. In a DFS preorder the vertices of one tree are contiguous and each tree
starts with its root, so one pass with one `Std.HashSet.contains` test per
vertex suffices (in the hash-table cost model; this split is *not* counted in
the abstract DFS transition counts `n₁` / `n₂` below). Computable: the split
tests are `Bool`-valued (`contains`, `List.isEmpty`).
