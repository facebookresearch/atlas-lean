# Kosaraju Is Empty BC

Assume that `State` carries a Boolean equality test `==` that agrees with equality; that equality on `State` is decidable; that membership in `na.start` is decidable; that membership in `na.accept` is decidable; that each proposition `na.Tr s x t` is decidable; and that `Symbol` is finite.

Costed Büchi emptiness scanner: the same `Bool` as `kosarajuIsEmptyB`,
plus the cost. The reachable preorder is bound once (`reachPre`); the
hash set is built from that binding and its length is reused for the
cost — so the start-reachability DFS runs once, not twice (calling
`startReachable` again for the length would be a second DFS). The cost
counts one hash-table insertion per start-reachable vertex for the
visited-set construction plus the block scan's cost (`scanBlocksC`);
the visited set is built once and shared across the scan.
