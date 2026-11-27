# The decision problem BALANCED BICLIQUE

BALANCED BICLIQUE is the decision problem that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
balanced biclique instance $(n, es, K)$ that is well formed (the entries of $es$ are distinct,
and every pair $(u, v)$ in $es$ has $u < n$, $v < n$, $u \neq v$ and $(v, u) \notin es$) and for
which there are disjoint sets $A$ and $B$ of exactly $K$ vertices each in $\{0, \dots, n-1\}$
such that every vertex of $A$ is adjacent to every vertex of $B$, where distinct vertices $u$ and
$v$ are adjacent when $(u, v)$ or $(v, u)$ belongs to $es$. Bitstrings that do not decode are
rejected.
