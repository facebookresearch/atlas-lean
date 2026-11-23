# GRAPH HOMOMORPHISM as a decision problem

The decision problem GRAPH HOMOMORPHISM accepts
a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
graph-homomorphism instance $(n, E, m, F)$ that is well formed (neither $E$ nor $F$ has repeated
entries, every pair $(u, v)$ in $E$ has $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$, and
every pair $(u, v)$ in $F$ has $u < m$, $v < m$, $u \ne v$ and $(v, u) \notin F$) and for which
there is a map $f : \{0, \dots, n - 1\} \to \{0, \dots, m - 1\}$ such that, for every pair
$(u, v)$ in $E$, $f(u) \ne f(v)$ and $(f(u), f(v))$ or $(f(v), f(u))$ belongs to $F$. Bitstrings
that do not decode are rejected.
