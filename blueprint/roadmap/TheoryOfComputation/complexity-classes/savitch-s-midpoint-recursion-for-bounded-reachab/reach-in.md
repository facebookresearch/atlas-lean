# Savitch midpoint predicate

Bounded reachability by midpoint recursion, for a decidable relation $R$ on a finite type $C$ with decidable equality (tested at level $0$). At
level $0$ the predicate accepts $(x, y)$ when $x = y$ or $R(x, y)$. At level $k + 1$ it accepts
$(x, y)$ when some midpoint $z$ is accepted at level $k$ both from $x$ and toward $y$, the midpoint
being found by exhaustive search over the finite type. It decides whether $y$ is reachable from
$x$ in at most $2^k$ steps; no space bound is claimed.
