# Feasible MINIMUM BISECTION instances

An instance $(n, es, K)$ of MINIMUM BISECTION is
feasible when there is a set $S \subseteq \{0, \dots, n - 1\}$ with $\lfloor n / 2 \rfloor$
elements such that no sublist of $es$ (a list obtained from $es$ by deleting entries) with
$K + 1$ entries consists only of entries $(u, v)$ with exactly one of $u$ and $v$ in $S$; that
is, at most $K$ entries of $es$ have exactly one endpoint in $S$.
