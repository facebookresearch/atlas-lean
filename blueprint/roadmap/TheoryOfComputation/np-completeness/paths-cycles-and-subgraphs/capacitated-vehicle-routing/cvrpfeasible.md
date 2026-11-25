# Feasibility of a capacitated vehicle routing instance

Let $(n, d, D, m, C, K)$ be a
capacitated vehicle routing instance, with customers $0, \dots, n - 1$ and depot $n$, and let the
demand $d_c$ of $c$ be the entry of the list $d$ at position $c$ (counting from $0$), or $0$ if
$d$ has no such entry. The instance is feasible when there is a list of at most $m$ routes, each
a list of natural numbers, such that every route has no repeated entries and only entries less
than $n$; every customer $c < n$ lies on some route, and all routes of the list that contain $c$
are equal; the demands of the entries of each route sum to at most $C$; and the lengths of the
routes, for the distance matrix $D$ and depot $n$, sum to at most $K$.
