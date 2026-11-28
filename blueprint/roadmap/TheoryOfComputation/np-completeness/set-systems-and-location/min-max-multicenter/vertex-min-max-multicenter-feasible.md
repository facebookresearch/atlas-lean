# Feasibility for vertex MIN-MAX MULTICENTER

Let $(n, E, w, K, (p, q))$ be an instance of MIN-MAX MULTICENTER: vertices $0, \dots, n-1$, an edge list $E$ of triples $(u, v, \ell)$ giving the edge $\{u, v\}$ of length $\ell$, a list $w$ of vertex weights, a natural number $K$ and the bound $B = p / q$. The length of an edge of the graph is the $\ell$ of the first entry of $E$ whose endpoints are its endpoints, and the length $\mathrm{len}(W)$ of a walk $W$ is the sum of the lengths of its edges, counted with multiplicity. The weight $w(v)$ is entry $v$ of $w$, or $0$ if the list is too short.

The instance is feasible for the variant with centers at vertices when there is a set $P$ of at most $K$ vertices such that every vertex $v$ has a center $c \in P$ and a walk $W$ from $v$ to $c$ in the graph of the instance with

$$w(v) \cdot \mathrm{len}(W) \le \frac{p}{q},$$

compared as real numbers, with the convention $p / 0 = 0$.
