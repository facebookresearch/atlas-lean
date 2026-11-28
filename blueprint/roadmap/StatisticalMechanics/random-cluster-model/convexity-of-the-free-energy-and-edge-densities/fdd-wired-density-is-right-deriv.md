# Why the wired-density condition concerns only genuine edges

The [wired-density condition for a box](../per-box-agreement-of-free-and-wired-random-clust/fpe2-genuine-wired-is-right-deriv.md)
compares the right derivative of a single pressure function with the wired densities of
nearest-neighbor pairs at $q = 2$. It cannot make the same comparison for all unordered pairs.
For example, take $t = \log(1/3)$, so the [logistic function](fsc-logistic.md) gives $p = 1/4$.
In $\Lambda_1 \subseteq \mathbb{Z}$, the loop at $0$ has open probability $1/2$ because its
coordinate does not enter the random-cluster weight. The genuine edge $\{0,1\}$ has open
probability at most $p = 1/4$ by domination by Bernoulli percolation on the genuine edges.
These two densities cannot equal the same right derivative. The same obstruction applies to
any box with a genuine edge.

The [per-coordinate free energy](../per-box-agreement-of-free-and-wired-random-clust/fpe2-per-edge-g.md)
uses the common pressure function on genuine edges and the linear function $s \mapsto s/2$ on
non-edges, whose wired densities are $1/2$.
