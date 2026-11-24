# Box-edge marginal uniqueness off a countable set under the eventual tilt criterion

Let $d, N \in \mathbb{N}$ and let $e$ be an unordered pair of vertices of the box $\Lambda_N = \{-N, \dots, N\}^d \subseteq \mathbb{Z}^d$ (not necessarily an edge), viewed as a pair of sites of $\mathbb{Z}^d$, and assume the [abstract eventual tilt criterion](fksecant-data.md) for $e$. Then there is a countable set $S \subseteq \mathbb{R}$ such that for every $p \notin S$ with $0 < p < 1$ and every measure $\phi$ on the space of configurations of $\mathbb{Z}^d$ (assignments of open/closed states to all unordered pairs of sites), if

$$\phi^0_{p,2}(e \text{ open}) \le \phi(e \text{ open}) \le \phi^1_{p,2}(e \text{ open}),$$

then $\phi(e \text{ open}) = \phi^0_{p,2}(e \text{ open})$ and $\phi(e \text{ open}) = \phi^1_{p,2}(e \text{ open})$. Here $\phi^0_{p,2}$ and $\phi^1_{p,2}$ are the [free](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/free-infinite-volume.md) and [wired](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-infinite-volume.md) infinite-volume random-cluster measures on $\mathbb{Z}^d$ at $q = 2$ (chosen subsequential weak limits of the box measures), and $\phi(e \text{ open})$ is the real value of the $\phi$-measure of the set of configurations in which $e$ is open (an infinite value is read as $0$).

The hypothesis is [equivalent to the wired/free secant comparison](fk-secant-data-iff-secant.md). This is conditional uniqueness of a single marginal, not uniqueness derived from finite-volume FK measures.
