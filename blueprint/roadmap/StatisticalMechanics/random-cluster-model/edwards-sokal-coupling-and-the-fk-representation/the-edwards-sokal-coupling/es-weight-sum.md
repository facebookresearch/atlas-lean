# Edwards–Sokal weight summed over spins is the random-cluster weight

Let $G = (V, E)$ be a finite simple graph, $q \in \mathbb{N}$ and $p \in \mathbb{R}$. For every assignment $\omega$ of open/closed states to the unordered pairs of vertices,

$$\sum_\sigma W_p(\sigma, \omega) = p^{o(\omega)} (1 - p)^{c(\omega)} q^{k(\omega)},$$

where the sum runs over all colorings $\sigma : V \to \{0, \dots, q - 1\}$, $W_p$ is the [Edwards–Sokal weight](es-weight.md) $W_p(\sigma, \omega) = \prod_{e \in E} f_e$, where for $e = \{x, y\}$ the factor $f_e$ is $p\,\mathbf{1}[\sigma_x = \sigma_y]$ if $e$ is open in $\omega$ and $1 - p$ if $e$ is closed, $o(\omega)$ and $c(\omega)$ are the numbers of open and closed edges of $G$, and $k(\omega)$ is the number of open clusters (isolated vertices included). The right side is the [random-cluster weight](../../random-cluster-measures-on-finite-graphs/fk-weight.md).
