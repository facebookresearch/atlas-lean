# Edwards–Sokal bond sum is a multiple of the Potts weight

Let $G = (V, E)$ be a finite simple graph, $q \in \mathbb{N}$, $\beta, J \in \mathbb{R}$ and $p = 1 - e^{-\beta J}$. For every coloring $\sigma : V \to \{0, \dots, q - 1\}$,

$$\sum_\omega W_p(\sigma, \omega) = c_G(\beta, J)\, e^{\beta J a(\sigma)},$$

where the sum runs over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included), $W_p$ is the [Edwards–Sokal weight](es-weight.md) $W_p(\sigma, \omega) = \prod_{e \in E} f_e$, where for $e = \{x, y\}$ the factor $f_e$ is $p\,\mathbf{1}[\sigma_x = \sigma_y]$ if $e$ is open in $\omega$ and $1 - p$ if $e$ is closed, $c_G(\beta, J) = 2^{N - |E|} e^{-\beta J |E|}$ is the [normalizing constant](es-first-const.md) ($N$ the number of unordered pairs of vertices, loops included), and $a(\sigma)$ is the number of edges of $G$ whose endpoints have the same color.
