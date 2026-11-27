# Spin marginal of the Edwards–Sokal measure

Let $G = (V, E)$ be a finite simple graph, $q \in \mathbb{N}$ and $p \in \mathbb{R}$. The spin marginal of the Edwards–Sokal measure at a coloring $\sigma : V \to \{0, \dots, q - 1\}$ is

$$\frac{1}{Z^{ES}_q(p)} \sum_\omega W_p(\sigma, \omega),$$

the sum running over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included), where $W_p$ is the [Edwards–Sokal weight](es-weight.md) $W_p(\sigma, \omega) = \prod_{e \in E} f_e$, where for $e = \{x, y\}$ the factor $f_e$ is $p\,\mathbf{1}[\sigma_x = \sigma_y]$ if $e$ is open in $\omega$ and $1 - p$ if $e$ is closed, and $Z^{ES}_q(p)$ is the [Edwards–Sokal partition function](es-z.md) $Z^{ES}_q(p) = \sum_\omega \sum_\sigma W_p(\sigma, \omega)$, the sums running over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included) and all colorings $\sigma : V \to \{0, \dots, q - 1\}$ (the quotient is read as $0$ if $Z^{ES}_q(p) = 0$).
