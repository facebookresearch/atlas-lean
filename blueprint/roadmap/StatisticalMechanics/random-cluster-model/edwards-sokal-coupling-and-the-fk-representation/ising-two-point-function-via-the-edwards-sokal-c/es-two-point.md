# Ising two-point function from the Edwards–Sokal coupling

Let $G = (V, E)$ be a finite simple graph, $p \in \mathbb{R}$ and $x, y \in V$. The Edwards–Sokal two-point function is

$$\langle s(\sigma_x)\, s(\sigma_y) \rangle^{ES}_p = \frac{1}{Z^{ES}_2(p)} \sum_\omega \sum_{\sigma} W_p(\sigma, \omega)\, s(\sigma_x)\, s(\sigma_y),$$

where $s(0) = 1$ and $s(1) = -1$ is the [Ising spin](ising-spin.md) of a color, $W_p$ is the [Edwards–Sokal weight](../the-edwards-sokal-coupling/es-weight.md) $W_p(\sigma, \omega) = \prod_{e \in E} f_e$, where for $e = \{x, y\}$ the factor $f_e$ is $p\,\mathbf{1}[\sigma_x = \sigma_y]$ if $e$ is open in $\omega$ and $1 - p$ if $e$ is closed, and $Z^{ES}_2(p)$ is the [Edwards–Sokal partition function](../the-edwards-sokal-coupling/es-z.md) $Z^{ES}_2(p) = \sum_\omega \sum_\sigma W_p(\sigma, \omega)$, the sums running over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included) and all colorings $\sigma : V \to \{0, 1\}$ (the quotient is read as $0$ if $Z^{ES}_2(p) = 0$).
