# Wired Edwards–Sokal one-point function

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, $b \in \{0, 1\}$, $p \in \mathbb{R}$ and $x \in V$. The wired Edwards–Sokal one-point function is

$$\langle s(\sigma_x) \rangle^{ES,b}_p = \frac{1}{Z^{ES,b}_2(p)} \sum_\omega \sum_\sigma W^b_p(\sigma, \omega)\, s(\sigma_x),$$

where $s(0) = 1$ and $s(1) = -1$ is the [Ising spin](../ising-two-point-function-via-the-edwards-sokal-c/ising-spin.md) of a color, $W^b_p$ is the [wired Edwards–Sokal weight](../the-edwards-sokal-coupling-with-wired-boundary-c/es-weight-wired.md) $W^b_p(\sigma, \omega)$, equal to the Edwards–Sokal weight $W_p(\sigma, \omega) = \prod_{e \in E} f_e$ (with $f_{\{x,y\}} = p\,\mathbf{1}[\sigma_x = \sigma_y]$ if $\{x, y\}$ is open and $1 - p$ if it is closed) when $\sigma = b$ on $\partial$, and to $0$ otherwise, and $Z^{ES,b}_2(p) = \sum_\omega \sum_\sigma W^b_p(\sigma, \omega)$ is the [total wired Edwards–Sokal weight](../the-edwards-sokal-coupling-with-wired-boundary-c/es-zwired.md), the sums running over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included) and all colorings $\sigma : V \to \{0, 1\}$ (the quotient is read as $0$ if $Z^{ES,b}_2(p) = 0$).
