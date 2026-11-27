# Total wired Edwards–Sokal weight

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, $q \in \mathbb{N}$, $b \in \{0, \dots, q - 1\}$ and $p \in \mathbb{R}$. The total wired Edwards–Sokal weight is

$$Z^{ES,b}_q(p) = \sum_\omega \sum_\sigma W^b_p(\sigma, \omega),$$

the sums running over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included) and all colorings $\sigma : V \to \{0, \dots, q - 1\}$, where $W^b_p$ is the [wired Edwards–Sokal weight](es-weight-wired.md) $W^b_p(\sigma, \omega)$, equal to the Edwards–Sokal weight $W_p(\sigma, \omega) = \prod_{e \in E} f_e$ (with $f_{\{x,y\}} = p\,\mathbf{1}[\sigma_x = \sigma_y]$ if $\{x, y\}$ is open and $1 - p$ if it is closed) when $\sigma = b$ on $\partial$, and to $0$ otherwise.
