# Edwards–Sokal joint weight

Let $G = (V, E)$ be a finite simple graph, $q \in \mathbb{N}$ and $p \in \mathbb{R}$. The Edwards–Sokal weight of a coloring $\sigma : V \to \{0, \dots, q - 1\}$ and an assignment $\omega$ of open/closed states to the unordered pairs of vertices is

$$W_p(\sigma, \omega) = \prod_{e \in E} f_e(\sigma, \omega),$$

where $f_e$ is the [Edwards–Sokal edge factor](es-edge-factor.md): $p\,\mathbf{1}[\sigma_x = \sigma_y]$ if $e = \{x, y\}$ is open in $\omega$, and $1 - p$ if $e$ is closed.
