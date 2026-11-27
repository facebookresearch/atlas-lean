# Edge bond sum is half the sum over ordered adjacent pairs

Let $G = (V, E)$ be a finite simple graph and $s$ a spin configuration, with spins $\sigma_x = +1$ if $s(x)$ is true and $\sigma_x = -1$ otherwise. Then

$$2 \sum_{\{x, y\} \in E} \sigma_x \sigma_y = \sum_{x \in V} \sum_{y \in V} [x \sim y]\, \sigma_x \sigma_y,$$

where $[x \sim y]$ is $1$ if $x$ and $y$ are adjacent and $0$ otherwise.
