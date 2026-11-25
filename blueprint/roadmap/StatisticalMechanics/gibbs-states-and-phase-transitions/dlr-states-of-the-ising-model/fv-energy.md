# Box energy with a boundary condition

Let $d, n \in \mathbb{N}$, let $\eta$ be a configuration of $\mathbb{Z}^d$ (the boundary condition), $B$ a
finite set of unordered pairs of sites and $h \in \mathbb{R}$. For spins $\tau$ on $\Lambda_n = \{x \in \mathbb{Z}^d : |x_i| \le n \text{ for all } i\}$, the box
energy is

$$-\sum_{\{x, y\} \in B} \sigma_x \sigma_y - h \sum_{x \in \Lambda_n} \sigma_x,$$

evaluated at the [glued configuration](glue.md) equal to $\tau$ in $\Lambda_n$ and to $\eta$ outside.
