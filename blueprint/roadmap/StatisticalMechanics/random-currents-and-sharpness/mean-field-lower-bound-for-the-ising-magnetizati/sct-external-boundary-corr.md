# External boundary correlation of a cut, over edges leaving the box

For $d, n \in \mathbb{N}$, $\beta \in \mathbb{R}$ and a set $T$ of sites of the box $\Lambda_n = \{-n, \dots, n\}^d$, this is

$$\mathrm{ext}(T) = \sum_{(x, y) \in \partial T,\ y \notin \Lambda_n} \langle \sigma_0 \sigma_x \rangle_T,$$

the sum over the oriented boundary edges $(x, y)$ of $T$ ($x \in T$, $y \notin T$ nearest neighbours) that leave the
box, with $\langle \sigma_0 \sigma_x \rangle_T$ the [zero-field two-point function in $T$](../sharpness-of-the-phase-transition-for-the-ising/the-duminil-copin-tassion-point-for-the-ising-mo/corr-origin-inner.md) (the free-boundary correlation at inverse temperature $\beta$ on the subgraph induced by $T$, extended by $0$ when $x \notin T$ or $0 \notin T$).
