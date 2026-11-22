# Translation covariance of wired box masses

Let $d, m \in \mathbb{N}$, $v \in \mathbb{Z}^d$, $t$ a finite set of unordered pairs of vertices of the box $\Lambda_m = \{-m, \dots, m\}^d$, and $p \in \mathbb{R}$. Then

$$\phi^w_{\Lambda_m,\partial\Lambda_m,p,2}[t] = \phi^w_{\Lambda_m + v,\partial\Lambda_m + v,p,2}[t + v],$$

where $\phi^w_{G,\partial,p,2}$ is the [wired random-cluster probability](../finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md) at $q = 2$, $\mu[t]$ denotes the [mass of the all-open event](med-multi-mass-prob.md) $\sum_\omega \mathbf{1}[\text{all pairs of } t \text{ open in } \omega]\, \mu(\omega)$, $\partial\Lambda_m = \Lambda_m \setminus \Lambda_{m-1}$, and $\Lambda_m + v$ is the translated box with its nearest-neighbour graph (and, for the wired measure, boundary $\partial\Lambda_m + v$), and $t + v$ is the image of a set $t$ of pairs of $\Lambda_m$ under $x \mapsto x + v$.
