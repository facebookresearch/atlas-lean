# Equal free probabilities from eventually equal translated masses

Let $d, N \in \mathbb{N}$, $v \in \mathbb{Z}^d$, $0 < p < 1$, and let $t, t'$ be finite sets of unordered pairs of vertices of $\Lambda_N = \{-N, \dots, N\}^d$. Suppose that for all sufficiently large $m \ge N$,

$$\phi_{\Lambda_m + v,p,2}[t^{(m)} + v] = \phi_{\Lambda_m,p,2}[t'^{(m)}],$$

where $t^{(m)}$ is the image of $t$ in $\Lambda_m$ under the inclusion $\Lambda_N \subseteq \Lambda_m$, $\phi_{G,p,2}$ is the [random-cluster probability](../../random-cluster-measures-on-finite-graphs/fk-prob.md) on $G$ at $q = 2$, $\mu[t]$ denotes the [mass of the all-open event](med-multi-mass-prob.md) $\sum_\omega \mathbf{1}[\text{all pairs of } t \text{ open in } \omega]\, \mu(\omega)$, and $\Lambda_m + v$ is the translated box with its nearest-neighbour graph (and, for the wired measure, boundary $\partial\Lambda_m + v$), and $t + v$ is the image of a set $t$ of pairs of $\Lambda_m$ under $x \mapsto x + v$. Then $\phi^0_{p,2}(O_t) = \phi^0_{p,2}(O_{t'})$, where $O_t$ is the event that all pairs of $t$ are open and $\phi^0_{p,2}$ is the [free infinite-volume random-cluster measure](../finite-and-infinite-volume-fk-measures-on-d/free-infinite-volume.md) on $\mathbb{Z}^d$ (a chosen subsequential weak limit of the free box measures).
