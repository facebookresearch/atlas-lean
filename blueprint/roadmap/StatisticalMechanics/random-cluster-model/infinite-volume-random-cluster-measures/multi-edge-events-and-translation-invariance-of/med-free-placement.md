# Free placement for a shift via eventually equal box masses

Let $d \in \mathbb{N}$, $0 < p < 1$ and $g \in \mathbb{Z}^d$. The free placement condition for $g$ holds when for every finite set $s$ of unordered pairs of sites of $\mathbb{Z}^d$ there are $N \in \mathbb{N}$ and finite sets $t, t'$ of pairs of vertices of $\Lambda_N = \{-N, \dots, N\}^d$ such that $s = t$ and $s - g = t'$ as sets of pairs of sites, and for all sufficiently large $m \ge N$

$$\phi_{\Lambda_m + g,p,2}[t^{(m)} + g] = \phi_{\Lambda_m,p,2}[t'^{(m)}],$$

where $t^{(m)}$ is the image of $t$ in $\Lambda_m$ under the inclusion $\Lambda_N \subseteq \Lambda_m$, $\phi_{G,p,2}$ is the [random-cluster probability](../../random-cluster-measures-on-finite-graphs/fk-prob.md) on $G$ at $q = 2$, $\mu[t]$ denotes the [mass of the all-open event](med-multi-mass-prob.md) $\sum_\omega \mathbf{1}[\text{all pairs of } t \text{ open in } \omega]\, \mu(\omega)$, and $\Lambda_m + g$ is the translated box with its nearest-neighbour graph (and, for the wired measure, boundary $\partial\Lambda_m + g$), and $t + g$ is the image of a set $t$ of pairs of $\Lambda_m$ under $x \mapsto x + g$.
