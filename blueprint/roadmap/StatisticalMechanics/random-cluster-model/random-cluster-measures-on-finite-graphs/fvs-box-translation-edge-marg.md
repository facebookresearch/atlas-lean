# Translation covariance of FK edge marginals on boxes

Let $d, m \in \mathbb{N}$, $v \in \mathbb{Z}^d$, $e$ an unordered pair of vertices of $\Lambda_m = \{-m, \dots, m\}^d$, and $p, q \in \mathbb{R}$. Then the wired and the free edge marginals are translation covariant:

$$\phi^w_{\Lambda_m + v}(e + v \text{ open}) = \phi^w_{\Lambda_m}(e \text{ open}), \qquad \phi_{\Lambda_m + v}(e + v \text{ open}) = \phi_{\Lambda_m}(e \text{ open}),$$

where $\phi^w$ is the [wired random-cluster probability](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md) (with boundary $\partial\Lambda_m = \Lambda_m \setminus \Lambda_{m-1}$, resp. its translate) and $\phi$ the [random-cluster probability](fk-prob.md), both at $(p, q)$, and $\Lambda_m + v$ is the translated box with its nearest-neighbour graph and boundary $\partial\Lambda_m + v$, and $e + v$ is the image of $e$ under $x \mapsto x + v$.
