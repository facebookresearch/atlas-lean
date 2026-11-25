# Closed annulus plus inner-boundary wiring gives wired $\Lambda_n$ law

Let $d, n \in \mathbb{N}$, $0 < p < 1$ and $q > 0$, let $\Lambda_m = \{-m, \dots, m\}^d$, and let $D$ be a graph on $\Lambda_{n+1}$ no edge of which has an endpoint in $\Lambda_n$. Let $K$ be the clique on the vertices of $\Lambda_{n+1}$ lying in $\partial\Lambda_n = \Lambda_n \setminus \Lambda_{n-1}$, and let $F$ be the set of unordered pairs of vertices of $\Lambda_{n+1}$ with both elements in $\Lambda_n$. For every set $B$ of configurations of $\Lambda_{n+1}$,

$$\sum_{\rho \in B} \phi^{K \cup D}_{\Lambda_{n+1},p,q}(\rho \mid F, \mathbf{0}) = \sum_{\omega :\ \tilde\omega \in B} \phi^w_{\Lambda_n,\partial\Lambda_n,p,q}(\omega),$$

where the left side uses the [conditional measure](../../fkg-inequality-and-monotonicity-of-random-cluste/cond-bc-prob.md) of the random-cluster measure on $\Lambda_{n+1}$ with boundary wiring $K \cup D$ given agreement with the all-closed configuration $\mathbf{0}$ off $F$, $\tilde\omega$ is the configuration of $\Lambda_{n+1}$ equal to $\omega$ on $F$ and closed elsewhere, and $\phi^w_{\Lambda_n,\partial\Lambda_n,p,q}$ is the [wired random-cluster probability](../finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md) of $\Lambda_n$.
