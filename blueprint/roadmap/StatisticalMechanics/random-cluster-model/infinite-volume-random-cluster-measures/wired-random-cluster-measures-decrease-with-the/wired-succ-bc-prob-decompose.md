# Wired $\Lambda_{n+1}$ measure decomposed over outer configurations

Let $d, n \in \mathbb{N}$, $\Lambda_m = \{-m, \dots, m\}^d$, $0 < p < 1$ and $q > 0$. Let $F$ be the set of unordered pairs of vertices of $\Lambda_{n+1}$ with both elements in $\Lambda_n$. For every set $B$ of configurations of $\Lambda_{n+1}$,

$$\sum_{\rho \in B} \phi^K_{\Lambda_{n+1},p,q}(\rho) = \sum_{\psi} \Big(\sum_{\sigma \in \mathcal{F}_\psi} \phi^K_{\Lambda_{n+1},p,q}(\sigma)\Big) \Big(\sum_{\rho \in B} \phi^K(\rho \mid F, \psi)\Big),$$

where the outer sum runs over the configurations $\psi$ closed on every pair of $F$, $\mathcal{F}_\psi$ is the set of configurations agreeing with $\psi$ off $F$, $K$ is the clique on $\partial\Lambda_{n+1} = \Lambda_{n+1} \setminus \Lambda_n$, $\phi^K_{\Lambda_{n+1},p,q}$ is the [random-cluster probability](../../fkg-inequality-and-monotonicity-of-random-cluste/bc-prob.md) on $\Lambda_{n+1}$ with boundary wiring $K$ (the wired measure), and $\phi^K(\cdot \mid F, \psi)$ is its [conditional measure](../../fkg-inequality-and-monotonicity-of-random-cluste/cond-bc-prob.md) given agreement with $\psi$ off $F$.
