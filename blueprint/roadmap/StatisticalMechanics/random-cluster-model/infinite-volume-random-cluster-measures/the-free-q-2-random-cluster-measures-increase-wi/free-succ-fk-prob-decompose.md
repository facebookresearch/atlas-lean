# Decomposition of the free measure over the outer configuration

Let $d, n \in \mathbb{N}$, $0 < p < 1$, $q > 0$ and $\Lambda_m = \{-m, \dots, m\}^d$. Let $F$ be the set of unordered pairs of vertices of $\Lambda_{n+1}$ with both elements in $\Lambda_n$. For every set $B$ of configurations of $\Lambda_{n+1}$,

$$\sum_{\rho \in B} \phi_{\Lambda_{n+1},p,q}(\rho) = \sum_{\psi} \Big(\sum_{\sigma \in \mathcal{F}_\psi} \phi_{\Lambda_{n+1},p,q}(\sigma)\Big) \Big(\sum_{\rho \in \mathcal{F}_\psi \cap B} \phi(\rho \mid F, \psi)\Big),$$

where the outer sum runs over the configurations $\psi$ of $\Lambda_{n+1}$ that are closed on every pair of $F$, $\mathcal{F}_\psi$ is the set of configurations of $\Lambda_{n+1}$ agreeing with $\psi$ off $F$, $\phi_{G,p,q}$ is the [random-cluster probability](../../random-cluster-measures-on-finite-graphs/fk-prob.md) on $G$, and $\phi(\cdot \mid F, \psi)$ is the [conditional random-cluster probability](../../random-cluster-measures-on-finite-graphs/cond-fk-prob.md) on $\Lambda_{n+1}$ given agreement with $\psi$ off $F$ (the random-cluster probability of $\Lambda_{n+1}$ divided by its total over the configurations agreeing with $\psi$ off $F$).
