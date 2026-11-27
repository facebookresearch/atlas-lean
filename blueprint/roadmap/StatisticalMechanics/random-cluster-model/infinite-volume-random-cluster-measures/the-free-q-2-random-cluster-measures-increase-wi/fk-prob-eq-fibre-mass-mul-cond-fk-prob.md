# Fibre-mass factorization of random-cluster probabilities

Let $d, n \in \mathbb{N}$, $0 < p < 1$, $q > 0$, $\Lambda_m = \{-m, \dots, m\}^d$, and let $\omega$ be a configuration of $\Lambda_{n+1}$. Let $F$ be the set of unordered pairs of vertices of $\Lambda_{n+1}$ with both elements in $\Lambda_n$. Then

$$\phi_{\Lambda_{n+1},p,q}(\omega) = \Big(\sum_{\rho \in \mathcal{F}_\omega} \phi_{\Lambda_{n+1},p,q}(\rho)\Big)\, \phi(\omega \mid F, \omega),$$

where $\mathcal{F}_\omega$ is the set of configurations agreeing with $\omega$ off $F$, $\phi_{G,p,q}$ is the [random-cluster probability](../../random-cluster-measures-on-finite-graphs/fk-prob.md) on $G$, and $\phi(\cdot \mid F, \omega)$ is the [conditional random-cluster probability](../../random-cluster-measures-on-finite-graphs/cond-fk-prob.md) on $\Lambda_{n+1}$ given agreement with $\omega$ off $F$ (the random-cluster probability of $\Lambda_{n+1}$ divided by its total over the configurations agreeing with $\omega$ off $F$).
