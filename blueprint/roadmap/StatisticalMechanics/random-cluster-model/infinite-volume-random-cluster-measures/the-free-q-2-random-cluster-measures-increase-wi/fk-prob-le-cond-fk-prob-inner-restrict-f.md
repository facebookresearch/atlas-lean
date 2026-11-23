# Conditional free measure dominates the smaller free box for $q \ge 1$

Let $d, n \in \mathbb{N}$, $\Lambda_m = \{-m, \dots, m\}^d$ (so $\Lambda_n \subseteq \Lambda_{n+1}$), and let $\psi$ be a configuration of $\Lambda_{n+1}$ (an assignment of open/closed states to the unordered pairs of vertices of $\Lambda_{n+1}$), and let $0 < p < 1$ and $q \ge 1$. Let $F$ be the set of unordered pairs of vertices of $\Lambda_{n+1}$ with both elements in $\Lambda_n$. For every increasing set $A$ of configurations of $\Lambda_n$,

$$\sum_{\omega \in A} \phi_{\Lambda_n,p,q}(\omega) \le \sum_{\rho \in \mathcal{F}_\psi,\ \rho|_n \in A} \phi(\rho \mid F, \psi),$$

where $\phi_{G,p,q}$ is the [random-cluster probability](../../random-cluster-measures-on-finite-graphs/fk-prob.md) on $G$, $\mathcal{F}_\psi$ is the set of configurations of $\Lambda_{n+1}$ agreeing with $\psi$ off $F$, $\rho|_n$ is the restriction of $\rho$ to the pairs of vertices of $\Lambda_n$, and $\phi(\cdot \mid F, \psi)$ is the [conditional random-cluster probability](../../random-cluster-measures-on-finite-graphs/cond-fk-prob.md) on $\Lambda_{n+1}$ given agreement with $\psi$ off $F$ (the random-cluster probability of $\Lambda_{n+1}$ divided by its total over the configurations agreeing with $\psi$ off $F$).
