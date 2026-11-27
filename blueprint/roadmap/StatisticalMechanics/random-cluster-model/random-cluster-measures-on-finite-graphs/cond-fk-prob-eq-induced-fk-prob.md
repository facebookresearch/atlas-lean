# Domain Markov property (finite volume)

Let $G = (V, E)$ be a simple graph on a finite set $V$, $0 < p < 1$, $q > 0$, $F$ a finite set of unordered pairs of elements of $V$, and $\psi, \omega$ configurations. Then

$$\phi(\omega \mid F, \psi) = \frac{w_{G,p,q}(\omega)}{\sum_{\rho \in \mathcal{F}_\psi} w_{G,p,q}(\rho)},$$

that is, the [conditional random-cluster probability](cond-fk-prob.md) equals the [induced probability](induced-fk-prob.md) on the fibre, where $w_{G,p,q}$ is the [random-cluster weight](fk-weight.md) and $\mathcal{F}_\psi$ is the [fibre](cond-fibre.md) of configurations agreeing with $\psi$ off $F$ (Grimmett, *The Random-Cluster Model*, 2006, Lemma 4.13).
