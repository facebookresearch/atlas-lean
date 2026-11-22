# Random-cluster measure conditioned on the edges off a set

Let $G = (V, E)$ be a simple graph on a finite set $V$, $p, q \in \mathbb{R}$, $F$ a finite set of unordered pairs of elements of $V$, and $\psi, \omega$ configurations. The conditional random-cluster probability is

$$\phi(\omega \mid F, \psi) = \frac{\phi_{G,p,q}(\omega)}{\sum_{\rho \in \mathcal{F}_\psi} \phi_{G,p,q}(\rho)},$$

where $\phi_{G,p,q}$ is the [random-cluster probability](fk-prob.md), $\mathcal{F}_\psi$ is the [fibre](cond-fibre.md) of configurations agreeing with $\psi$ off $F$, and a zero denominator gives $0$. The formula is used for $\omega \in \mathcal{F}_\psi$. When $0 \le p \le 1$, $q > 0$ and the denominator is positive (always the case when $0 < p < 1$ and $q > 0$), its values on $\mathcal{F}_\psi$ form the conditional distribution of $\phi_{G,p,q}$ given agreement with $\psi$ off $F$.
