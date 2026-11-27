# Disintegration of a boundary-wired measure over conditioning fibres

Let $G = (V, E)$ be a finite simple graph, $C$ a simple graph on $V$, $0 < p < 1$, $q > 0$, $F$ a finite set of unordered pairs of vertices, and $\omega$ an assignment of open/closed states to the unordered pairs of vertices. Then

$$\phi^C_{G,p,q}(\omega) = \Big(\sum_{\rho \in \mathcal{F}_F(\omega)} \phi^C_{G,p,q}(\rho)\Big) \cdot \phi^C_{G,p,q}(\omega \mid F, \omega),$$

where $\mathcal{F}_F(\omega)$ is the set of configurations that agree with $\omega$ on every pair outside $F$, $\phi^C_{G,p,q}$ is the [random-cluster probability with boundary wiring $C$](bc-prob.md), and $\phi^C_{G,p,q}(\cdot \mid F, \psi)$ is the [conditional measure](cond-bc-prob.md) $\phi^{C}_{G,p,q}(\,\cdot \mid F, \psi)$, which gives $\omega$ the mass $w^C(\omega)/Z^C_{F,\psi}$ if $\omega$ agrees with $\psi$ on every unordered pair outside $F$ and $0$ otherwise, where $w^C(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k_C(\omega)}$ and $Z^C_{F,\psi}$ is the [sum of $w^C$ over the configurations agreeing with $\psi$ off $F$](induced-bc-z.md).
