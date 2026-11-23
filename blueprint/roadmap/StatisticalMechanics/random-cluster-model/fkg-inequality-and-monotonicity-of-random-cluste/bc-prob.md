# Random-cluster probability with a boundary wiring

Let $G = (V, E)$ be a finite simple graph, $C$ a simple graph on $V$ (the boundary wiring), and $p, q \in \mathbb{R}$. The random-cluster probability with boundary wiring $C$ of an assignment $\omega$ of open/closed states to the unordered pairs of vertices is

$$\phi^C_{G,p,q}(\omega) = \frac{w^C(\omega)}{Z^C_G(p, q)},$$

the [weight](bc-weight.md) $w^C(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k_C(\omega)}$ divided by the [partition function](bc-z.md) $Z^C_G(p, q) = \sum_{\omega'} w^C(\omega')$ (the quotient is read as $0$ if $Z^C_G(p, q) = 0$); here $o(\omega)$ and $c(\omega)$ count the open and closed edges of $G$ and $k_C(\omega)$ is the [number of clusters under the wiring $C$](num-clusters-bc.md), the number of connected components of the graph on $V$ whose edges are the edges of $G$ open in $\omega$ together with the edges of $C$. For $0 \le p \le 1$ and $q > 0$ the weights are nonnegative and $Z^C_G(p, q) > 0$, so $\phi^C_{G,p,q}$ is a probability distribution; for other parameters it is only a normalized signed weight, possibly identically $0$.
