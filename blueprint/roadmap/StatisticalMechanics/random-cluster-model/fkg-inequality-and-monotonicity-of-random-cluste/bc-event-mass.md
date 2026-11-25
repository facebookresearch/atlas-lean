# Event mass under the random-cluster measure with a boundary graph

Let $G = (V, E)$ be a finite simple graph, $C$ a simple graph on $V$, $p, q \in \mathbb{R}$, and $A$ a set of assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included). The mass of $A$ is

$$\phi^C_{G,p,q}(A) = \sum_{\omega \in A} \phi^C_{G,p,q}(\omega),$$

where $\phi^C_{G,p,q}(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k_C(\omega)} / Z^C_{G}(p, q)$ is the [random-cluster probability with boundary wiring $C$](bc-prob.md); here $o(\omega)$ and $c(\omega)$ count the open and closed edges of $G$, $k_C(\omega)$ is the [number of clusters under the wiring $C$](num-clusters-bc.md), the number of connected components of the graph on $V$ whose edges are the edges of $G$ open in $\omega$ together with the edges of $C$, and $Z^C_G(p, q)$ is the sum of the numerators over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included).
