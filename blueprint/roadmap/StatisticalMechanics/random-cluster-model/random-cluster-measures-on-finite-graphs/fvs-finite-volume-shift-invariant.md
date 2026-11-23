# Boundary-matching isomorphisms transport FK edge marginals

Let $G$ and $H$ be simple graphs on finite sets $V$ and $W$, and let $\sigma : V \to W$ be a bijection with $x \sim_G y \iff \sigma(x) \sim_H \sigma(y)$ for all $x, y$, and let $\partial_V \subseteq V$, $\partial_W \subseteq W$ with $x \in \partial_V \iff \sigma(x) \in \partial_W$. For all $p, q \in \mathbb{R}$ and every unordered pair $e$ of elements of $V$,

$$\phi^w_{H,\partial_W,p,q}(\sigma(e) \text{ open}) = \phi^w_{G,\partial_V,p,q}(e \text{ open}), \qquad \phi_{H,p,q}(\sigma(e) \text{ open}) = \phi_{G,p,q}(e \text{ open}),$$

where $\phi^w$ is the [wired random-cluster probability](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md), $\phi$ the [random-cluster probability](fk-prob.md), and $\mu(e \text{ open}) = \sum_{\omega :\ \omega(e) \text{ open}} \mu(\omega)$ is the [edge marginal](../fkg-inequality-and-monotonicity-of-random-cluste/edge-marg-prob.md).
