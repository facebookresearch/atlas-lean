# Gibbs expectation with a site field

Let $G = (V, E)$ be a finite simple graph, $\beta \in \mathbb{R}$, $J$ real couplings and $H \colon V \to \mathbb{R}$ a site field. For a function $f$ of the spin
configurations, this is $\sum_\sigma f(\sigma)\, w(\sigma) / Z$, with $w(\sigma) = \exp\bigl(\beta (\sum_{\{x, y\} \in E} J_{xy} \sigma_x \sigma_y + \sum_{x \in V} H_x \sigma_x)\bigr)$ the [Boltzmann weight](vertex-field-weight.md)
and $Z = \sum_\sigma w(\sigma)$.
