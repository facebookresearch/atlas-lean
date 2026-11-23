# Inhomogeneous law of the agreement configuration

Let $G = (V, E)$ be a finite simple graph, $K$ real couplings on unordered pairs and $h \colon V \to \mathbb{R}$ site fields, and let $\langle \cdot \rangle$ be the [Gibbs expectation](../griffiths-inequalities/exp-j.md) with pair set $E$, couplings $K$ and fields $h$. For a configuration $q$, the probability that two independent replicas $(a, b)$ of this
model have [agreement configuration](ghs-lagreement.md) $q$ is

$$\frac{1}{Z^2} \sum_a w(a)\, w(\mathrm{mate}_q(a)),$$

with $w(a) = \exp\bigl(\sum_{e \in E} K_e \sigma_e(a) + \sum_x h_x \sigma_x(a)\bigr)$, $Z = \sum_a w(a)$
and $\mathrm{mate}_q(a)$ the [mate](ghs-lmate.md) of $a$ over $q$.
