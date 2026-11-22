# Inhomogeneous conditional expectation given the agreement

Let $G = (V, E)$ be a finite simple graph, $K$ real couplings on unordered pairs and $h \colon V \to \mathbb{R}$ site fields, and let $w(a) = \exp\bigl(\sum_{e \in E} K_e \sigma_e(a) + \sum_x h_x \sigma_x(a)\bigr)$. For a function $F$ of two configurations and a configuration $q$,
the conditional two-replica expectation of $F$ given the agreement configuration $q$ is

$$\frac{\sum_a w(a)\, w(\bar a)\, F(a, \bar a)}{\sum_a w(a)\, w(\bar a)},$$

with $\bar a = \mathrm{mate}_q(a)$ the [mate](ghs-lmate.md) of $a$ over $q$: the [fibre numerator](ghsi-fibre-numerator.md) over the
[fibre mass](ghsi-fibre-mass.md).
