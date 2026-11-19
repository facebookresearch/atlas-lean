# Conditional two-replica expectation given the agreement

Let $G = (V, E)$ be a finite simple graph and $\beta, h \in \mathbb{R}$. For a function $F$ of two configurations and a configuration $q$, the conditional
two-replica expectation of $F$ given the agreement configuration $q$ is the
[fibre numerator](ghs-lfibre-numerator.md) divided by the [fibre mass](ghs-lfibre-mass.md):

$$\frac{\sum_a w(a)\, w(\bar a)\, F(a, \bar a)}{\sum_a w(a)\, w(\bar a)},$$

with $w(a) = e^{-\beta H(a)}$ the [Boltzmann weight](../../spin-models/ising-model-on-a-finite-graph/the-finite-volume-ising-gibbs-measure/ising-weight.md) and $\bar a = \mathrm{mate}_q(a)$ the [mate](ghs-lmate.md) of $a$ over $q$.
