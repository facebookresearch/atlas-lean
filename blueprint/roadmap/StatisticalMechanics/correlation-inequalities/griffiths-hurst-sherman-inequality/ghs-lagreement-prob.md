# Law of the agreement configuration of two replicas

Let $G = (V, E)$ be a finite simple graph and $\beta, h \in \mathbb{R}$. For a configuration $q$ on $V$, the probability that two independent replicas $(a, b)$
of the Ising model have [agreement configuration](ghs-lagreement.md) $q$ is

$$\pi(q) = \frac{1}{Z^2} \sum_{a} w(a)\, w(\mathrm{mate}_q(a)),$$

the [total fibre weight](ghs-lfibre-mass.md) over $q$ divided by $Z^2$, with $w(a) = e^{-\beta H(a)}$ the [Boltzmann weight](../../spin-models/ising-model-on-a-finite-graph/the-finite-volume-ising-gibbs-measure/ising-weight.md), $Z$ the
partition function and $\mathrm{mate}_q(a)$ the [mate](ghs-lmate.md) of $a$ (the second replica is
determined by $a$ and $q$).
