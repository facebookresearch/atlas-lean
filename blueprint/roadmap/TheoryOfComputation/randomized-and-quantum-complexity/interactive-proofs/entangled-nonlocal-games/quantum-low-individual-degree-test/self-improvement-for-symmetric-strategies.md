# Self-improvement for symmetric low individual degree strategies

Consider a symmetric strategy over $\mathbb{F}$ (swap-invariant state, identical measurements for both players) for the $m$-variate low individual degree test that passes the axis-parallel lines test with probability at least $1 - \varepsilon$ and the self-consistency test with probability at least $1 - \delta$, and let $\{G_g\}$ be a measurement on polynomials of individual degree at most $d$ that disagrees with the point measurements with probability at most $\nu$ on average. Let $\zeta = 100\, m \big(\sqrt\varepsilon + \sqrt\delta + \sqrt{d/|\mathbb{F}|}\big)$. Then there is a local submeasurement $\{H_h\}$ on such polynomials and a positive semidefinite operator $Z$ that dominates, for every such $h$, the average over points $u$ of the point measurement's operator for outcome $h(u)$, such that the completeness of $H$ is at least $1 - \nu - \zeta$, and its disagreement with the point measurements, its failure of strong self-consistency and the boundedness gap given by $Z$ are each at most $\zeta$ (Ji et al. 2020, Lemma 9.1). A projective submeasurement $H$ with the corresponding properties (boundedness now meaning that $Z$ paired with the failure outcome of $H$ has weight at most $\zeta$) exists with $\zeta = 3000\, m \big(\varepsilon^{1/32} + \delta^{1/32} + (d/|\mathbb{F}|)^{1/32}\big)$ (Ji et al. 2020, Theorem 6.2).

## Proof sketch

Formulate the search for the best polynomial measurement as a semidefinite program maximizing the average agreement with the point measurements; strong duality gives a common majorant certifying optimality, and complementary slackness turns approximate consistency of the original measurements into strong self-consistency of the optimizer. Orthogonalization of nearly projective measurements gives the projective version.

## Depends on

- [The low individual degree test](the-low-individual-degree-test.md)
- [Entangled strategies and the entangled value of a game](../entangled-strategies-and-entangled-value.md)

## Proof depends on

- [Strong duality for the self-improvement semidefinite program](strong-duality-for-self-improvement-sdp.md)
- [Projective strategies suffice (Naimark dilation)](../projective-strategies-suffice.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum Soundness of the Classical Low Individual Degree Test", arXiv:2009.12982, 2020.
