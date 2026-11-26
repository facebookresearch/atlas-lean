# Self-improvement for symmetric low individual degree strategies

Consider a finite tensor strategy over $\mathbb{F}$ with a swap-invariant state and identical local projective measurements that passes the axis-line and point-consistency checks with losses $\varepsilon$ and $\delta$. Then there is a single local submeasurement $\{G_g\}$ indexed by polynomials $g$ of individual degree at most $d$, completed by a failure outcome, and a positive common operator majorant, such that completeness loss, point mismatch, successful self-consistency and the dual gap are all at most $100\, m \big(\sqrt\varepsilon + \sqrt\delta + \sqrt{d/|\mathbb{F}|}\big)$. A projective version holds with error $3000\, m \big(\varepsilon^{1/32} + \delta^{1/32} + (d/|\mathbb{F}|)^{1/32}\big)$, with outputs on the original local space.

## Proof sketch

Formulate the search for the best polynomial measurement as a semidefinite program maximizing the average agreement with the point measurements; strong duality gives a common majorant certifying optimality, and complementary slackness turns approximate consistency of the original measurements into strong self-consistency of the optimizer. Orthogonalization of nearly projective measurements gives the projective version.

## Depends on

- [The low individual degree test](the-low-individual-degree-test.md)
- [Entangled strategies and the entangled value of a game](../entangled-nonlocal-games/entangled-strategies-and-entangled-value.md)

## Proof depends on

- [Strong duality for the self-improvement semidefinite program](strong-duality-for-self-improvement-sdp.md)
- [Projective strategies suffice (Naimark dilation)](../entangled-nonlocal-games/projective-strategies-suffice.md)

## Sources

- Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, "Quantum Soundness of the Classical Low Individual Degree Test", arXiv:2009.12982, 2020.
