# Conditional probability that an edge is open given the rest

Let $G = (V, E)$ be a simple graph on a finite set $V$, $p, q \in \mathbb{R}$, $e$ an unordered pair of elements of $V$, and $\omega$ a configuration. The conditional open probability is

$$\frac{\phi_{G,p,q}(\omega^{e,\mathrm{open}})}{\phi_{G,p,q}(\omega^{e,\mathrm{open}}) + \phi_{G,p,q}(\omega^{e,\mathrm{closed}})},$$

where $\omega^{e,\mathrm{open}}$ and $\omega^{e,\mathrm{closed}}$ are $\omega$ with $e$ set open, resp. closed, $\phi_{G,p,q}$ is the [random-cluster probability](fk-prob.md), and a zero denominator gives $0$. When $0 \le p \le 1$, $q > 0$ and the denominator is positive (always the case when $0 < p < 1$ and $q > 0$), it is the conditional probability under $\phi_{G,p,q}$ that $e$ is open given the states of all other pairs.
