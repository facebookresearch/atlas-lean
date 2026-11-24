# Wired tilted log normalizer as a cumulant generating function

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices. If $q > 0$ and $|E| > 0$, then for every $t \in \mathbb{R}$

$$F^w_{G,\partial,q}(t) = \frac{1}{|E|} \log \sum_\omega q^{k^w(\omega)} e^{t\, o(\omega)},$$

where $F^w_{G,\partial,q}$ is the [wired per-edge ambient tilted log-normalizer](wpd-wired-ambient-tilt-log-z.md), the sum runs over all assignments $\omega$ of open/closed states to the unordered pairs of vertices, $o(\omega)$ is the number of open edges of $G$, and $k^w(\omega)$ is the number of connected components of the graph whose edges are the open edges of $G$ together with all pairs of distinct vertices of $\partial$. The right-hand side is $|E|^{-1}$ times the [log-sum-exp function](ivp2-kcgf.md) with weights $q^{k^w(\omega)}$ and exponents $o(\omega)$.
