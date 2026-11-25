# Finite-volume pressure decomposition for $\beta \ge 0$

Let $G = (V, E)$ be a simple graph on a finite set $V$ with $V$ nonempty, and $\beta \ge 0$. Then

$$\frac{\log Z_G(\beta)}{|V|} = \log 2 + \frac{|E|}{|V|} \log\cosh\beta + \frac{\log X_G(\tanh\beta)}{|V|},$$

where $Z_G(\beta) = \sum_{s} \exp\big(\beta \sum_{\{x,y\} \in E} s_x s_y\big)$ is the [zero-field Ising partition function](../high-temperature-expansion-of-the-ising-partitio/ons-z.md) with unit couplings, the sum over all spin configurations $s : V \to \{+1, -1\}$, and $X_G(x) = \sum_{F} x^{|F|}$ is the [even-subgraph generating function](../high-temperature-expansion-of-the-ising-partitio/ons-x.md), the sum over the subsets $F \subseteq E$ in which every vertex has even degree.
