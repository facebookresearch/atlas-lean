# Kramers–Wannier duality

Let $V$ be a finite set and let $G_p$ (primal) and $G_d$ (dual) be simple graphs on $V$, with $V$ nonempty and $G_p$ connected, and suppose there is an [edge crossing](edge-crossing.md) from $G_p$ to $G_d$. Then for all $\beta, \beta^\ast \in \mathbb{R}$ with $\tanh \beta^\ast = e^{-2\beta}$,

$$Z_{G_d}(\beta^\ast) = \frac{2^{|V|} \cosh(\beta^\ast)^{|E(G_d)|}}{2\, e^{\beta |E(G_p)|}}\, Z_{G_p}(\beta),$$

where $Z_G(\beta) = \sum_{s} \exp\big(\beta \sum_{\{x,y\} \in E(G)} s_x s_y\big)$ is the zero-field [Ising partition function](../../spin-models/ising-model-on-a-finite-graph/the-finite-volume-ising-gibbs-measure/ising-z.md), the sum running over all spin configurations $s : V \to \{+1, -1\}$ (Kramers and Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, Phys. Rev. 60 (1941)).
