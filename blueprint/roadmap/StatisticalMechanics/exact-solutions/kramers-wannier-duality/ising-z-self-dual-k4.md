# Kramers–Wannier duality

Let $K_4$ be the complete graph on four vertices and let $\beta, \beta^\ast \in \mathbb{R}$ with $\tanh \beta^\ast = e^{-2\beta}$. Then

$$Z_{K_4}(\beta^\ast) = \frac{2^4 \cosh(\beta^\ast)^6}{2\, e^{6\beta}}\, Z_{K_4}(\beta),$$

where $Z_G(\beta) = \sum_{s} \exp\big(\beta \sum_{\{x,y\} \in E(G)} s_x s_y\big)$ is the zero-field [Ising partition function](../../spin-models/ising-model-on-a-finite-graph/the-finite-volume-ising-gibbs-measure/ising-z.md), the sum running over all spin configurations $s : V \to \{+1, -1\}$ (Kramers and Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, Phys. Rev. 60 (1941)).
