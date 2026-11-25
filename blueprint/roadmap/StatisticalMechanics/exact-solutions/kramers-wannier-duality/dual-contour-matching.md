# Dual high-temperature expansion proportional to the partition function

Let $V$ be a finite set and let $G_p$ (primal) and $G_d$ (dual) be simple graphs on $V$, and $\beta, \beta^\ast, c \in \mathbb{R}$. The dual contour matching holds when $\tanh \beta^\ast = e^{-2\beta}$ and

$$2^{|V|} \cosh(\beta^\ast)^{|E(G_d)|} \sum_{F} \tanh(\beta^\ast)^{|F|} = c\, Z_{G_p}(\beta),$$

where the sum runs over the [even subgraphs](even-subgraphs.md) $F$ of $G_d$ and $Z_G(\beta) = \sum_{s} \exp\big(\beta \sum_{\{x,y\} \in E(G)} s_x s_y\big)$ is the zero-field [Ising partition function](../../spin-models/ising-model-on-a-finite-graph/the-finite-volume-ising-gibbs-measure/ising-z.md), the sum running over all spin configurations $s : V \to \{+1, -1\}$.
