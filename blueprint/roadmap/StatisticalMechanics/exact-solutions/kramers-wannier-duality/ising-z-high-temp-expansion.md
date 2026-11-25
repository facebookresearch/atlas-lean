# High-temperature expansion

Let $G = (V, E)$ be a simple graph on a finite set $V$ and $\beta \in \mathbb{R}$. Then

$$Z_G(\beta) = 2^{|V|} (\cosh \beta)^{|E|} \sum_{F} (\tanh \beta)^{|F|},$$

the sum running over the subsets $F \subseteq E$ in which every vertex has even degree, where $Z_G(\beta) = \sum_{s} \exp\big(\beta \sum_{\{x,y\} \in E(G)} s_x s_y\big)$ is the zero-field [Ising partition function](../../spin-models/ising-model-on-a-finite-graph/the-finite-volume-ising-gibbs-measure/ising-z.md), the sum running over all spin configurations $s : V \to \{+1, -1\}$ (Friedli and Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University Press (2017), Section 3.7).
