# Kramers–Wannier duality

Let $V$ be a finite set and let $G_p$ (primal) and $G_d$ (dual) be simple graphs on $V$. Suppose $V$ is nonempty and $G_p$ is connected, and let $\psi$ be a bijection of the unordered pairs of elements of $V$ such that $\psi$ maps edges of $G_p$ to edges of $G_d$, $\psi^{-1}$ maps edges of $G_d$ to edges of $G_p$, and $\psi(C)$ is an even subgraph of $G_d$ for every cut set $C$ of $G_p$, and suppose that for every closed walk $W$ of $G_d$ there is $S : V \to \{0, 1\}$ such that for all adjacent $u, v$ in $G_p$, $\{u, v\} \in \psi^{-1}(E(W))$ if and only if $S(u) \ne S(v)$, where $E(W)$ is the set of edges traversed by $W$. Then for all $\beta, \beta^\ast \in \mathbb{R}$ with $\tanh \beta^\ast = e^{-2\beta}$,

$$Z_{G_d}(\beta^\ast) = \frac{2^{|V|} \cosh(\beta^\ast)^{|E(G_d)|}}{2\, e^{\beta |E(G_p)|}}\, Z_{G_p}(\beta),$$

where $Z_G(\beta) = \sum_{s} \exp\big(\beta \sum_{\{x,y\} \in E(G)} s_x s_y\big)$ is the zero-field [Ising partition function](../../spin-models/ising-model-on-a-finite-graph/the-finite-volume-ising-gibbs-measure/ising-z.md), the sum running over all spin configurations $s : V \to \{+1, -1\}$ (Kramers and Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, Phys. Rev. 60 (1941)).
