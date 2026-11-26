# Lee–Yang polynomial of a finite Ising model

Let $G = (V, E)$ be a finite simple graph and $\beta \in \mathbb{R}$. The Lee–Yang polynomial of the Ising
model on $G$ is

$$P(X) = \sum_{\sigma} \exp\Bigl(\beta \sum_{\{x, y\} \in E} \sigma_x \sigma_y\Bigr) X^{k(\sigma)} \in \mathbb{R}[X],$$

the sum over all spin configurations $\sigma \in \{1, -1\}^V$, with $k(\sigma)$ the
[number of minus spins](minus-spin-count.md). Its variable stands for the fugacity $e^{-2\beta h}$ of a
field $h$.
