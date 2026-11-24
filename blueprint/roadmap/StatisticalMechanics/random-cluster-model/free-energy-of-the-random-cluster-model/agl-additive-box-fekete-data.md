# Doubling, boundedness and oscillation data along $K_j$

Let $d \in \mathbb{N}$ and $t \in \mathbb{R}$. The box data at $t$ hold when all three of the following hold, where $K_j = 2^{j+1} - 1$ are the [scales](agl-k.md), $u_t(n) = -\log Z_{\Lambda_n}(\sigma(t), 2)$ is the [negative log ambient normalizer](agl-ambient-neg-log-z.md) of $\Lambda_n$, $E(n)$ is the [number of edges](agl-e.md) of $\Lambda_n$, and $F_{\Lambda_n}(t)$ is the [ambient tilted log-normalizer](../convexity-of-the-free-energy-and-edge-densities/ivp2-ambient-tilt-log-z.md) of $\Lambda_n$ at $q = 2$, $F_{G}(t) = |E(G)|^{-1} \log Z_G(\sigma(t), 2) + \log(1 + e^t)$:

- the [additive doubling bound](agl-additive-doubling-bound.md) along $K_j$ holds at $t$;
- there is $M \in \mathbb{R}$ with $|u_t(K_j)/E(K_j)| \le M$ for every $j$;
- there are $b : \mathbb{N} \to \mathbb{N}$ with $b(n) \to \infty$ and $(\mathrm{osc}_j)$ with $\mathrm{osc}_j \to 0$ such that $|F_{\Lambda_n}(t) - F_{\Lambda_{K_{b(n)}}}(t)| \le \mathrm{osc}_{b(n)}$ for every $n$.
