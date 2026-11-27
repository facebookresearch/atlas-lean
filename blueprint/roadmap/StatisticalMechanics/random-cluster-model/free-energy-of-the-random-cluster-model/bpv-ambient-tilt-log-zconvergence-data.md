# Dyadic convergence data for the ambient tilted log normalizer

Let $d \in \mathbb{N}$ and $t \in \mathbb{R}$, and let $F_{\Lambda_n}(t)$ is the [ambient tilted log-normalizer](../convexity-of-the-free-energy-and-edge-densities/ivp2-ambient-tilt-log-z.md) of $\Lambda_n$ at $q = 2$, $F_{G}(t) = |E(G)|^{-1} \log Z_G(\sigma(t), 2) + \log(1 + e^t)$. The dyadic convergence data at $t$ hold when there are real sequences $(\delta_j)$ and $(\mathrm{osc}_j)$ such that

- $\delta_j \ge 0$ for all $j$ and $\sum_j \delta_j$ converges;
- $F_{\Lambda_{2^j}}(t) - \delta_j \le F_{\Lambda_{2^{j+1}}}(t)$ for every $j$;
- the set $\{F_{\Lambda_{2^j}}(t) : j \in \mathbb{N}\}$ is bounded above;
- $\mathrm{osc}_j \to 0$, and $|F_{\Lambda_n}(t) - F_{\Lambda_{2^{\lfloor \log_2 n \rfloor}}}(t)| \le \mathrm{osc}_{\lfloor \log_2 n \rfloor}$ for every $n \ge 1$.
