# Single-machine versus family subexponential time

For a parameter $\mu$ of instances, say a problem is decidable in **family subexponential time** if for every $\delta>0$ some machine $M_\delta$ decides it in time $2^{\delta\mu}\mathrm{poly}(L)$, and in **single-machine subexponential time** if one machine decides it in time $2^{s(\mu)}\mathrm{poly}(L)$ for a function $s(\mu)=o(\mu)$. The single-machine notion implies the family notion; conversely, if the machines $M_\delta$ (for $\delta=1/j$) are produced by a uniform computable family whose running-time constants are computable, a single machine is obtained by switching from $M_{1/j}$ to $M_{1/(j+1)}$ at computable thresholds of $\mu$. The ETH is stated with the family notion.

## Proof sketch

Choose increasing thresholds $\mu_j$ beyond which the constant overhead of $M_{1/(j+1)}$ is dominated by $2^{\mu/j}$; on instances with $\mu\in[\mu_j,\mu_{j+1})$ run $M_{1/j}$, giving exponent $s(\mu)\le\mu/j(\mu)=o(\mu)$.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Sources

- Russell Impagliazzo and Ramamohan Paturi, "On the Complexity of k-SAT", Journal of Computer and System Sciences 62(2), 2001.
- Russell Impagliazzo, Ramamohan Paturi and Francis Zane, "Which Problems Have Strongly Exponential Complexity?", Journal of Computer and System Sciences 63(4), 2001.
