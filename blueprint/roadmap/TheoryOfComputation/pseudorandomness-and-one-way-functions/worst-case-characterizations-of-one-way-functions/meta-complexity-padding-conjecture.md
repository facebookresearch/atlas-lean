# The Meta-Complexity Padding Conjecture

For a constant $\delta>0$ and a polynomial $p$, $\mathrm{Gap}_\delta(K^p\ \mathrm{vs}\ K)$ is the promise problem with YES instances $\{x: K^{p(|x|)}(x)\le|x|^{\delta}\}$ and NO instances $\{x: K(x)\ge|x|-3\}$; it asks to approximate $K^{p(|x|)}(x)$ within a factor $|x|^{1-\delta}$, with NO instances having high time-unbounded complexity. A reduction to $\mathrm{dpK}$ is **size-expanding** if, on input $\varphi$, every query has size parameter $s=\omega(|\varphi|)$.

**Meta-Complexity Padding Conjecture** (a conjecture, not a theorem): for every polynomial $p$ there are constants $\epsilon,\delta>0$ and a randomized polynomial-time size-expanding reduction from $\mathrm{Gap}_\delta(K^p\ \mathrm{vs}\ K)$ to a $(1+\epsilon)$-factor approximation of $\mathrm{dpK}^{\tau}$ for all large polynomials $\tau$. Randomness is essential: no deterministic size-expanding reduction from a non-trivial language to $\mathrm{dpK}^{\tau}$ exists.

## Depends on

- [Distributional Kolmogorov complexity dK^t_λ(x|D) and its probabilistic variant](distributional-kolmogorov-complexity.md)

## Sources

- Shuichi Hirahara, "Capturing One-Way Functions via NP-Hardness of Meta-Complexity", STOC (2023), ECCC TR23-037.
