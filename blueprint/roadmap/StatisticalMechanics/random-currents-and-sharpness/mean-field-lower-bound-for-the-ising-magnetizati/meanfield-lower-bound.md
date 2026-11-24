# Integrated mean-field lower bound from $m(\beta_0) = 0$

Let $\beta_0 > 0$ and $m \colon \mathbb{R} \to \mathbb{R}$ be such that $m^2$ is continuous on $[\beta_0, \infty)$ and differentiable on
$(\beta_0, \infty)$, with

$$(m^2)'(\beta) \ge \frac{2}{\beta} \bigl(1 - m(\beta)^2\bigr) \quad \text{for } \beta > \beta_0,$$

$m(\beta_0) = 0$ and $m(\beta) \ge 0$ for $\beta \ge \beta_0$. Then $m(\beta) \ge \sqrt{1 - (\beta_0/\beta)^2}$ for every $\beta \ge \beta_0$.

Differentiability of $m^2$ at $\beta_0$ itself cannot be required together with $m(\beta_0) = 0$: since $m^2 \ge 0$ vanishes at
$\beta_0$, its derivative there would be $0$, while the bound forces right difference quotients at least
$(\beta + \beta_0)/\beta^2 \to 2/\beta_0 > 0$. The [version without an initial condition](meanfield-lower-bound-of-initial-nonneg.md)
has no such constraint.
