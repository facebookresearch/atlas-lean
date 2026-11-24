# Abstract form of the sharpness theorem

Let $V$ be a set with a distinguished element $o$, let $\beta_c > 0$, $m \colon \mathbb{R} \to \mathbb{R}$ and $c \colon V \times V \to \mathbb{R}$
with $c \ge 0$. Suppose that $m^2$ is continuous on $[\beta_c, \infty)$ and differentiable on $(\beta_c, \infty)$, that
$(m^2)'(\beta) \ge \frac{2}{\beta}(1 - m(\beta)^2)$ for $\beta > \beta_c$, that $m(\beta_c) = 0$ and $m \ge 0$ on $[\beta_c, \infty)$,
and that for some $N \in \mathbb{N}$ and $\varphi \in [0, 1)$ every finite $\Lambda \subseteq V$ satisfies
$\sum_{z \in \Lambda} c(o, z) \le N + \varphi N/(1 - \varphi)$. Then

- $m(\beta) \ge \sqrt{1 - (\beta_c/\beta)^2}$ for every $\beta > \beta_c$, and
- $z \mapsto c(o, z)$ is summable, with $\sum_z c(o, z) \le N/(1 - \varphi)$.

The regularity of $m^2$ is one-sided at $\beta_c$, as in the [integrated mean-field lower bound](../mean-field-lower-bound-for-the-ising-magnetizati/meanfield-lower-bound.md).
The [sharpness theorem](sharpness-of-the-phase-transition-for-the-ising/ising-sharp-phase-transition.md) is the Ising
case.
