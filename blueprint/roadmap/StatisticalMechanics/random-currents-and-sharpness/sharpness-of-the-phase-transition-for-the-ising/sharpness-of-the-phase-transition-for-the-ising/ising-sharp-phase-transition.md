# Sharpness of the Ising phase transition on $\mathbb{Z}^d$, $d \ge 2$

Let $d \ge 2$, let $\beta_c = \beta_c(d) = \inf\{\beta \ge 0 : m^*(\beta) > 0\}$ be the
[critical inverse temperature](../../../gibbs-states-and-phase-transitions/phase-transition-of-the-ising-model/beta-c.md) ($0$ if
the set is empty), with $m^*$ the spontaneous magnetization, and let $\langle \sigma_0 \sigma_z \rangle^+_\beta$ be the zero-field
plus-state two-point function. Then:

- for every $\beta \ge \beta_c$, $m^*(\beta) \ge \sqrt{1 - (\beta_c/\beta)^2}$;
- for every $0 \le \beta < \beta_c$, $z \mapsto \langle \sigma_0 \sigma_z \rangle^+_\beta$ is summable over $\mathbb{Z}^d$, and there is $c > 0$ with
  $\langle \sigma_0 \sigma_z \rangle^+_\beta \le e^{-c \|z\|_1}$ for every $z$, where $\|z\|_1 = \sum_i |z_i|$.

(H. Duminil-Copin and V. Tassion, *A new proof of the sharpness of the phase transition for Bernoulli
percolation and the Ising model*, Comm. Math. Phys. 343 (2016) 725–745, arXiv:1502.03050v3, Theorem 2.1;
first proved in M. Aizenman, D. J. Barsky and R. Fernández, *The phase transition in a general class of
Ising-type models is sharp*, J. Stat. Phys. 47 (1987) 343–374.)

The [existence of the phase transition](../../../gibbs-states-and-phase-transitions/phase-transition-of-the-ising-model/ising-phase-transition-of-two-le.md)
locates $\beta_c$ in $(0, \infty)$.
