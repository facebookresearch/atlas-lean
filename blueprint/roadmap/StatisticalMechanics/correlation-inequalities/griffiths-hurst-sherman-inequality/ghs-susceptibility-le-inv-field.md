# GHS susceptibility bound $\chi \le 1/h$

Let $G = (V, E)$ be a finite simple graph, $\beta \ge 0$, $h > 0$ and $o \in V$, with the field entering
the Hamiltonian as $-h \sum_x \sigma_x$, and write $m(t) = \langle \sigma_o \rangle_{\beta, t}$ for the
[finite-volume Ising expectation](../griffiths-inequalities/ising-expectation.md). Then

$$m'(h) = \beta \sum_{x \in V} \bigl(\langle \sigma_o \sigma_x \rangle - \langle \sigma_o \rangle \langle \sigma_x \rangle\bigr) \le \frac1h,$$

the expectations taken at $(\beta, h)$ (R. B. Griffiths, C. A. Hurst and S. Sherman, *Concavity of magnetization of an Ising ferromagnet in a positive external field*, J. Math. Phys. 11 (1970) 790–795). The bound $\chi \le 1/h$ is a weak form of
the consequence $\chi \le m/h$ of [concavity](ghs-magnetization-concave-on.md).
