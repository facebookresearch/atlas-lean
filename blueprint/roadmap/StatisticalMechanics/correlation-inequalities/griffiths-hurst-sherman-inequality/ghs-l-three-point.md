# Griffiths–Hurst–Sherman inequality

Let $G = (V, E)$ be a finite simple graph and $\beta, h \in \mathbb{R}$ with $\beta \ge 0$ and $h \ge 0$, and let $\langle \cdot \rangle$ be the [finite-volume Ising expectation](../griffiths-inequalities/ising-expectation.md) at $(\beta, h)$. For every site $o$ and every
edge $\{x, y\} \in E$,

$$\langle \sigma_o \sigma_x \sigma_y \rangle - \langle \sigma_o \rangle \langle \sigma_x \sigma_y \rangle \le \bigl(\langle \sigma_o \sigma_x \rangle - \langle \sigma_o \rangle \langle \sigma_x \rangle\bigr) \langle \sigma_y \rangle + \bigl(\langle \sigma_o \sigma_y \rangle - \langle \sigma_o \rangle \langle \sigma_y \rangle\bigr) \langle \sigma_x \rangle,$$

equivalently the [third Ursell function](eg-ursell3.md) $u_3(o, x, y) \le 0$ (R. B. Griffiths, C. A. Hurst and S. Sherman, *Concavity of magnetization of an Ising ferromagnet in a positive external field*, J. Math. Phys. 11 (1970) 790–795); proof of J. L. Lebowitz, *GHS and other
inequalities*, Comm. Math. Phys. 35 (1974).
