# Euler decomposition of single-qubit unitaries

For real $\theta, \alpha, \delta$ let

$$R_y(\theta) = \begin{pmatrix} \cos\frac{\theta}{2} & \sin\frac{\theta}{2} \\ -\sin\frac{\theta}{2} & \cos\frac{\theta}{2} \end{pmatrix}, \qquad
R_z(\alpha) = \begin{pmatrix} e^{i\alpha/2} & 0 \\ 0 & e^{-i\alpha/2} \end{pmatrix}, \qquad
\mathrm{Ph}(\delta) = e^{i\delta} I .$$

Every unitary $2 \times 2$ matrix $U$ can be written as $U = \mathrm{Ph}(\delta)\, R_z(\alpha)\, R_y(\theta)\, R_z(\beta)$
with $\delta, \alpha, \theta, \beta \in \mathbb{R}$, and every $W \in SU(2)$ as $W = R_z(\alpha)\, R_y(\theta)\, R_z(\beta)$.
Moreover $R_y(\theta_1) R_y(\theta_2) = R_y(\theta_1 + \theta_2)$, $R_z(\alpha_1) R_z(\alpha_2) = R_z(\alpha_1 + \alpha_2)$,
$X R_y(\theta) X = R_y(-\theta)$ and $X R_z(\alpha) X = R_z(-\alpha)$.

Proof idea: the rows and columns of a unitary $2 \times 2$ matrix are orthonormal, so it has the form
$\begin{pmatrix} e^{i(\delta + \alpha/2 + \beta/2)} \cos\frac{\theta}{2} & e^{i(\delta + \alpha/2 - \beta/2)} \sin\frac{\theta}{2} \\ -e^{i(\delta - \alpha/2 + \beta/2)} \sin\frac{\theta}{2} & e^{i(\delta - \alpha/2 - \beta/2)} \cos\frac{\theta}{2} \end{pmatrix}$;
for determinant $1$, $e^{i\delta} = \pm 1$ and the sign is absorbed into $R_z(\alpha)$.

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 4, Lemma 4.1, the definitions after it, and Lemma 4.2.
