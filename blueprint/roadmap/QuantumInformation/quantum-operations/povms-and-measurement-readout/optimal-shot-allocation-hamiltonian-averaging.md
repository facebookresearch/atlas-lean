# Optimal shot allocation for Hamiltonian averaging

When an energy is estimated as a weighted sum of independent sample means of Pauli measurements, the total number of shots needed for a target variance is minimized by allocating shots in proportion to $|w_\ell|\sigma_\ell$, and the minimal total is $(\sum_\ell|w_\ell|\sigma_\ell)^2/\epsilon^2$ in the continuous relaxation.

Let $H=\sum_{\ell=1}^{L}w_\ell H_\ell$ with $w_\ell\in\mathbb R$ and Hermitian $H_\ell$ with $H_\ell^2=\mathbf 1$ (for example Pauli strings), fix a state, and let $\sigma_\ell=\sqrt{1-\langle H_\ell\rangle^2}\ge0$ be the single-shot standard deviation of measuring $H_\ell$. Suppose $\langle H_\ell\rangle$ is estimated by the mean of $M_\ell$ independent shots, with the estimates for different $\ell$ mutually independent; then the estimator $\sum_\ell w_\ell\bar X_\ell$ of $\langle H\rangle$ has variance $\sum_\ell w_\ell^2\sigma_\ell^2/M_\ell$. Let $I=\{\ell:w_\ell\sigma_\ell\ne0\}$ be nonempty and $\epsilon>0$. Over real $M_\ell>0$, $\ell\in I$,

$$
\min\Bigl\{\sum_{\ell\in I}M_\ell:\ \sum_{\ell\in I}\frac{w_\ell^2\sigma_\ell^2}{M_\ell}\le\epsilon^2\Bigr\}=\frac{1}{\epsilon^2}\Bigl(\sum_{\ell\in I}|w_\ell|\sigma_\ell\Bigr)^2\le\frac{\Lambda^2}{\epsilon^2},\qquad\Lambda=\sum_{\ell=1}^{L}|w_\ell|,
$$

attained exactly at $M_\ell=|w_\ell|\sigma_\ell\bigl(\sum_{k\in I}|w_k|\sigma_k\bigr)/\epsilon^2$. Integer shot counts (for example rounding up) give at most $|I|$ extra shots. Terms with $\sigma_\ell=0$ and $w_\ell\ne0$ contribute no variance but have deterministic outcomes, so a single shot determines each of them; they are excluded from the variance-driven count.

## Context

Graduate/research. This governs the measurement cost of variational quantum eigensolvers for chemistry, where the $w_\ell$ are combinations of one- and two-electron integrals. Correlated estimators (for example two identical terms measured on the same shots) change the variance, which is why mutual independence is assumed; the result is a quantum-measurement statistics statement used by chemistry.

## Depends on

- [Expectation value of an observable](../../../Physics/quantum-mechanics/postulates-of-finite-dimensional-quantum-mechani/expectation-value.md)

## Proof depends on

- [Variance of a finite sum](../../../Probability/moments/variance-of-a-finite-sum/variance-sum.md)
- [Cauchy–Schwarz inequality in an inner product space](../../../Analysis/hilbert-spaces/inner-product-spaces-and-their-completions/cauchy-schwarz.md)

## Expansion

Variance: a single shot of $H_\ell$ has outcomes $\pm1$ with mean $\langle H_\ell\rangle$, hence variance $\sigma_\ell^2$; the mean of $M_\ell$ independent shots has variance $\sigma_\ell^2/M_\ell$, scaling by $w_\ell$ multiplies it by $w_\ell^2$ (Mathlib `variance_const_mul`), and independence makes covariances vanish in the variance of the sum (Mathlib `IndepFun.variance_sum`). Optimum on $I$: by Cauchy–Schwarz, $\bigl(\sum_{\ell\in I}|w_\ell|\sigma_\ell\bigr)^2\le\bigl(\sum_{\ell\in I}M_\ell\bigr)\bigl(\sum_{\ell\in I}w_\ell^2\sigma_\ell^2/M_\ell\bigr)\le\bigl(\sum_{\ell\in I}M_\ell\bigr)\epsilon^2$, with equality iff $M_\ell\propto|w_\ell|\sigma_\ell$ and the constraint is tight, which fixes the stated allocation. The final inequality uses $\sigma_\ell\le1$. The review of Cao, Aspuru-Guzik and coauthors writes $\sigma_i=1-\langle O_i\rangle^2$ (a variance) and then uses $\sigma_i$ as a standard deviation in its Eq. (73); Rubin, Babbush and McClean use the standard deviation consistently, as here.

## Sources

- Nicholas C. Rubin, Ryan Babbush and Jarrod McClean, *Application of fermionic marginal constraints to hybrid quantum algorithms*, New J. Phys. 20 (2018), <https://doi.org/10.1088/1367-2630/aab919>; numbers from arXiv:1801.03524v2, §IV.A, Eqs. (42)–(49). <https://arxiv.org/abs/1801.03524v2>
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §5.1.2, Eqs. (70)–(73). <https://arxiv.org/abs/1812.09976v2>
