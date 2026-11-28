# Resolvent kernel of quantum relative entropy

For positive semidefinite $\rho,\sigma\in M_\iota(\mathbb{C})$ and $t > 0$ define

$$
R_t(\rho,\sigma) = \sup_{X \in M_\iota(\mathbb{C})} \Big( 2\operatorname{Re}\operatorname{Tr}(X^*\rho) - \operatorname{Tr}(X^*\sigma X) - t\,\operatorname{Tr}(X^* X\rho) \Big),
$$

the inverse quadratic form at $\rho$ of the operator $L_\sigma + tR_\rho : X\mapsto \sigma X + tX\rho$ on $M_\iota(\mathbb{C})$ with the Hilbert-Schmidt inner product $\langle A,B\rangle = \operatorname{Tr}A^*B$. When $\sigma$ is positive definite, $L_\sigma + tR_\rho$ is invertible, the supremum is attained at $X = (L_\sigma + tR_\rho)^{-1}(\rho)$, and

$$
R_t(\rho,\sigma) = \operatorname{Tr}\,\rho\,(L_\sigma + tR_\rho)^{-1}(\rho).
$$

## Proof sketch

For invertible $A = L_\sigma + tR_\rho$, which is self-adjoint and positive for the Hilbert-Schmidt inner product, expanding $0 \le \langle A^{-1/2}\rho - A^{1/2}X,\, A^{-1/2}\rho - A^{1/2}X\rangle$ gives $\langle\rho, A^{-1}\rho\rangle \ge 2\operatorname{Re}\langle X,\rho\rangle - \langle X, AX\rangle$, with equality at $X = A^{-1}\rho$; the right side is the objective above.

The same computation in coordinates covers singular $\rho,\sigma$. In eigenbases $\rho=\sum_j\lambda_j u_ju_j^*$ and $\sigma = \sum_i\mu_i v_iv_i^*$, the matrices $v_iu_j^*$ form an orthonormal basis of $M_\iota(\mathbb{C})$ in which $L_\sigma + tR_\rho$ is diagonal with eigenvalues $\mu_i + t\lambda_j$, and $\rho$ has coefficient $\lambda_j\langle v_i,u_j\rangle$, which vanishes whenever $\mu_i + t\lambda_j = 0$. Maximizing coordinatewise, the supremum is attained and

$$
R_t(\rho,\sigma) = \sum_{j,i} \frac{\lambda_j^2\, |\langle u_j, v_i\rangle|^2}{\mu_i + t\lambda_j},
$$

with terms whose denominator vanishes read as $0$.

## Sources

- M. B. Ruskai, "Another short and elementary proof of strong subadditivity of quantum entropy", Reports on Mathematical Physics 60(1):1-12, 2007, Section 2.1 (left and right multiplication), statement (II) of Section 2.2, and Section 2.4, eqs. (16)-(17).
