# Resolvent kernel of quantum relative entropy

For positive semidefinite $\rho,\sigma\in M_\iota(\mathbb{C})$ and $t > 0$ define

$$
R_t(\rho,\sigma) = \sup_{X \in M_\iota(\mathbb{C})} \Big( 2\operatorname{Re}\operatorname{Tr}(X^*\rho) - \operatorname{Tr}(X^*\sigma X) - t\,\operatorname{Tr}(X^* X\rho) \Big),
$$

the inverse quadratic form at $\rho$ of the operator $X\mapsto \sigma X + tX\rho$. The supremum is attained even when $\rho,\sigma$ are singular, and in eigenbases $\rho=\sum_j\lambda_j u_ju_j^*$, $\sigma = \sum_i\mu_i v_iv_i^*$,

$$
R_t(\rho,\sigma) = \sum_{j,i} \frac{\lambda_j^2\, |\langle u_j, v_i\rangle|^2}{\mu_i + t\lambda_j},
$$

with terms whose denominator vanishes read as $0$ (their numerator vanishes too).

## Sources

- M. B. Ruskai, "Another short and elementary proof of strong subadditivity of quantum entropy", Reports on Mathematical Physics 60(1):1-12, 2007.
