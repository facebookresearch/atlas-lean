# Joint convexity of the resolvent kernel

For $t>0$, finitely many positive semidefinite pairs $(\rho_k,\sigma_k)$ and weights $w_k \ge 0$ (not necessarily summing to one),

$$
R_t\Big(\sum_k w_k\rho_k,\ \sum_k w_k\sigma_k\Big) \le \sum_k w_k\, R_t(\rho_k,\sigma_k).
$$

## Proof sketch

For a fixed test matrix $X$ the objective $2\operatorname{Re}\operatorname{Tr}(X^*\rho) - \operatorname{Tr}(X^*\sigma X) - t\operatorname{Tr}(X^*X\rho)$ is linear in the pair $(\rho,\sigma)$. Evaluating the mixture at its maximizer and bounding each component's objective by its supremum gives the inequality.

## Depends on

- [Resolvent kernel of quantum relative entropy](relative-entropy-resolvent-kernel.md)

## Proof depends on

- [Resolvent kernel of quantum relative entropy](relative-entropy-resolvent-kernel.md)

## Sources

- M. B. Ruskai, "Another short and elementary proof of strong subadditivity of quantum entropy", Reports on Mathematical Physics 60(1):1-12, 2007.
