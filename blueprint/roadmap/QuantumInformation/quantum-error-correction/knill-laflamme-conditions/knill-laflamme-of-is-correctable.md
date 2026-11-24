# Necessity of the Knill–Laflamme conditions

Let $P$ be an orthogonal projector ($P^{*} = P$, $P^2 = P$) on $\mathbb{C}^n$. If the errors
$A_a$ are [correctable](is-correctable.md) on the code $\operatorname{range} P$, then for all
$a$ and $b$ there is a scalar $c_{ab}$ with

$$P A_a^{*} A_b P = c_{ab} P.$$

This is the "only if" half of Knill and Laflamme's Theorem 3.2, in projector form. The proof
inserts $I = \sum_r R_r^{*} R_r$ between $A_a^{*}$ and $A_b$:
$P A_a^{*} A_b P = \sum_r (R_r A_a P)^{*} (R_r A_b P) = \big(\sum_r \overline{\lambda_{ra}} \lambda_{rb}\big) P$.

For example, the bit flip $X$ together with the identity is not correctable on the whole qubit
space, because $X$ is not a multiple of $I$.

## Sources

- E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, Phys. Rev. A 55 (1997), 900–911, arXiv:quant-ph/9604034, Section 3.1 and Theorems 3.1–3.2.
