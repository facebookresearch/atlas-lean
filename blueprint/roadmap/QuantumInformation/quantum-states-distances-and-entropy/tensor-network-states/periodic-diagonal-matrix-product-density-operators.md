# Periodic diagonal matrix product density operators

A periodic, diagonal, translation-invariant matrix product density operator built from matrices $A_1, \dots, A_d$ assigns to every system size $L$ the diagonal operator whose entry at a basis word is the trace of the corresponding product of the matrices.

**Definition.** Given $d \ge 1$ complex $D \times D$ matrices $A_1, \dots, A_d$ with $D \ge 1$, the matrix product density operator for system size $L \geq 1$ is the diagonal operator

$$
\rho_A^L = \sum_{i_1, \dots, i_L = 1}^{d} \operatorname{tr}(A_{i_1} A_{i_2} \cdots A_{i_L})\, \lvert i_1 \cdots i_L\rangle\langle i_1 \cdots i_L\rvert
$$

on $(\mathbb{C}^d)^{\otimes L}$, not normalized. It is positive semidefinite exactly when every $\operatorname{tr}(A_{i_1} \cdots A_{i_L})$ is a nonnegative real number. Decision problems take the entries of $A_1, \dots, A_d$ as input, so they restrict them to integers (Problem 2 of the source) or rational numbers.

## Depends on

None.

## Proof depends on

None.

## Remarks

The trace closes the chain periodically, and the same matrices sit at every site. A family in purification form, $\sigma_B^L = \operatorname{tr}_{\mathrm{env}} \lvert\Psi\rangle\langle\Psi\rvert$ for a translation-invariant matrix product state $\lvert\Psi\rangle = \sum \operatorname{tr}(B_{i_1, e_1} \cdots B_{i_L, e_L}) \lvert i_1 e_1 \cdots i_L e_L \rangle$ with an environment index $e_j$ at each site, is positive semidefinite for every $L$ by construction.

## Sources

- G. De las Cuevas, T. S. Cubitt, J. I. Cirac, M. M. Wolf and D. Pérez-García, "Fundamental limitations in the purifications of tensor networks", *Journal of Mathematical Physics* 57(7), 071902, 2016, doi:[10.1063/1.4954983](https://doi.org/10.1063/1.4954983). Numbering of the version read, arXiv:1512.05709v2: Equation (1) (the periodic diagonal case, the classical case of matrix product density operators, in the introduction), Equation (2) (purification form), and Problem 2 (integer matrices).
