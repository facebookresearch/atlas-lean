# Decomposition of a unitary into two-level unitaries

For every $d \ge 0$ and every unitary $d \times d$ complex matrix $U$ there are a list $M_1, \dots, M_m$ of unitary matrices,
each [two-level](../../../LinearAlgebra/not-yet-classified/two-level/is-two-level.md) on some pair of indices, with $m \le d(d-1)/2$, and complex numbers $\varphi_1, \dots, \varphi_d$
with $|\varphi_k| = 1$, such that

$$U = M_1 M_2 \cdots M_m \cdot \operatorname{diag}(\varphi_1, \dots, \varphi_d).$$

The factors are found column by column, as in Gaussian elimination with Givens rotations: two-level unitaries zero the
entries below the diagonal of the first column, which leaves a unit complex number on the diagonal, and the procedure
repeats on the remaining $(d - 1) \times (d - 1)$ block.

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 8 ("Reck et al. note that a formula exists for the decomposition of any unitary matrix into matrices only involving a U(2) operation acting in the space of pairs of states ... $U = (\prod T(x_1, x_2)) \cdot D$").
- M. Reck, A. Zeilinger, H. J. Bernstein and P. Bertani, *Experimental realization of any discrete unitary operator*, Phys. Rev. Lett. 73 (1994), 58–61 (the factorization cited by Barenco et al.).
