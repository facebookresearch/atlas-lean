# Decomposition of a unitary into two-level unitaries

Let $d \ge 2$ and fix an orthonormal basis $e_1, \dots, e_d$ of $\mathbb{C}^d$. A *two-level unitary* is a unitary that acts
as the identity on all basis vectors except two, $e_j$ and $e_k$, and maps $\operatorname{span}(e_j, e_k)$ to itself. Every
unitary $U$ on $\mathbb{C}^d$ is a product of at most $d(d-1)/2$ two-level unitaries, one for each pair of basis vectors,
followed by a diagonal unitary $D$:

$$U = \Big( \prod_{j > k} T(j, k) \Big) \cdot D ,$$

where $T(j, k)$ acts on $\operatorname{span}(e_j, e_k)$. The factors are found column by column, as in Gaussian elimination
with Givens rotations: two-level unitaries zero the entries below the diagonal of the first column, which leaves a unit
complex number on the diagonal, and the procedure repeats on the remaining $(d - 1) \times (d - 1)$ block.

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 8 ("Reck et al. note that a formula exists for the decomposition of any unitary matrix into matrices only involving a U(2) operation acting in the space of pairs of states ... $U = (\prod T(x_1, x_2)) \cdot D$").
- M. Reck, A. Zeilinger, H. J. Bernstein and P. Bertani, *Experimental realization of any discrete unitary operator*, Phys. Rev. Lett. 73 (1994), 58–61 (the factorization cited by Barenco et al.).
