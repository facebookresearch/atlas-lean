# A diagonal unitary is a product of two-level diagonal unitaries

Let $d$ be even and let $D = \operatorname{diag}(e^{i\varphi_1}, \dots, e^{i\varphi_d})$ be a diagonal unitary on
$\mathbb{C}^d$. Then $D = D_1 D_2 \cdots D_{d/2}$, where $D_j$ is the two-level unitary (a unitary that is [two-level](../../../LinearAlgebra/not-yet-classified/two-level/is-two-level.md))
acting on $\operatorname{span}(e_{2j-1}, e_{2j})$ by $\operatorname{diag}(e^{i\varphi_{2j-1}}, e^{i\varphi_{2j}})$ and as
the identity on the other basis vectors. The factors act on disjoint pairs and commute. For $d = 2^n$ there are
$2^{n-1}$ factors, and no global phase is left over, since $D$ carries all its phases.

## Depends on

- [Two-level matrix](../../../LinearAlgebra/not-yet-classified/two-level/is-two-level.md)

## Sources

- A. Barenco, C. H. Bennett, R. Cleve, D. P. DiVincenzo, N. Margolus, P. Shor, T. Sleator, J. Smolin and H. Weinfurter, *Elementary gates for quantum computation*, Phys. Rev. A 52 (1995), 3457–3467, arXiv:quant-ph/9503016, Section 8 ("$D$ is a diagonal matrix involving only phase factors, and thus can also be thought of as a product of $2^{n-1}$ matrices which perform rotations in two-dimensional subspaces").
