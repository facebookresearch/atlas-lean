# Translation-invariant matrix product operators

A translation-invariant matrix product operator assigns to every chain length $n$ an operator on $(\mathbb{C}^d)^{\otimes n}$ built from one fixed tensor, closed either by two boundary vectors (open boundary conditions) or by a trace (periodic boundary conditions). The question whether all of these operators are positive semidefinite is the positivity problem.

**Open boundary conditions.** An instance consists of MPO tensors $M = \bigl(M^{(\alpha,\beta)}_{i,j}\bigr)$ with $\alpha, \beta \in [d]$ and $i, j \in [D]$, and boundary vectors $\lvert L\rangle, \lvert R\rangle \in \mathbb{C}^D$. The number $d$ is the *physical dimension* and $D$ the *bond dimension*. Writing $M_{i,j}$ for the $d \times d$ matrix with entries $M^{(\alpha,\beta)}_{i,j}$, the operator for system size $n \geq 1$ is

$$
\rho(L, M, R, n) = \sum_{j \in [D]^{n+1}} L_{j_1}\, M_{j_1, j_2} \otimes M_{j_2, j_3} \otimes \cdots \otimes M_{j_n, j_{n+1}}\, R_{j_{n+1}},
$$

an operator on $(\mathbb{C}^d)^{\otimes n}$.

**Periodic boundary conditions, diagonal case.** Given $D \times D$ matrices $A_1, \dots, A_d$, the matrix product density operator for system size $L \geq 1$ is the diagonal operator

$$
\rho_A^L = \sum_{i_1, \dots, i_L = 1}^{d} \operatorname{tr}(A_{i_1} A_{i_2} \cdots A_{i_L})\, \lvert i_1 \cdots i_L\rangle\langle i_1 \cdots i_L\rvert
$$

on $(\mathbb{C}^d)^{\otimes L}$. It is positive semidefinite exactly when $\operatorname{tr}(A_{i_1} \cdots A_{i_L}) \geq 0$ for every word $i_1 \cdots i_L$.

An operator is called *positive* when it is positive semidefinite. Decision problems take the entries of the tensors as input, so they are restricted to rational, integer or algebraic entries.

## Depends on

None.

## Proof depends on

None.

## Expansion

Both families are translation invariant: the same tensor sits at every site. For a fixed $n$ the operator is an explicit finite matrix, so positivity for one system size is a finite computation. The problems become hard when positivity is asked for all system sizes at once. For open boundary conditions the bounded version, with $n$ part of the input, is NP-hard. A positive family in purification form, $\sigma_B^L = \operatorname{tr}_{\mathrm{env}} \lvert\Psi\rangle\langle\Psi\rvert$ for a translation-invariant matrix product state $\lvert\Psi\rangle$ with an environment at each site, is positive for every $L$ by construction.

## Sources

- M. Kliesch, D. Gross and J. Eisert, "Matrix-product operators and states: NP-hardness and undecidability", *Physical Review Letters* 113(16), 160503, 2014, doi:[10.1103/PhysRevLett.113.160503](https://doi.org/10.1103/PhysRevLett.113.160503). Numbering of the version read, arXiv:1404.4466v2: Definition 1 (open boundary conditions) and Theorem 4 (NP-hardness of the bounded problem).
- G. De las Cuevas, T. S. Cubitt, J. I. Cirac, M. M. Wolf and D. Pérez-García, "Fundamental limitations in the purifications of tensor networks", *Journal of Mathematical Physics* 57(7), 071902, 2016, doi:[10.1063/1.4954983](https://doi.org/10.1063/1.4954983). Numbering of the version read, arXiv:1512.05709v2: Equation (1) (the periodic diagonal case) and Equation (2) (purification form).
