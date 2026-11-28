# Translation-invariant matrix product operators with open boundary conditions

A translation-invariant matrix product operator with open boundary conditions assigns to every chain length $n$ an operator on $(\mathbb{C}^d)^{\otimes n}$ built from one fixed four-index tensor, repeated at every site and closed by two boundary vectors.

**Definition.** An instance consists of MPO tensors $M = \bigl(M^{(\alpha,\beta)}_{i,j}\bigr)$ with $\alpha, \beta \in [d]$ and $i, j \in [D]$, and boundary vectors $\lvert L\rangle, \lvert R\rangle \in \mathbb{C}^D$. The number $d$ is the *physical dimension* and $D$ the *bond dimension*. Writing $M_{i,j}$ for the $d \times d$ matrix with entries $M^{(\alpha,\beta)}_{i,j}$, the operator for system size $n \geq 1$ is

$$
\rho(L, M, R, n) = \sum_{j \in [D]^{n+1}} L_{j_1}\, M_{j_1, j_2} \otimes M_{j_2, j_3} \otimes \cdots \otimes M_{j_n, j_{n+1}}\, R_{j_{n+1}},
$$

an operator on $(\mathbb{C}^d)^{\otimes n}$. An operator is called *positive* when it is positive semidefinite. Decision problems take the entries of $M$, $\lvert L\rangle$ and $\lvert R\rangle$ as input, so they restrict them to rational numbers.

## Depends on

None.

## Proof depends on

None.

## Remarks

The same tensor sits at every site. For a fixed $n$ the operator is an explicit finite matrix, so positivity for one system size is a finite computation; the problems become hard when positivity is asked for all system sizes at once. When every $M_{i,j}$ is diagonal, $\rho(L, M, R, n)$ is diagonal in the product basis, with entry $L^{\mathsf{T}} A^{(w_1)} \cdots A^{(w_n)} R$ at $\lvert w_1 \cdots w_n\rangle$ (the coordinates of $\lvert L\rangle$ enter without complex conjugation, so for real $\lvert L\rangle$ this is $\langle L \rvert A^{(w_1)} \cdots A^{(w_n)} \lvert R\rangle$), where $A^{(\alpha)}$ is the $D \times D$ matrix with entries $M^{(\alpha,\alpha)}_{i,j}$.

## Sources

- M. Kliesch, D. Gross and J. Eisert, "Matrix-product operators and states: NP-hardness and undecidability", *Physical Review Letters* 113(16), 160503, 2014, doi:[10.1103/PhysRevLett.113.160503](https://doi.org/10.1103/PhysRevLett.113.160503). Numbering of the version read, arXiv:1404.4466v2: Definition 1 (open boundary conditions) and Problems 2 and 3 (rational instances).
