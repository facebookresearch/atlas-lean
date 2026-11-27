# Weyl-Brauer Clifford observables

On $k$ qubits there are $2k$ pairwise anticommuting Hermitian involutions $\Gamma_1,\dots,\Gamma_{2k}$, obtained inductively by tensoring the single-qubit Pauli matrices: $\Gamma_{2j-1} = Z^{\otimes(j-1)}\otimes X\otimes I^{\otimes(k-j)}$ and $\Gamma_{2j} = Z^{\otimes(j-1)}\otimes Y\otimes I^{\otimes(k-j)}$, with $Y = \begin{pmatrix}0&-i\\ i&0\end{pmatrix}$. They satisfy $\Gamma_i^2 = I$ and $\Gamma_i\Gamma_j = -\Gamma_j\Gamma_i$ for $i\ne j$. For $u\in\mathbb{R}^m$ and $k = \lceil m/2\rceil$, the *Clifford observable* is $\Gamma(u) = \sum_{j\le m}u_j\Gamma_j$; it is Hermitian with $\Gamma(u)^2 = \|u\|^2I$, hence a $\pm1$ observable when $\|u\| = 1$.

## Depends on

- [Pauli strings and the Pauli group modulo $i$ as a Heisenberg group](pauli-group-modulo-i.md)

## Sources

- B. S. Cirel'son, "Quantum generalizations of Bell's inequality", Letters in Mathematical Physics 4:93-100, 1980.
- R. Cleve, P. Hoyer, B. Toner and J. Watrous, "Consequences and limits of nonlocal strategies", Proceedings of the 19th IEEE Conference on Computational Complexity, 236-249, 2004.
