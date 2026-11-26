# Tsirelson's vector-to-observable realization

For $u,v\in\mathbb{R}^m$ and $k = \lceil m/2\rceil$, the Clifford observables satisfy $\operatorname{Tr}(\Gamma(u)\Gamma(v)) = 2^k\langle u,v\rangle$, and on the maximally entangled state $\Phi$ of two $k$-qubit registers

$$
\langle\Phi,\ (\Gamma(u)\otimes\Gamma(v)^{\mathsf T})\,\Phi\rangle = \langle u,v\rangle .
$$

Hence any correlation matrix $(\langle u_x,v_y\rangle)$ of real unit vectors in $\mathbb{R}^m$ is realized exactly by $\pm1$ observables on a maximally entangled state of local dimension $2^{\lceil m/2\rceil}$.

## Proof sketch

Anticommutation gives $\Gamma_i\Gamma_j+\Gamma_j\Gamma_i = 2\delta_{ij}I$, and each product $\Gamma_i\Gamma_j$ with $i\ne j$ is traceless, so $\operatorname{Tr}(\Gamma(u)\Gamma(v)) = 2^k\langle u,v\rangle$. The maximally entangled correlation formula $\langle\Phi,(A\otimes B^{\mathsf T})\Phi\rangle = \operatorname{Tr}(AB)/2^k$ converts the trace into the stated expectation.

## Depends on

- [Weyl-Brauer Clifford observables](weyl-brauer-clifford-observables.md)
- [Local correlations on the maximally entangled state and the transpose trick](maximally-entangled-correlations-transpose-trick.md)

## Proof depends on

- [Local correlations on the maximally entangled state and the transpose trick](maximally-entangled-correlations-transpose-trick.md)

## Sources

- B. S. Cirel'son, "Quantum generalizations of Bell's inequality", Letters in Mathematical Physics 4:93-100, 1980.
- R. Cleve, P. Hoyer, B. Toner and J. Watrous, "Consequences and limits of nonlocal strategies", Proceedings of the 19th IEEE Conference on Computational Complexity, 236-249, 2004.
