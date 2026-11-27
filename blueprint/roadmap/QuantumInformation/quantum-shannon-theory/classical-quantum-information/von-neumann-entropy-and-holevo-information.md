# Von Neumann entropy and Holevo information

The *von Neumann entropy* of a density matrix $\rho$ on $\mathbb{C}^\iota$ is $S(\rho) = -\operatorname{Tr}(\rho\log_2\rho) = -\sum_i\lambda_i\log_2\lambda_i$ in bits, where $\lambda_i$ are the eigenvalues of $\rho$ and $0\log 0 = 0$; it is the Shannon entropy of the spectrum. For a finite ensemble given by a distribution $p$ on $X$ and density matrices $\rho_x$, the *Holevo information* is

$$
\chi(p,\rho) = S\Big(\sum_x p(x)\rho_x\Big) - \sum_x p(x)\,S(\rho_x).
$$

## Depends on

- [Density matrices, pure states and reduced states](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Sources

- A. S. Holevo, "Bounds for the quantity of information transmitted by a quantum communication channel", Problems of Information Transmission 9:177-183, 1973.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
