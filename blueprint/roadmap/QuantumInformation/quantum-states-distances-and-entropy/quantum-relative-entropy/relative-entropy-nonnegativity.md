# Nonnegativity of quantum relative entropy for singular states (Klein's inequality)

For all density matrices $\rho,\sigma$ on $\mathbb{C}^\iota$, including singular ones, $D(\rho\,\|\,\sigma) \ge 0$ in $[0,+\infty]$ (natural logarithms); the value is $+\infty$ exactly when $\ker\sigma\not\subseteq\ker\rho$.

## Proof sketch

If the support test fails the value is $+\infty$. Otherwise the eigenbasis representation writes $D(\rho\|\sigma)$ as a classical Kullback-Leibler divergence between two probability distributions, which is nonnegative by Gibbs' inequality.

## Depends on

- [Density matrices, pure states and reduced states](../density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)
- [Klein's inequality for the matrix relative entropy](../../../LinearAlgebra/positive-definite-matrices/matrix-relative-entropy/re-trace-mul-cfc-log-sub-le.md)

## Proof depends on

- [Quantum relative entropy as a classical divergence in the two eigenbases](relative-entropy-eigenbasis-representation.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
