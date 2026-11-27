# Trace norm and trace distance

For a complex matrix $X$ (possibly rectangular) the *trace norm* is $\|X\|_1 = \operatorname{Tr}\sqrt{X^*X}$, the sum of the singular values of $X$. It is a norm, it is invariant under left multiplication by isometries and under conjugation $X \mapsto VXV^*$ by isometries, and for square $X$ it has the variational form $\|X\|_1 = \max_{U} \operatorname{Re}\operatorname{Tr}(UX)$ over unitaries $U$. For Hermitian $X$, $\|X\|_1 = \sum_i |\lambda_i(X)|$.

The *trace distance* of two density matrices $\rho, \sigma$ on $\mathbb{C}^\iota$ is $T(\rho,\sigma) = \tfrac12\|\rho - \sigma\|_1 \in [0,1]$.

## Depends on

- [Density matrices, pure states and reduced states](density-matrices-and-reduced-states.md)
- [Polar decomposition of a complex square matrix](../../../LinearAlgebra/matrix-decompositions/polar-decomposition/polar-decomposition-theorem/exists-unitary-group-pos-semidef.md)

## Sources

- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
