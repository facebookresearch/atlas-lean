# Inverse measurement channels for Clifford and Pauli shadows

For Clifford shadows $\mathcal{M}(X) = \frac{X + \mathrm{Tr}(X) I}{2^n + 1}$, so $\mathcal{M}^{-1}(Y) = (2^n + 1)Y - \mathrm{Tr}(Y) I$ and $\hat\rho = (2^n + 1)U^\dagger|b\rangle\langle b|U - I$. For Pauli shadows $\mathcal{M} = \bigotimes_{j=1}^n \mathcal{M}_1$ with $\mathcal{M}_1(X) = \frac{X + \mathrm{Tr}(X) I}{3}$, so

$$
\hat\rho = \bigotimes_{j=1}^{n} \left( 3\, U_j^\dagger |b_j\rangle\langle b_j| U_j - I \right).
$$

## Proof sketch

The Clifford group is a unitary $3$-design, in particular a $2$-design, so the twirl $\mathbb{E}_U U^\dagger \Phi(U \cdot U^\dagger) U$ of the dephasing channel is a depolarizing channel; matching the trace and the action on $|0\rangle\langle 0|$ gives the parameter $1/(2^n + 1)$. The single-qubit Clifford group gives the qubit case with $n = 1$, and the product ensemble factorizes.

## Depends on

- [Classical shadows from randomized measurements](randomized-measurement-classical-shadow.md)

## Sources

- Hsin-Yuan Huang, Richard Kueng, John Preskill, "Predicting many properties of a quantum system from very few measurements", Nature Physics 16 (2020); arXiv:2002.08953.
