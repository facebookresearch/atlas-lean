# Extremal values and multiplicativity of fidelity

Let $F$ be the root fidelity.

1. For all positive semidefinite $P, Q$: $F(P,Q) \ge 0$, and $F(P,Q) = 0$ if and only if $PQ = 0$ (orthogonal supports).
2. For density matrices $\rho,\sigma$: $F(\rho,\sigma) \le 1$, and $F(\rho,\sigma) = 1$ if and only if $\rho = \sigma$.
3. For positive semidefinite $P_1,Q_1 \in M_\iota(\mathbb{C})$ and $P_2,Q_2 \in M_\kappa(\mathbb{C})$: $F(P_1 \otimes P_2,\, Q_1 \otimes Q_2) = F(P_1,Q_1)\,F(P_2,Q_2)$.

## Proof sketch

$F(P,Q)=0$ means $\sqrt P\sqrt Q = 0$, which is equivalent to $PQ = 0$ by taking square roots on the supports. For density matrices, Uhlmann's theorem writes $F$ as the largest overlap of unit purifications, so $F \le 1$ by Cauchy-Schwarz, with equality only for equal purifications up to a local unitary, hence equal reduced states. For tensor products, the square root of a Kronecker product of positive matrices is the Kronecker product of the square roots, and singular values of a Kronecker product are the products of singular values.

## Depends on

- [Fidelity of positive semidefinite matrices](root-fidelity.md)

## Proof depends on

- [Fidelity of positive semidefinite matrices](root-fidelity.md)
- [Uhlmann's theorem](../uhlmann-s-theorem.md)

## Sources

- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
