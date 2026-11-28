# Naimark dilation of a POVM

Let $(E_a)_{a\in A}$ be a POVM on $\mathbb{C}^\iota$ with finite outcome set $A$, fix $a_0\in A$, and let $J:\mathbb{C}^\iota\to\mathbb{C}^\iota\otimes\mathbb{C}^A$, $J\psi = \psi\otimes|a_0\rangle$. There is a projective measurement $(P_a)_{a\in A}$ on $\mathbb{C}^\iota\otimes\mathbb{C}^A$ with $J^*P_aJ = E_a$ for every $a$. Consequently measuring $\psi$ with $E$ and measuring $\psi\otimes|a_0\rangle$ with $P$ give the same outcome distribution.

## Proof sketch

The map $V\psi = \sum_a \sqrt{E_a}\,\psi\otimes|a\rangle$ is an isometry because $\sum_a E_a = I$. Its columns extend to an orthonormal basis, giving a unitary $U$ on $\mathbb{C}^\iota\otimes\mathbb{C}^A$ with $UJ = V$. Put $P_a = U^*(I\otimes|a\rangle\langle a|)U$; these are orthogonal projections summing to $I$, and $J^*P_aJ = V^*(I\otimes|a\rangle\langle a|)V = E_a$.

## Depends on

- [Positive-operator-valued measurements and the Born rule](povm-and-born-rule.md)

## Sources

- M. A. Naimark, "Spectral functions of a symmetric operator", Izvestiya Akademii Nauk SSSR, Seriya Matematicheskaya 4:277-318, 1940.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
