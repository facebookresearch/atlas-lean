# Uhlmann's theorem in local-unitary form for arbitrary bipartite vectors

Let $\iota,\kappa$ be finite and let $\psi,\varphi \in \mathbb{C}^\iota \otimes \mathbb{C}^\kappa$ be arbitrary vectors (not necessarily normalized; the local dimensions need not be equal and the reduced states may be singular). Put $\rho_\psi = \operatorname{Tr}_\kappa |\psi\rangle\langle\psi|$ and $\rho_\varphi = \operatorname{Tr}_\kappa|\varphi\rangle\langle\varphi|$. Then:

1. For every unitary $V$ on $\mathbb{C}^\kappa$, $\operatorname{Re}\langle (I\otimes V)\psi, \varphi\rangle \le F(\rho_\psi, \rho_\varphi)$.
2. There is a unitary $U$ on $\mathbb{C}^\kappa$ with $\langle (I\otimes U)\psi, \varphi\rangle = F(\rho_\psi,\rho_\varphi)$, a nonnegative real number.
3. If $\psi,\varphi$ are unit vectors, this $U$ satisfies $\|(I\otimes U)\psi - \varphi\|^2 = 2\big(1 - F(\rho_\psi,\rho_\varphi)\big)$.

## Proof sketch

Write $\psi$ and $\varphi$ through their $\iota\times\kappa$ coefficient matrices $A, B$, so that $\rho_\psi = AA^*$, $\rho_\varphi = BB^*$, a local unitary acts by $A \mapsto AU^{\mathsf T}$, and the inner product is the trace pairing of coefficient matrices. Optimizing over unitaries is the variational formula for the trace norm, which gives $\max_U \operatorname{Re}\langle (I\otimes U)\psi,\varphi\rangle = \|A^*B\|_1$, attained at the unitary factor of a polar decomposition. Finally $\|A^*B\|_1 = F(AA^*, BB^*)$, which identifies the optimum with the root fidelity; part 3 expands the squared norm.

## Depends on

- [Fidelity of positive semidefinite matrices](root-fidelity.md)
- [Partial trace over the second factor](../../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-right.md)

## Proof depends on

- [Uhlmann's theorem](../uhlmann-s-theorem.md)
- [Purification and unitary equivalence of purifications](../../quantum-foundations/purification-and-unitary-equivalence-of-purifications.md)
- [Polar decomposition of a complex square matrix](../../../LinearAlgebra/matrix-decompositions/polar-decomposition/polar-decomposition-theorem/exists-unitary-group-pos-semidef.md)
- [Trace norm and trace distance](trace-norm-and-trace-distance.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
