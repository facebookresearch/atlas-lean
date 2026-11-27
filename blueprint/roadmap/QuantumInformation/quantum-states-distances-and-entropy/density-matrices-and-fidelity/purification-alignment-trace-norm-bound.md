# Aligning purifications with error bounded by the trace distance of the reductions

Let $\psi,\varphi \in \mathbb{C}^\iota\otimes\mathbb{C}^\kappa$ be unit vectors with reduced states $\rho_\psi = \operatorname{Tr}_\kappa|\psi\rangle\langle\psi|$ and $\rho_\varphi = \operatorname{Tr}_\kappa|\varphi\rangle\langle\varphi|$. There is a unitary $U$ on $\mathbb{C}^\kappa$ such that

$$
\|(I \otimes U)\psi - \varphi\|^2 \le \|\rho_\psi - \rho_\varphi\|_1 .
$$

## Proof sketch

Take the unitary of the local-unitary form of Uhlmann's theorem, for which the squared error equals $2(1 - F(\rho_\psi,\rho_\varphi))$. The lower Fuchs-van de Graaf inequality $1 - F \le \tfrac12\|\rho_\psi - \rho_\varphi\|_1$ finishes the bound.

## Depends on

- [Trace norm and trace distance](trace-norm-and-trace-distance.md)
- [Partial trace over the second factor](../../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-right.md)

## Proof depends on

- [Uhlmann's theorem in local-unitary form for arbitrary bipartite vectors](uhlmann-local-unitary-attainment.md)
- [Fuchs–van de Graaf inequalities](../fuchsvan-de-graaf-inequalities.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
