# Relative entropy bounds fidelity and purification alignment

Let $\rho,\sigma$ be density matrices.

1. If $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$ then $F(\rho,\sigma) \ge \exp\!\big(-D(\rho\|\sigma)/2\big)$.
2. Always $2\big(1 - F(\rho,\sigma)\big) \le D(\rho\,\|\,\sigma)$.
3. For unit vectors $\psi,\varphi\in\mathbb{C}^\iota\otimes\mathbb{C}^\kappa$ there is a unitary $U$ on $\mathbb{C}^\kappa$ with $\|(I\otimes U)\psi - \varphi\|^2 \le D(\rho_\psi\,\|\,\rho_\varphi)$, where $\rho_\psi,\rho_\varphi$ are the reductions to $\mathbb{C}^\iota$.

## Proof sketch

By the eigenbasis representation, $D$ is a classical KL divergence and $\operatorname{Tr}\sqrt\rho\sqrt\sigma$ is the Bhattacharyya coefficient; Jensen's inequality gives Bhattacharyya $\ge e^{-D/2}$, and $F \ge \operatorname{Tr}\sqrt\rho\sqrt\sigma$. Part 2 follows from $1 - e^{-x/2}\le x/2$. Part 3 combines part 2 with the identity $\|(I\otimes U)\psi-\varphi\|^2 = 2(1-F)$ for the Uhlmann unitary.

## Depends on

- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)
- [Fidelity of positive semidefinite matrices](../density-matrices-and-fidelity/root-fidelity.md)

## Proof depends on

- [Quantum relative entropy as a classical divergence in the two eigenbases](relative-entropy-eigenbasis-representation.md)
- [Uhlmann's theorem in local-unitary form for arbitrary bipartite vectors](../density-matrices-and-fidelity/uhlmann-local-unitary-attainment.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
