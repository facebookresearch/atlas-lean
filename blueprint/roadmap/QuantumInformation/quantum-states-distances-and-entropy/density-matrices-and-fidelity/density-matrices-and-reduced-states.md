# Density matrices, pure states and reduced states

Let $\iota$ and $\kappa$ be finite index sets. A *density matrix* (mixed state) on $\mathbb{C}^\iota$ is a matrix $\rho \in M_\iota(\mathbb{C})$ that is positive semidefinite and has $\operatorname{Tr}\rho = 1$. For a unit vector $\psi \in \mathbb{C}^\iota$ the *pure state* is the rank-one projector $|\psi\rangle\langle\psi|$ with entries $\psi_i \overline{\psi_j}$; it is a density matrix and does not change when $\psi$ is multiplied by a unimodular scalar.

For a bipartite system $\mathbb{C}^{\iota \times \kappa} \cong \mathbb{C}^\iota \otimes \mathbb{C}^\kappa$ and $\rho \in M_{\iota\times\kappa}(\mathbb{C})$, the *reduced states* are the partial traces
$(\operatorname{Tr}_B \rho)_{i i'} = \sum_{k} \rho_{(i,k),(i',k)}$ and $(\operatorname{Tr}_A\rho)_{kk'} = \sum_i \rho_{(i,k),(i,k')}$. Both partial traces preserve the trace and positive semidefiniteness, hence map density matrices to density matrices, and $\operatorname{Tr}_B(A \otimes B) = (\operatorname{Tr} B)\,A$. Conjugation $\rho \mapsto V\rho V^*$ by a possibly rectangular isometry $V$ ($V^*V = I$) maps density matrices to density matrices; a positive matrix $P \neq 0$ normalizes to the density matrix $P/\operatorname{Tr}P$.

## Depends on

- [Partial trace over the first factor](../../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-left.md)
- [Partial trace over the second factor](../../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-right.md)

## Sources

- R. de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
