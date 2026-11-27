# Bounded-degree local Hamiltonian families and relative energy

A *$(k, \ell)$-local Hamiltonian* on $n$ qubits is $H = \sum_{j=1}^{m} h_j$ with $0 \preceq h_j \preceq I$, each $h_j$ acting nontrivially on at most $k$ qubits, and each qubit acted on by at most $\ell$ terms. For a state $\rho$, its *energy* is $\mathrm{Tr}(H\rho)$; $\rho$ has *relative energy* $\varepsilon$ if $\mathrm{Tr}(H\rho) \le \lambda_{\min}(H) + \varepsilon m$. The Hamiltonian is *frustration-free* if $\lambda_{\min}(H) = 0$ and *commuting* if $[h_j, h_{j'}] = 0$ for all $j, j'$.

## Depends on

- [Hamiltonian of a list of 2-local terms](../hamiltonian.md)
- [Ground energy of a Hermitian matrix](../ground-energy.md)

## Sources

- Anurag Anshu, Nikolas P. Breuckmann, Chinmay Nirkhe, "NLTS Hamiltonians from good quantum codes", STOC (2023); arXiv:2206.13228.
- Dorit Aharonov, Itai Arad, Thomas Vidick, "The quantum PCP conjecture", ACM SIGACT News 44(2) (2013); arXiv:1309.7495.
