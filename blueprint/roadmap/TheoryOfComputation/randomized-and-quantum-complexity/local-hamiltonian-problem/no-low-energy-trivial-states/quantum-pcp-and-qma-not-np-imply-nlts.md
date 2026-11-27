# The quantum PCP conjecture together with NP different from QMA implies NLTS

Assume the quantum PCP conjecture: deciding whether a local Hamiltonian has ground energy at most $a$ or at least $a + \varepsilon m$ is QMA-hard for some constant $\varepsilon > 0$. If moreover $\mathrm{QMA} \ne \mathrm{NP}$, then there are local Hamiltonian families with no trivial states of relative energy below $\varepsilon/2$. Hence the NLTS theorem is a necessary consequence of the quantum PCP conjecture (under $\mathrm{NP} \ne \mathrm{QMA}$).

## Proof sketch

If every hard instance had a constant-depth state of relative energy $\varepsilon/2$, its circuit would be a classical polynomial-size NP witness: the energy of a constant-depth state under each local term is computable classically by restricting to the bounded light cone. This would place the gapped local Hamiltonian problem in NP, contradicting QMA-hardness under $\mathrm{QMA} \ne \mathrm{NP}$.

## Depends on

- [The NLTS property and the Freedman-Hastings conjecture](no-low-energy-trivial-states-property.md)
- [Quantum PCP conjecture](../quantum-pcp-conjecture.md)

## Proof depends on

- [The 2-local Hamiltonian problem is QMA-complete](../local-hamiltonian-qma-complete.md)

## Sources

- Dorit Aharonov, Itai Arad, Thomas Vidick, "The quantum PCP conjecture", ACM SIGACT News 44(2) (2013); arXiv:1309.7495.
- Michael H. Freedman, Matthew B. Hastings, "Quantum systems on non-k-hyperfinite complexes: a generalization of classical statistical mechanics on expander graphs", Quantum Information and Computation 14 (2014); arXiv:1301.1363.
