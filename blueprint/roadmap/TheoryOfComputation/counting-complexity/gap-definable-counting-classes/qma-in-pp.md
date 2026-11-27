# NP ⊆ MA ⊆ QMA ⊆ PP

$\mathsf{NP}\subseteq\mathsf{MA}\subseteq\mathsf{QMA}$, where $\mathsf{QMA}$ uses polynomial-size quantum verifiers over a fixed universal gate set receiving a polynomial-size quantum witness, with completeness $2/3$ and soundness $1/3$. Together with $\mathsf{QMA}\subseteq\mathsf{PP}$ this gives the chain $\mathsf{NP}\subseteq\mathsf{MA}\subseteq\mathsf{QMA}\subseteq\mathsf{PP}$.

## Proof sketch

An $\mathsf{NP}$ verifier is a Merlin–Arthur verifier that ignores its coins. Classical witnesses are computational-basis states, and a randomized classical verifier is simulated by a quantum circuit exactly as in $\mathsf{BPP}\subseteq\mathsf{BQP}$, so an $\mathsf{MA}$ protocol becomes a $\mathsf{QMA}$ protocol whose verifier first measures the witness in the computational basis; a quantum witness then acts as a mixture of classical witnesses, so soundness is kept.

## Depends on

- [QMA for promise problems](../../randomized-and-quantum-complexity/local-hamiltonian-problem/qmapromise.md)
- [The class MA (Merlin–Arthur)](../../complexity-classes/time-and-space-complexity-classes/ma.md)
- [Probabilistic polynomial time with unbounded error](../../complexity-classes/time-and-space-complexity-classes/pp.md)
- [QMA is contained in PP via in-place amplification](../../randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/witness-preserving-amplification-and-black-box-groups/qma-is-contained-in-pp.md)

## Proof depends on

- [BPP is contained in BQP](../../randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/bpp-subset-bqp.md)

## Sources

- Chris Marriott and John Watrous, "Quantum Arthur–Merlin Games", Computational Complexity 14(2), arXiv:cs/0506068, 2005.
- A. Yu. Kitaev, A. H. Shen and M. N. Vyalyi, "Classical and Quantum Computation", American Mathematical Society, 2002.
- John Watrous, "Quantum Computational Complexity", arXiv:0804.3401, 2008.
