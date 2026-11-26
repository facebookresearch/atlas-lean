# NP ⊆ MA ⊆ QMA ⊆ PP

$\mathsf{NP}\subseteq\mathsf{MA}\subseteq\mathsf{QMA}$ and $\mathsf{QMA}\subseteq\mathsf{PP}$, where $\mathsf{QMA}$ uses polynomial-size quantum verifiers over a fixed universal gate set receiving a polynomial-size quantum witness, with completeness $2/3$ and soundness $1/3$. Also $\mathsf{BPP}\subseteq\mathsf{BQP}$.

## Proof sketch

Classical witnesses and coins are special quantum states and gates. For $\mathsf{QMA}\subseteq\mathsf{PP}$: after strong (witness-preserving) amplification, the maximum acceptance probability is the top eigenvalue of a $2^{p}\times2^{p}$ matrix whose trace is a $\mathsf{GapP}$ function divided by a power of two; the trace separates the two cases.

## Depends on

- [QMA for promise problems](../../randomized-and-quantum-complexity/local-hamiltonian-problem/qmapromise.md)
- [The class MA (Merlin–Arthur)](../../complexity-classes/time-and-space-complexity-classes/ma.md)
- [Probabilistic polynomial time with unbounded error](../../complexity-classes/time-and-space-complexity-classes/pp.md)

## Proof depends on

- [Closure properties of GapP](gapp-closure.md)
- [QMA error reduction by parallel repetition](../../randomized-and-quantum-complexity/qma-error-reduction-by-parallel-repetition.md)

## Sources

- Chris Marriott and John Watrous, "Quantum Arthur–Merlin Games", Computational Complexity 14(2), arXiv:cs/0506068, 2005.
- A. Yu. Kitaev, A. H. Shen and M. N. Vyalyi, "Classical and Quantum Computation", American Mathematical Society, 2002.
- John Watrous, "Quantum Computational Complexity", arXiv:0804.3401, 2008.
