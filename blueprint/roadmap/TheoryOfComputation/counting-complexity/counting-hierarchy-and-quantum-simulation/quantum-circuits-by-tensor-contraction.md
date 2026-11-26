# Quantum circuits with T gates are classically simulable in time 2^{O(T/√log T)}

For a quantum circuit of $T$ gates over $\{\mathrm{H},\mathrm{NOT},\mathrm{CNOT},\mathrm{Toffoli}\}$ with $h$ Hadamard gates, the probability that measuring a set $S$ of qubits yields all ones equals $\mathrm{gap}_S/2^{h}$ for an integer path-sum $\mathrm{gap}_S$. This integer can be computed exactly by contracting the associated path-sum tensor network in deterministic time $2^{O(T/\sqrt{\log T})}$ and polynomial space. Consequently quantum time $T$ (with this gate set and bounded error) is contained in $\mathsf{DTIME}\bigl(2^{O(T/\sqrt{\log T})}\bigr)$.

## Proof sketch

Write the amplitude as a sum over Hadamard path variables of signs determined by the classical reversible gates; this is the value of a factored tensor network with one tensor per gate. Grouping gates into blocks of $\Theta(\sqrt{\log T})$ and contracting block by block keeps the boundary sizes $O(T/\sqrt{\log T})$.

## Depends on

- [BQP](../../complexity-classes/time-and-space-complexity-classes/bqp.md)
- [Merging vertices of a factored tensor network](../../fine-grained-complexity/tensor-network-contraction/contraction-of-factored-tensor-networks/merge.md)

## Proof depends on

- [Model counting by tensor contraction in time 2^{O(m/√log n)}](../../fine-grained-complexity/subexponential-model-counting/tensor-contraction-model-counting.md)
- [BQP is contained in PP](../../randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/bqp-subset-pp.md)

## Sources

- OpenAI, "The Exponential Time Hypothesis is False", Manuscript, 2026, Theorem D.1.
- Stephen Fenner, Frederic Green, Steven Homer and Randall Pruim, "Determining Acceptance Possibility for a Quantum Computation is Hard for the Polynomial Hierarchy", Proceedings of the Royal Society of London. Series A: Mathematical, Physical and Engineering Sciences 455(1991), arXiv:quant-ph/9812056, 1999.
