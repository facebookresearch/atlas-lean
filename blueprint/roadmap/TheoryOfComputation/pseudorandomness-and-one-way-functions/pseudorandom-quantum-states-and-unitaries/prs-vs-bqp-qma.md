# Pseudorandom states can exist even if BQP = QMA

There is a quantum oracle relative to which $\mathsf{BQP}=\mathsf{QMA}$ yet pseudorandom state generators (and pseudorandom unitaries) exist. Conversely, pseudorandom states do not exist if $\mathsf{BQP}=\mathsf{PP}$ (relative to all oracles), so some complexity assumption is necessary. Since $\mathsf{NP}\subseteq\mathsf{QMA}=\mathsf{BQP}$ relative to this oracle, every one-way function candidate can be inverted in quantum polynomial time relative to it, so this shows that PRS, and the primitives built from them, may exist in worlds without classical cryptography.

## Proof sketch

The oracle is a family of Haar-random unitaries (giving PRS) together with a $\mathsf{QMA}$-solving oracle; a $\mathsf{QMA}$ verifier with classical inputs cannot break PRS because breaking requires processing quantum copies, and this distinction is made rigorous by concentration of measure for Haar-random unitaries. For the converse, a $\mathsf{PP}$ oracle can estimate, given the classical description of the generator, the acceptance probability of an optimal distinguisher via postselection over keys, and a quantum algorithm with this oracle breaks the PRS.

## Depends on

- [Pseudorandom quantum state generators](pseudorandom-quantum-states.md)
- [QMA for promise problems](../../randomized-and-quantum-complexity/local-hamiltonian-problem/qmapromise.md)
- [Pseudorandom unitaries](pseudorandom-unitaries.md)

## Proof depends on

- [BQP is contained in PP](../../randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/bqp-subset-pp.md)

## Sources

- William Kretschmer, "Quantum Pseudorandomness and Classical Complexity", TQC (2021), arXiv:2103.09320.
