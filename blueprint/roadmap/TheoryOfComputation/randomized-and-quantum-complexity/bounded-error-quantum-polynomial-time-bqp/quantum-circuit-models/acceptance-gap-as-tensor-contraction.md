# Acceptance gaps of quantum circuits as tensor-network contractions

For a Hadamard–Toffoli circuit $C$ on $m$ qubits started in $|0^m\rangle$ and a set $S$ of measured qubits, let $\mathrm{gap}_S(C)$ be $2^{h}$ times the probability that all qubits in $S$ read $1$, where $h$ is the number of Hadamard gates. Then $\mathrm{gap}_S(C)$ is the contraction of an explicit tensor network with $0,\pm1$ entries built from $C$ and a mirrored copy of $C$ (a sum over pairs of computational paths), and this network is computable from the gate list in polynomial time.

## Proof sketch

By the path-sum expansion each amplitude is $2^{-h/2}$ times a signed count of computational paths; the probability is a sum over pairs of paths (one for the amplitude, one for its conjugate) agreeing at the end on $S$, which is the contraction of local gate tensors along wires.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)
- [Path-sum expansion of quantum circuit amplitudes](../../path-sum-expansion-of-quantum-circuit-amplitudes.md)

## Sources

- Christopher M. Dawson, Henry L. Haselgrove, Andrew P. Hines, Duncan Mortimer, Michael A. Nielsen and Tobias J. Osborne, "Quantum Computing and Polynomial Equations over the Finite Field Z_2", Quantum Information and Computation 5(2), 102–112, 2005 (path sums for Hadamard–Toffoli circuits).
- Igor L. Markov and Yaoyun Shi, "Simulating Quantum Computation by Contracting Tensor Networks", SIAM Journal on Computing 38(3), 963–981, 2008.
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
- Scott Aaronson, "Quantum Computing, Postselection, and Probabilistic Polynomial-Time", Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences 461(2063), 3473–3482, 2005.
