# Acceptance gaps of quantum circuits as tensor-network contractions

For a Hadamard–Toffoli circuit $C$ on $m$ qubits started in $|0^m\rangle$ and a set $S$ of measured qubits, let $\mathrm{gap}_S(C)$ be $2^{h}$ times the probability that all qubits in $S$ read $1$, where $h$ is the number of Hadamard gates. That probability is the value of the rank-0 tensor obtained by contracting the Markov–Shi tensor network of $C$ with input $0^m$ and the measurement scenario "all qubits of $S$ read $1$": one tensor for the input density operator, one for the superoperator of each gate, and one for the measurement, joined along the wires of $C$. This network has size linear in the number of gates and is computed from the gate list in polynomial time; hence $\mathrm{gap}_S(C)$ is $2^{h}$ times its contraction.

## Proof sketch

Contracting the input wires of the gate superoperators in order gives the tensor of the state after each gate, and contracting the remaining wires with the measurement tensor gives the probability that the scenario is realized.

Derived integer form (not stated in the cited sources): by the path-sum expansion each amplitude is $2^{-h/2}$ times a signed count of computational paths, so $\mathrm{gap}_S(C)$ is a sum over pairs of paths (one for the amplitude, one for its conjugate) agreeing at the end on $S$. Equivalently, scaling each Hadamard tensor by $2$ turns the network into one built from $C$ and a mirrored copy of $C$ whose entries are $0$ and $\pm1$, and whose contraction is exactly the integer $\mathrm{gap}_S(C)$.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)

## Proof depends on

- [Path-sum expansion of quantum circuit amplitudes](../../path-sum-expansion-of-quantum-circuit-amplitudes.md)

## Sources

- Igor L. Markov and Yaoyun Shi, "Simulating Quantum Computation by Contracting Tensor Networks", SIAM Journal on Computing 38(3), 963–981, 2008, numbering of arXiv:quant-ph/0511069, Proposition 3.5 (contracting $N(C; x, \tau)$ gives the probability that $\tau$ is realized on $C(\rho_x)$) and Proposition 3.6 with its proof (the network of a size-$T$ circuit has size $\Theta(T)$).
- Christopher M. Dawson, Henry L. Haselgrove, Andrew P. Hines, Duncan Mortimer, Michael A. Nielsen and Tobias J. Osborne, "Quantum Computing and Polynomial Equations over the Finite Field Z_2", Quantum Information and Computation 5(2), 102–112, 2005 (path sums for Hadamard–Toffoli circuits).
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
- Scott Aaronson, "Quantum Computing, Postselection, and Probabilistic Polynomial-Time", Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences 461(2063), 3473–3482, 2005.
