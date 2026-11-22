# Acceptance probability of a quantum state

For a state vector $\psi$ on $N$ qubits, given
by its amplitudes $\psi(s) \in \mathbb{C}$ at the basis states $s \in \{0, \dots, 2^N - 1\}$, the
acceptance probability is the sum of $|\psi(s)|^2$ over the basis states $s$ whose qubit $0$ (the
output qubit, the least significant bit of $s$) equals $1$. By the Born rule, for a unit vector
$\psi$ this is the probability that measuring the output qubit gives $1$.

## Sources

- M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press, 2000, Chapter 2 (Born rule, measurement).
