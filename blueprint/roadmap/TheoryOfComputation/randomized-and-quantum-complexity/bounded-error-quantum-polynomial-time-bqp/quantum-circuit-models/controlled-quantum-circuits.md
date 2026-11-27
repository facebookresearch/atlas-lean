# Controlled circuits and self-inverse gate codes

A circuit whose gates never act on qubit $j$ has zero matrix entries between basis strings that differ at $j$, so it commutes with the projections onto $|0\rangle$ and $|1\rangle$ of qubit $j$. Every Hadamard, NOT, CNOT and Toffoli gate is its own inverse, so running a gate list backwards undoes it. A circuit $C$ equals *$D$ controlled by qubit $c$* if it acts as $D$ on the subspace where $c$ is $1$ and as the identity where $c$ is $0$; controlled versions of Hadamard–Toffoli circuits are obtained gate by gate (adding $c$ as a control).

## Proof sketch

Each gate is a tensor product with the identity on untouched qubits; involutivity is a direct matrix computation.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)

## Sources

- Michael A. Nielsen and Isaac L. Chuang, "Quantum Computation and Quantum Information", Cambridge University Press, 2000, Sections 4.2–4.3.
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
