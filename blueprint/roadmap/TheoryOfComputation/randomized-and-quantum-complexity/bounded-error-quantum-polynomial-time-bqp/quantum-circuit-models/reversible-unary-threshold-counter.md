# A reversible unary threshold counter

For $k$ input bits and a threshold $T$, there is a classical reversible circuit of NOT, CNOT and Toffoli gates with $O(kT)$ gates and $O(kT)$ ancilla qubits initialized to $0$ that computes, for each $i<T$, a level bit indicating whether more than $i$ of the input bits are $1$, leaving the inputs unchanged.

## Proof sketch

Stage $s$ introduces $T$ fresh level qubits; reading input bit $b$, the new level $i$ is set to old level $i$ OR (old level $i-1$ AND $b$), which is computed into a fresh zero qubit with a constant number of Toffoli and CNOT gates.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)
- [Reversible simulation of classical circuits](../reversible-simulation-of-classical-circuits.md)

## Sources

- Ronald de Wolf, "Quantum Computing: Lecture Notes", 2019.
