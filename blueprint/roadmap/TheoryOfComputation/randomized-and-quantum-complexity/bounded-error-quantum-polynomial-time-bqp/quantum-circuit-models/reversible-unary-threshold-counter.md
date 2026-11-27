# A reversible unary threshold counter

For $k$ input bits $z$ and a threshold $T$, let $f(z)\in\{0,1\}^T$ list, for each $i<T$, the level bit indicating whether more than $i$ of the input bits are $1$. There is a classical reversible circuit of Toffoli gates (with NOT and CNOT), using ancilla bits initialized to $0$, that maps $|z\rangle|0\rangle\mapsto|z\rangle|f(z)\rangle$, leaving the inputs unchanged; this is the reversible implementation of the classical computation of $f$.

## Proof sketch

Toffoli gates with auxiliary wires fixed to constants implement AND and NOT, so any classical circuit for $f$ is implemented reversibly; uncomputing the intermediate wires returns the ancillas to $0$.

Derived explicit construction (not stated in the cited sources): with $O(kT)$ gates and $O(kT)$ ancilla bits. Stage $s$ introduces $T$ fresh level bits; reading input bit $b$, the new level $i$ is set to old level $i$ OR (old level $i-1$ AND $b$), which is computed into a fresh zero bit with a constant number of Toffoli and CNOT gates.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)
- [Reversible simulation of classical circuits](../reversible-simulation-of-classical-circuits.md)

## Sources

- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415 (version 6), Section 2.2 (the Toffoli gate "is complete for classical reversible computation: any classical computation can be implemented by a circuit of Toffoli gates") and Section 2.3 (a Toffoli circuit $U$ with $|z\rangle|0\rangle \mapsto |z\rangle|f(z)\rangle$).
- Charles H. Bennett, "Logical Reversibility of Computation", IBM Journal of Research and Development 17(6), 525–532, 1973.
- Michael A. Nielsen and Isaac L. Chuang, "Quantum Computation and Quantum Information", Cambridge University Press, 2000, Section 3.2.5 (reversible computation).
