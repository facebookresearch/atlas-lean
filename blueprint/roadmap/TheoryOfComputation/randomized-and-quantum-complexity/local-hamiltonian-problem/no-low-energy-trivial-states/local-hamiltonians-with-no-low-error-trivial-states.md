# Eldar-Harrow: local Hamiltonians with no low-error trivial states

There is a family of $O(1)$-local Hamiltonians on $n$ qubits and a constant $\varepsilon > 0$ such that every state that agrees with a ground state on all but $\varepsilon n$ qubits (that is, coincides with a ground state after tracing out and replacing at most $\varepsilon n$ qubits) has circuit depth $\Omega(\log n)$.

## Proof sketch

Apply Tillich-Zemor-type products of classical expander codes and a Hamiltonian derived from the code's checks on an expander. A state that is a ground state up to local errors has measurement distributions concentrated near codewords, whose span is far from any distribution produced by a shallow circuit because the latter are well spread; the quantum code structure prevents concentrating on a single codeword in both bases.

## Depends on

- [Bounded-degree local Hamiltonian families and relative energy](normalized-local-hamiltonian-families-and-relative-energy.md)
- [Circuit depth of a quantum state and trivial states](trivial-states-of-bounded-circuit-depth.md)

## Proof depends on

- [Output distributions of shallow circuits do not concentrate on two distant sets](shallow-circuits-produce-well-spread-distributions.md)
- [CSS code Hamiltonians of quantum LDPC codes](css-code-hamiltonians.md)

## Sources

- Lior Eldar, Aram W. Harrow, "Local Hamiltonians whose ground states are hard to approximate", FOCS (2017); arXiv:1510.02082.
