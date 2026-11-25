# Polynomial-time languages are in BQP with error zero

Every language $L$ decided by a polynomial-time Turing machine is decided by a uniform family of polynomial-size quantum circuits in the encoded gate model of the BQP definition that outputs the correct answer with probability $1$ on every input; in particular $L \in \mathrm{BQP}$ with error $0$.

## Proof

A polynomial-time machine has uniform polynomial-size Boolean circuits computing $L$; their reversible simulation by Toffoli, CNOT and NOT gates, with clean ancillas, is again uniform and of polynomial size, and on a computational-basis input it maps the basis state of $x$ to a basis state carrying $L(x)$ in an output qubit, which a SWAP gate moves to the measured qubit. In the encoded gate model each Toffoli gate is replaced by its exact five-gate decomposition into 2-local Gaussian-rational gates, and NOT, CNOT and SWAP are themselves such gates, so the generated circuits stay uniform, of polynomial size and exactly equal to the reversible circuit. Measuring a basis state in the computational basis
returns its label with probability $1$.

## Depends on

- [BQP](../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Proof depends on

- [Reversible simulation of classical circuits](reversible-simulation-of-classical-circuits.md)
- [Exact Gaussian-rational Toffoli and multi-controlled NOT decompositions](exact-2-local-gaussian-rational-toffoli-and-multi-controlled.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Sections 2.1 and 13.2 (classical computation as reversible circuits; P and BQP). <https://arxiv.org/abs/1907.09415v6>
