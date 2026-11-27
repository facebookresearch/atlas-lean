# Quantum-computable one-way functions without classical one-way functions

There is an oracle relative to which there exist one-way functions computable by quantum polynomial-time algorithms (with classical inputs and outputs, i.e., quantum-computable OWFs), yet no classically computable one-way functions exist. This separates quantum-computable one-way functions, which suffice for many primitives such as commitments, from classical one-way functions in a black-box sense.

## Proof sketch

Construct an oracle encoding a function that requires quantum advantage (a Forrelation-type task) to evaluate but whose inversion is hard, while adding a classical oracle making all classically computable functions invertible (an $\mathsf{NP}$-type oracle relative to which $\mathsf{P}=\mathsf{NP}$). Lower bounds for constant-depth circuits on the quantum-friendly task show the quantum function stays one-way.

## Depends on

- [One-way functions exist](../impagliazzo-s-five-worlds/owfexists.md)
- [Black-box constructions and oracle separations](../../../ComputerScience/cryptography/public-key/hardness-assumptions/black-box-constructions-and-oracle-separations.md)

## Proof depends on

- [Pseudorandom states in Algorithmica: a classical oracle with P = NP](prs-in-algorithmica.md)

## Sources

- William Kretschmer, Luowen Qian, Avishay Tal, "Quantum-Computable One-Way Functions without One-Way Functions", STOC (2025).
