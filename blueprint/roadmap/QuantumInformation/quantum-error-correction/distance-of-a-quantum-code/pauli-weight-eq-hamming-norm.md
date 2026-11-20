# Pauli weight as a Hamming norm

The [weight](pauli-weight.md) of the Pauli operator $X^a Z^b$ equals the Hamming norm of the
vector $i \mapsto (a_i, b_i)$ in $(\mathbb{F}_2 \times \mathbb{F}_2)^n$, that is the number of
indices with $(a_i, b_i) \ne (0, 0)$. The vector $(a, b) \in \mathbb{F}_2^{2n}$ is the symplectic
representation of the Pauli operator up to phase used in Preskill's Section 7.9.2, so the quantum
weight is the classical Hamming weight over the four-letter alphabet $\mathbb{F}_2^2$.

## Background

- [Bounds on code size](../../../InformationTheory/error-correcting-codes/bounds-on-code-size/README.md): classical codes measured with the same Hamming norm.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Sections 7.2 and 7.9.2, equation (7.126).
