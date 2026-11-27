# The normalizer of a stabilizer group is its centralizer

Let $S$ be a stabilizer group: an abelian subgroup of the $n$-qubit Pauli group $\mathcal{P}_n$ with $-I \notin S$.
For $A \in \mathcal{P}_n$ the following are equivalent:

1. $A S A^{-1} = S$, that is, $A$ lies in the normalizer $N(S)$ of $S$ in $\mathcal{P}_n$;
2. $A$ commutes with every element of $S$, that is, $A$ lies in the centralizer of $S$ in $\mathcal{P}_n$.

So $N(S)$ equals the centralizer; it contains $S$ as a normal subgroup.

Proof: for $M \in S$, $A M A^{-1} = \pm M$ because Pauli operators
[commute or anticommute](pauli-operators-commute-iff-symplectic-product-vanishes.md). If $A M A^{-1} = -M$ were in
$S$, then $-I = (-M) M^{-1} \in S$, which is excluded. Hence $A M A^{-1} \in S$ exactly when $A$ commutes with $M$.

## Depends on

- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)
- [Stabilizer groups and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](pauli-operators-commute-iff-symplectic-product-vanishes.md)

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.2, equation (3.6).
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 2.3, the paragraph before Theorem 5.
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.9.2 ("the normalizer (or centralizer) group $N(S)$").
