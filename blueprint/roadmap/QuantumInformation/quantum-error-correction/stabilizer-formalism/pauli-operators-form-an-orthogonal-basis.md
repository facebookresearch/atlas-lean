# Pauli operators form an orthogonal basis of the matrices

The $4^n$ Pauli products $P_1 \otimes \cdots \otimes P_n$ with $P_j \in \{I, X, Y, Z\}$ are orthogonal for the
Hilbert–Schmidt inner product: $\operatorname{Tr}(P^{*} Q) = 2^n$ if $P = Q$ and $0$ otherwise. Hence they form a basis of
the space of complex $2^n \times 2^n$ matrices, and every matrix $A$ expands as

$$A = \sum_{P} \alpha_P\, P, \qquad \alpha_P = 2^{-n} \operatorname{Tr}(P A).$$

The one-qubit case, $\operatorname{Tr}(I) = 2$ and $\operatorname{Tr}(X) = \operatorname{Tr}(Y) = \operatorname{Tr}(Z) = 0$
together with the products $XY = iZ$, $YZ = iX$, $ZX = iY$, gives the general case by
$\operatorname{Tr}(A \otimes B) = \operatorname{Tr}(A) \operatorname{Tr}(B)$. This expansion is why correcting the Pauli
errors of weight at most $t$ corrects every error supported on at most $t$ qubits.

## Depends on

- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.2 (the Pauli operators "are a basis for the vector space of $2 \times 2$ matrices").
- A. Ketkar, A. Klappenecker, S. Kumar and P. K. Sarvepalli, *Nonbinary stabilizer codes over finite fields*, IEEE Trans. Inform. Theory 52 (2006), 4892–4914, arXiv:quant-ph/0508070, Section II (the nice error basis: $\operatorname{Tr}(A^\dagger B) = 0$ for distinct elements, so the error operators form a basis), Lemma 1 and Corollary 4.
- C. Dankert, R. Cleve, J. Emerson and E. Livine, *Exact and approximate unitary 2-designs and their application to fidelity estimation*, Phys. Rev. A 80 (2009), 012304, arXiv:quant-ph/0606161, the expansion $A = \sum_a \alpha_a P_a$ before equation (10).
