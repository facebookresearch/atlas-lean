# Pauli operators are orthogonal for the trace inner product

For $k \ge 0$ and $a, b \in \mathbb{F}_2^k$ let $\sigma_{a, b} = i^{|a \wedge b|} X^a Z^b$ be the Hermitian Pauli operator on $k$
qubits, the tensor product of the factors $I, X, Z, Y$ for $(a_j, b_j) = (0,0), (1,0), (0,1), (1,1)$. Then

$$\operatorname{Tr}(\sigma_{a, b}\, \sigma_{a', b'}) = \begin{cases} 2^k & \text{if } (a, b) = (a', b'), \\ 0 & \text{otherwise.} \end{cases}$$

So the $4^k$ Pauli products $\{I, X, Y, Z\}^{\otimes k}$ are orthogonal for the Hilbert–Schmidt inner product
$\langle A, B \rangle = \operatorname{Tr}(A^{*} B)$; together with the
[Pauli expansion](pauli-expansion-of-a-matrix.md) they form an orthogonal basis of the $2^k \times 2^k$ complex matrices.
This is why correcting the Pauli errors of weight at most $t$ corrects every error supported on at most $t$ qubits.

## Related topics

- [Every matrix is a combination of Pauli operators](pauli-expansion-of-a-matrix.md): the expansion in this basis

## Sources

- A. Ketkar, A. Klappenecker, S. Kumar and P. K. Sarvepalli, *Nonbinary stabilizer codes over finite fields*, IEEE Trans. Inform. Theory 52 (2006), 4892–4914, arXiv:quant-ph/0508070, Section II (the nice error basis: $\operatorname{Tr}(A^\dagger B) = 0$ for distinct elements), Lemma 1 and Corollary 4.
- C. Dankert, R. Cleve, J. Emerson and E. Livine, *Exact and approximate unitary 2-designs and their application to fidelity estimation*, Phys. Rev. A 80 (2009), 012304, arXiv:quant-ph/0606161, the expansion $A = \sum_a \alpha_a P_a$ before equation (10).
- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.2 (the Pauli operators "are a basis for the vector space of $2 \times 2$ matrices").
