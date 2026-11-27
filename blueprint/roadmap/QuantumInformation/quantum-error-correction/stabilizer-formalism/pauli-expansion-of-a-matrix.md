# Every matrix is a combination of Pauli operators

For $k \ge 0$ and $a, b \in \mathbb{F}_2^k$ let $\sigma_{a, b} = i^{|a \wedge b|} X^a Z^b$, with $X^a Z^b$ the [Pauli operator](../css-codes/pauli.md), be the Hermitian Pauli operator on $k$
qubits, where $|a \wedge b|$ is the number of positions $j$ with $a_j = b_j = 1$. Every complex $2^k \times 2^k$ matrix $A$
satisfies

$$A = \sum_{a, b \in \mathbb{F}_2^k} c_{a, b}(A)\, \sigma_{a, b}, \qquad c_{a, b}(A) = 2^{-k} \operatorname{Tr}(\sigma_{a, b} A).$$

So the $4^k$ Pauli operators span, and hence form a basis of, the space of $2^k \times 2^k$ matrices.

## Sources

- A. Ketkar, A. Klappenecker, S. Kumar and P. K. Sarvepalli, *Nonbinary stabilizer codes over finite fields*, IEEE Trans. Inform. Theory 52 (2006), 4892–4914, arXiv:quant-ph/0508070, Section II (the nice error basis: $\operatorname{Tr}(A^\dagger B) = 0$ for distinct elements, so the error operators form a basis), Lemma 1 and Corollary 4.
- C. Dankert, R. Cleve, J. Emerson and E. Livine, *Exact and approximate unitary 2-designs and their application to fidelity estimation*, Phys. Rev. A 80 (2009), 012304, arXiv:quant-ph/0606161, the expansion $A = \sum_a \alpha_a P_a$ before equation (10).
