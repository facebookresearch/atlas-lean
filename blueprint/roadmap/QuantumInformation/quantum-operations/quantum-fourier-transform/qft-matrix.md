# Quantum Fourier transform matrix

For a natural number $q$, the quantum Fourier transform is the $q \times q$ complex matrix
$A_q$ with rows and columns indexed by $0, \dots, q - 1$ and entries

$$(A_q)_{a c} = \frac{1}{\sqrt q}\, e^{2 \pi i a c / q}.$$

It maps the basis state $|a\rangle$ to $q^{-1/2} \sum_{c=0}^{q-1} e^{2\pi i a c/q} |c\rangle$.
For $q \ge 1$, up to the normalisation $q^{-1/2}$, it is the discrete Fourier transform on
$\mathbb{Z}/q\mathbb{Z}$; for $q = 0$ it is the empty matrix.

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, SIAM J. Comput. 26 (1997), 1484–1509, arXiv:quant-ph/9508027, Section 4, equation (4.1).
