# The quantum Fourier transform is unitary

For every natural number $q$, the quantum Fourier transform matrix $A_q$, with entries
$q^{-1/2} e^{2\pi i a c/q}$, is unitary: $A_q A_q^{*} = I$.

This is what makes Shor's transformation (4.1) a legitimate quantum operation. The proof is the
orthogonality of the characters $c \mapsto e^{2 \pi i a c / q}$: the $(a, b)$ entry of
$A_q A_q^{*}$ is $q^{-1} \sum_{c=0}^{q-1} w^c$ with $w = e^{2\pi i (a - b)/q}$, which is $1$ when
$a = b$, and $0$ otherwise because then $w \ne 1$ and $w^q = 1$.

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, SIAM J. Comput. 26 (1997), 1484–1509, arXiv:quant-ph/9508027, Section 4, equation (4.1).
