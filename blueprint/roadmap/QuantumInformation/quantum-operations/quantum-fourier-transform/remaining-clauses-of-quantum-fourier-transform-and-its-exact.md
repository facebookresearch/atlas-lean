# Product form and exact circuits for the quantum Fourier transform

The quantum Fourier transform matrix, its unitarity and its identification with the normalized discrete Fourier
transform are separate pages, including the one listed under the dependencies. This node collects only the circuit
clauses they do not state.

## Expansion

A sound expansion has separate pages for:

1. **Product form.** For $N = 2^n$ and $k = k_1 \cdots k_n$ in binary with $k_1$ the most significant bit,
   $A_N \lvert k \rangle = \bigotimes_{\ell=1}^{n} \frac{1}{\sqrt 2}\bigl(\lvert 0 \rangle + e^{2\pi i\, 0.k_{n-\ell+1} \cdots k_n} \lvert 1 \rangle\bigr)$, the
   $\ell$-th factor on the $\ell$-th qubit counted from the most significant one.
2. **Exact circuit.** Hadamard gates and controlled phases $R_k = \mathrm{diag}(1, e^{2\pi i/2^k})$, at most $n^2$ gates in total,
   followed by a reversal of the qubit order, implement the QFT exactly, over a gate set containing these gates.
3. **Gaussian-rational gates.** Among exactly unitary gates with entries in $\mathbb{Q}(i)$, the Hadamard gate is exact up to
   the global phase $e^{i\pi/4}$, as $\tfrac{1+i}{2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$, when it is not controlled, and the
   controlled $R_2$ is exact; the controlled $R_k$ for $k \ge 3$, and $A_{2^n}$ for $n \ge 3$, are not implementable exactly by such
   gates even up to a global phase with clean ancillas, because two nonzero entries of the target have ratio
   $e^{2\pi i/2^k} \notin \mathbb{Q}(i)$ (respectively $e^{2\pi i/8}$), while such a circuit has Gaussian-rational entries.

## Depends on

- [Quantum Fourier transform matrix](qft-matrix.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §4.4–4.5 (the product form $F_N|k\rangle = \bigotimes_{\ell=1}^n \frac{1}{\sqrt 2}(|0\rangle + e^{2\pi i k/2^\ell}|1\rangle)$ and the circuit of at most $n^2$ gates followed by swaps). <https://arxiv.org/pdf/1907.09415v6>
- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, arXiv:quant-ph/9508027v2 (SIAM J. Comput. 26 (1997)), Section 4, equations (4.1)–(4.4) (the transform $A_q$ and its circuit with the output bits in reversed order). <https://arxiv.org/abs/quant-ph/9508027>
