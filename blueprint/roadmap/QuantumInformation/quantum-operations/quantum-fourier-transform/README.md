# Quantum Fourier transform

The quantum Fourier transform on $q$ basis states is the unitary matrix $A_q$ with entries $q^{-1/2} e^{2\pi i a c/q}$: the discrete Fourier transform, normalised to be unitary, acting on amplitudes. Shor's algorithms apply it to a superposition of periodic values to make the period visible (P. W. Shor, SIAM J. Comput. 26 (1997), Section 4, equation (4.1)). For $q = 2^l$ it is implemented by $l$ one-qubit gates $R_j$ and $l(l-1)/2$ controlled phase gates $S_{j,k}$, with the output bits in reversed order (equation (4.4)).

- [Quantum Fourier transform matrix](qft-matrix.md)
- [The quantum Fourier transform is unitary](qft-matrix-mem-unitary-group.md)
- [The quantum Fourier transform matrix is symmetric](qft-matrix-transpose.md)

## Related topics

- [Shor's order-finding algorithm](../../../ComputerScience/quantum-algorithms/shor-s-order-finding-algorithm/README.md): the algorithm that applies $A_q$ with $n^2 \le q < 2n^2$ and post-processes the observed output with continued fractions.
- [Fast Fourier transform](../../../ComputerScience/algebraic-and-numerical-algorithms/fast-fourier-transform/README.md): the classical algorithm for the unnormalised discrete Fourier transform.
