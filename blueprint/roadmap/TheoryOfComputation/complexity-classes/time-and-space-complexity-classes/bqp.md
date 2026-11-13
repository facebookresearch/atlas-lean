# BQP

The class BQP of bounded-error quantum polynomial-time decision problems consists
of the decision problems $L$ for which there are polynomials $a$ and $q$ with natural number
coefficients and a polynomial-time computable map sending each bitstring $x$ to a list of
2-local quantum gates such that, for every bitstring $x$, with $n = |x|$ and $N = n + a(n)$:
the list has at most $q(n)$ gates; each gate acts on qubits $i < j < N$ and its $4 \times 4$
matrix, whose entries have rational real and imaginary parts, is unitary; and after the gates
are applied in order to the state with $x$ in the computational basis on the $n$ low-order
qubits and $a(n)$ ancilla qubits in state $0$, the probability that qubit $0$ measures $1$ is
at least $2/3$ if $L(x)$ is true and at most $1/3$ if $L(x)$ is false.

## Sources

- S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Definition 10.1; M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press, 2000, Chapter 4; E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411-1473.
