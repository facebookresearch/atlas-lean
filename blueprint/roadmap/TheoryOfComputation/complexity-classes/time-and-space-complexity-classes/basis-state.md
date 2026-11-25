# Computational basis state of a bitstring

For a bitstring $x = (x_0, \dots, x_{n-1})$,
reading true as $1$ and false as $0$, the computational basis state of $x$ is the vector
$\psi : \{0, \dots, 2^n - 1\} \to \mathbb{C}$ with $\psi(s) = 1$ if $s = \sum_{k < n} x_k 2^k$
(the number whose binary expansion is $x$, least significant bit first) and $\psi(s) = 0$
otherwise.

## Sources

- M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press, 2000, Chapter 1 (computational basis).
