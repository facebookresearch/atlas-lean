# Tensor product of state vectors

For vectors $\varphi \in \mathbb{C}^{2^a}$ and
$\psi \in \mathbb{C}^{2^b}$, indexed by $\{0, \dots, 2^a - 1\}$ and $\{0, \dots, 2^b - 1\}$, their
tensor product is the vector in $\mathbb{C}^{2^{a+b}}$ whose entry at $s$ is
$\varphi_{s \bmod 2^a}\, \psi_{\lfloor s / 2^a \rfloor}$. Thus $\varphi$ occupies the low-order $a$
bits of the index and $\psi$ the high-order $b$ bits.

## Sources

- M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press, 2000, Chapter 2 (tensor products).
