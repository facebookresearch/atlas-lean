# Stretch amplification of a one-bit pseudorandom generator

Let $G$ be a pseudorandom generator stretching $n$ bits to $n+1$ bits, and write $G(s) = G'(s) \| \sigma(s)$ with $|G'(s)| = n$ and $\sigma(s)$ a single bit. For a polynomially bounded $\ell$ (that is, $\ell(n) \le p(n)$ for a polynomial $p$), computable from $1^n$ in time polynomial in $n$, with $\ell(n) > n$, define $s_0 = s$, $s_i = G'(s_{i-1})$ and $\sigma_i = \sigma(s_{i-1})$ for $i = 1, \dots, \ell(n)$. Then $G_\ell(s) = \sigma_1 \sigma_2 \cdots \sigma_{\ell(n)}$ is a pseudorandom generator with output length $\ell(n)$.

## Proof sketch

Hybrid $H_i$ outputs $i$ uniform bits followed by the emitted bits of the iteration started from a uniform seed. Adjacent hybrids differ by replacing one application $G(s)$ with a uniform $(n+1)$-bit string, so a distinguisher for $G_\ell$ loses at most a factor $\ell(n)$ against $G$.

## Depends on

- [Asymptotic PRG security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/prgsecure.md)

## Proof depends on

- [Hybrid argument](../../../ComputerScience/cryptography/security-games/games-and-advantages/advantage-le-sum.md)
- [Sequential and parallel composition of pseudorandom generators](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/sequential-and-parallel-composition-of.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- M. Blum and S. Micali, "How to Generate Cryptographically Strong Sequences of Pseudo-Random Bits", SIAM Journal on Computing 13(4), 1984.
