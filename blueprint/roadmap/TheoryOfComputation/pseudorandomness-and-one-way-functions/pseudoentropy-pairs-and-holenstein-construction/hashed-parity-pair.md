# Hashed parity pair of a function

Let $f$ map $n$-bit inputs to $m(n)$-bit outputs. The *hashed parity pair* of $f$ samples a uniform $x \in \{0,1\}^n$, a uniform hash length $i \in \{0, \dots, n\}$, a uniform Boolean matrix $M$, and a uniform $r \in \{0,1\}^n$, and outputs the observation

$$X = \bigl(f(x),\ i,\ M,\ (Mx)_{1..i},\ r\bigr)$$

together with the hidden bit $B = \langle x, r \rangle \bmod 2$.

## Depends on

- [Samplable pseudoentropy pair with a prediction gap](samplable-pseudoentropy-pair.md)
- [Inner product modulo 2](../goldreich-levin-theorem/xor-dot.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
