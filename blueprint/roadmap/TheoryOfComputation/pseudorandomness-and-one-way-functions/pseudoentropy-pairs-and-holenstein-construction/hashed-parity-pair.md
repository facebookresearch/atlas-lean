# Hashed parity pair of a function

Let $f$ map $n$-bit inputs to $m(n)$-bit outputs. The *hashed parity pair* of $f$ samples a uniform $x \in \{0,1\}^n$, a hash length $i = s \bmod (n+1) \in \{0, \dots, n\}$ for a uniform integer $s \in \{0, \dots, 2^n - 1\}$ (given by $n$ fair bits), a uniform $n \times n$ Boolean matrix $M$, and a uniform $r \in \{0,1\}^n$, and outputs the observation

$$X = \bigl(f(x),\ i,\ M,\ (Mx)_{1..i},\ r\bigr)$$

together with the hidden bit $B = \langle x, r \rangle \bmod 2$. The sampler uses $n + n + n^2 + n$ fair bits and, for $f$ computable in polynomial time, runs in polynomial time, so the pair is sampled exactly; the hash length is within statistical distance $(n+1)2^{-n}$ of uniform on $\{0, \dots, n\}$, the "almost uniform" choice of Holenstein's footnote 3, which costs only an exponentially small error in his analysis.

## Depends on

- [Samplable pseudoentropy pair with a prediction gap](samplable-pseudoentropy-pair.md)
- [Inner product modulo 2](../goldreich-levin-theorem/xor-dot.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006, Section 4, equations (4)-(5) and footnote 3.
