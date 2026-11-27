# A one-way permutation with a hard-core predicate gives a one-bit-stretch generator

Let $f$ be a length-preserving one-way permutation and $b$ a hard-core predicate of $f$. Then $G(s) = f(s) \| b(s)$ is a pseudorandom generator stretching $n$ bits to $n+1$ bits. In particular, applying this to the padded permutation $(x, r) \mapsto (f(x), r)$ with the Goldreich–Levin predicate, every one-way permutation yields a pseudorandom generator with one bit of stretch.

## Proof sketch

Since $f$ is a permutation, $f(s)$ is uniform, so a distinguisher between $G(s)$ and $U_{n+1}$ distinguishes $(f(s), b(s))$ from $(f(s), u)$ with $u$ a fresh uniform bit. Converting such a distinguisher into a predictor of $b(s)$ from $f(s)$ contradicts hard-coreness.

## Depends on

- [Hard-core predicate of a function](hard-core-predicate.md)
- [One-way permutation families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-permutation.md)
- [Asymptotic PRG security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/prgsecure.md)

## Proof depends on

- [Predicting a hidden bit from a distinguishing test](../../../ComputerScience/cryptography/security-games/computational-indistinguishability-of-ensembles/predicting-a-bit-from-a-distinguishing-test.md)
- [Goldreich–Levin for arbitrary one-way functions](goldreich-levin-for-arbitrary-one-way-functions.md)

## Sources

- M. Blum and S. Micali, "How to Generate Cryptographically Strong Sequences of Pseudo-Random Bits", SIAM Journal on Computing 13(4), 1984.
- A. C. Yao, "Theory and Application of Trapdoor Functions", Proceedings of the 23rd Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1982.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
