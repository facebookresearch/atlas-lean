# Hard-core predicate of a function

Let $f : \{0,1\}^* \to \{0,1\}^*$ be polynomial-time computable. A polynomial-time computable predicate $b : \{0,1\}^* \to \{0,1\}$ is *hard-core* for $f$ if for every probabilistic polynomial-time predictor $P$,

$$\Pr_{x \leftarrow \{0,1\}^n}\bigl[P(1^n, f(x)) = b(x)\bigr] - \frac{1}{2}$$

is negligible in $n$. A function with a hard-core predicate need not be one-way (a predicate may be information-theoretically lost), but a hard-core predicate of an injective function makes it one-way.

## Depends on

- [Probabilistic polynomial-time Turing machines](../../../ComputerScience/cryptography/security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible functions](../../complexity-classes/time-and-space-complexity-classes/negligible.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- M. Blum and S. Micali, "How to Generate Cryptographically Strong Sequences of Pseudo-Random Bits", SIAM Journal on Computing 13(4), 1984.
- O. Goldreich and L. A. Levin, "A Hard-Core Predicate for All One-Way Functions", Proceedings of the 21st Annual ACM Symposium on Theory of Computing (STOC), 1989.
