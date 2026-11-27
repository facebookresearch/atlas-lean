# Yao's amplification: weak one-way functions yield strong one-way functions

If $f$ is a weak one-way function with failure parameter $1/p(n)$, then the direct product $F(x_1, \dots, x_t) = (f(x_1), \dots, f(x_t))$ with $t(n) = n\,p(n)$ independent $n$-bit blocks is a (strongly) one-way function: every probabilistic polynomial-time algorithm inverts $F$ on a uniform input with negligible probability.

## Proof sketch

From an inverter $B$ for $F$ with success $\varepsilon$, build $A$ for $f$ that plants its challenge at a random block, samples the other blocks itself, and repeats this polynomially many times. A counting argument on the set of inputs on which a planted run succeeds with noticeable probability shows that $A$ inverts $f$ with probability above $1 - 1/p(n)$ unless $\varepsilon$ is negligible.

## Depends on

- [Weak one-way function](weak-one-way-function.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Error reduction for BPP](../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/error-reduction-for-bpp.md)

## Sources

- A. C. Yao, "Theory and Application of Trapdoor Functions", Proceedings of the 23rd Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1982.
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
