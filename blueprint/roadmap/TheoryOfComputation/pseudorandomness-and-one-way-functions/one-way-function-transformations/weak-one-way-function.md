# Weak one-way function

A polynomial-time computable function $f : \{0,1\}^* \to \{0,1\}^*$ is *weakly one-way* if there is a polynomial $p$ such that for every probabilistic polynomial-time inverter $A$ receiving $1^n$ and $f(x)$, for all sufficiently large $n$,

$$\Pr_{x \leftarrow \{0,1\}^n}\bigl[A(1^n, f(x)) \in f^{-1}(f(x))\bigr] \le 1 - \frac{1}{p(n)}.$$

Any preimage counts as a success. A (strongly) one-way function is one for which this probability is negligible; every strongly one-way function is weakly one-way.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [Probabilistic polynomial-time Turing machines](../../../ComputerScience/cryptography/security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- A. C. Yao, "Theory and Application of Trapdoor Functions", Proceedings of the 23rd Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1982.
