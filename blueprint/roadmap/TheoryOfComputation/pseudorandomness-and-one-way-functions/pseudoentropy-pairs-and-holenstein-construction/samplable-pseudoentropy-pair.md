# Samplable pseudoentropy pair with a prediction gap

A *samplable pair* is an ensemble of joint distributions $(X_n, B_n)$ of an observation $X_n$ (in a finite set with an injective encoding) and a hidden bit $B_n$, sampled exactly by a probabilistic polynomial-time algorithm. The pair has *pseudoentropy gap* $\gamma(n)$ if for every probabilistic polynomial-time predictor $P$, for all large $n$,

$$\mathbb{E}\bigl[(-1)^{P(1^n, X_n) \oplus B_n}\bigr] \le 1 - H(B_n \mid X_n) - \gamma(n),$$

where $H(B_n \mid X_n)$ is the conditional Shannon entropy. That is, efficient prediction is noticeably worse than the entropy of the bit allows; mere unpredictability is not sufficient. A version *with advice* requires the bound against predictors receiving a polynomially bounded advice string.

## Depends on

- [Conditional entropy of a finite joint law](../../../InformationTheory/entropy-and-mutual-information/conditional-entropy-and-mutual-information/finite-conditional-entropy.md)
- [Probabilistic polynomial-time Turing machines](../../../ComputerScience/cryptography/security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Computational pseudoentropy](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-generators/computational-pseudoentropy.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006.
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-Way Function", SIAM Journal on Computing 28(4), 1999.
