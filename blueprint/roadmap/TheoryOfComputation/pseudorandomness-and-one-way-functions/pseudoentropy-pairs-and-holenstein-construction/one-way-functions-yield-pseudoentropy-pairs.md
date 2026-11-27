# One-way functions yield samplable pairs with an inverse-linear pseudoentropy gap

If $f$ is a one-way function, then its hashed parity pair is an exactly samplable pair with pseudoentropy gap at least $1/(c\,n)$ for a constant $c$: every probabilistic polynomial-time predictor has correlation at most $1 - H(B_n \mid X_n) - 1/(cn)$ for all large $n$. The same holds relative to any fixed polynomially bounded advice family when $f$ is one-way against adversaries with advice.

## Proof sketch

The conditional entropy of the hidden bit is at most $1 - \Omega(1/n)$ because the hash length equals the fiber's log-size with probability $\Omega(1/n)$, in which case $x$ is nearly determined. A predictor whose correlation exceeds $1 - H(B_n \mid X_n) - 1/(cn)$ for infinitely many $n$ would, by the matrix-hash reduction with $\varphi = 1/(cn)$, invert $f$ with probability $\Omega(n^{-3})\,2^{-1/c}$ for those $n$, contradicting one-wayness.

## Depends on

- [Hashed parity pair of a function](hashed-parity-pair.md)
- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Prediction from a leaked matrix hash yields inversion](matrix-hash-prediction-to-inversion.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography (TCC 2006), LNCS 3876, 2006, Section 4 (Lemmas 3 and 4, footnote 3).
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A Pseudorandom Generator from Any One-Way Function", SIAM Journal on Computing 28(4), 1999.
